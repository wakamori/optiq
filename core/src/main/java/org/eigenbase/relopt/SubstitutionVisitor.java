/*
// Licensed to Julian Hyde under one or more contributor license
// agreements. See the NOTICE file distributed with this work for
// additional information regarding copyright ownership.
//
// Julian Hyde licenses this file to you under the Apache License,
// Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at:
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
*/
package org.eigenbase.relopt;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.eigenbase.rel.*;
import org.eigenbase.rel.rules.RemoveTrivialProjectRule;
import org.eigenbase.reltype.*;
import org.eigenbase.rex.*;
import org.eigenbase.sql.SqlKind;
import org.eigenbase.sql.fun.SqlStdOperatorTable;
import org.eigenbase.sql.validate.SqlValidatorUtil;
import org.eigenbase.trace.EigenbaseTrace;
import org.eigenbase.util.*;
import org.eigenbase.util.mapping.Mapping;
import org.eigenbase.util.mapping.Mappings;

import net.hydromatic.linq4j.Ord;

import net.hydromatic.optiq.prepare.OptiqPrepareImpl;
import net.hydromatic.optiq.runtime.Spaces;
import net.hydromatic.optiq.util.BitSets;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Function;
import com.google.common.collect.*;

/**
 * Substitutes part of a tree of relational expressions with another tree.
 *
 * <p>The call {@code new SubstitutionVisitor(target, query).go(replacement))}
 * will return {@code query} with every occurrence of {@code target} replaced
 * by {@code replacement}.</p>
 *
 * <p>The following example shows how {@code SubstitutionVisitor} can be used
 * for materialized view recognition.</p>
 *
 * <ul>
 * <li>query = SELECT a, c FROM t WHERE x = 5 AND b = 4</li>
 * <li>target = SELECT a, b, c FROM t WHERE x = 5</li>
 * <li>replacement = SELECT * FROM mv</li>
 * <li>result = SELECT a, c FROM mv WHERE b = 4</li>
 * </ul>
 *
 * <p>Note that {@code result} uses the materialized view table {@code mv} and a
 * simplified condition {@code b = 4}.</p>
 *
 * <p>Uses a bottom-up matching algorithm. Nodes do not need to be identical.
 * At each level, returns the residue.</p>
 *
 * <p>The inputs must only include the core relational operators:
 * {@link TableAccessRel},
 * {@link FilterRel},
 * {@link ProjectRel},
 * {@link JoinRel},
 * {@link UnionRel},
 * {@link AggregateRel}.</p>
 */
public class SubstitutionVisitor {
  private static final boolean DEBUG = OptiqPrepareImpl.DEBUG;

  private static final Logger LOGGER = EigenbaseTrace.getPlannerTracer();

  private static final List<UnifyRule> RULES =
      ImmutableList.<UnifyRule>of(
          TrivialRule.INSTANCE,
          ProjectToProjectUnifyRule.INSTANCE,
          FilterToProjectUnifyRule.INSTANCE,
//          ProjectToFilterUnifyRule.INSTANCE,
          FilterToFilterUnifyRule.INSTANCE,
          AggregateToAggregateUnifyRule.INSTANCE,
          AggregateOnProjectToAggregateUnifyRule.INSTANCE);

  private static final Map<Pair<Class, Class>, List<UnifyRule>> RULE_MAP =
      new HashMap<Pair<Class, Class>, List<UnifyRule>>();

  private final RelOptCluster cluster;
  private final MutableRel query;
  private final MutableRel target;

  /**
   * Nodes in {@link #target} that have no children.
   */
  final List<MutableRel> targetLeaves;

  /**
   * Nodes in {@link #query} that have no children.
   */
  final List<MutableRel> queryLeaves;

  final Map<MutableRel, MutableRel> replacementMap =
      new HashMap<MutableRel, MutableRel>();

  public SubstitutionVisitor(RelNode target_, RelNode query_) {
    this.cluster = target_.getCluster();
    this.query = toMutable(query_);
    this.target = toMutable(target_);
    final Set<MutableRel> parents = Sets.newIdentityHashSet();
    final List<MutableRel> allNodes = new ArrayList<MutableRel>();
    final MutableRelVisitor visitor =
        new MutableRelVisitor() {
          public void visit(MutableRel node) {
            parents.add(node.parent);
            allNodes.add(node);
            super.visit(node);
          }
        };
    visitor.go(target);

    // Populate the list of leaves in the tree under "target".
    // Leaves are all nodes that are not parents.
    // For determinism, it is important that the list is in scan order.
    allNodes.removeAll(parents);
    targetLeaves = ImmutableList.copyOf(allNodes);

    allNodes.clear();
    parents.clear();
    visitor.go(query);
    allNodes.removeAll(parents);
    queryLeaves = ImmutableList.copyOf(allNodes);
  }

  private MutableRel toMutable(RelNode rel) {
    if (rel instanceof TableAccessRelBase) {
      return MutableScan.of((TableAccessRelBase) rel);
    }
    if (rel instanceof ValuesRelBase) {
      return MutableValues.of((ValuesRelBase) rel);
    }
    if (rel instanceof ProjectRelBase) {
      final ProjectRelBase project = (ProjectRelBase) rel;
      final MutableRel input = toMutable(project.getChild());
      return MutableProject.of(input, project.getProjects(),
          project.getRowType().getFieldNames());
    }
    if (rel instanceof FilterRelBase) {
      final FilterRelBase filter = (FilterRelBase) rel;
      final MutableRel input = toMutable(filter.getChild());
      return MutableFilter.of(input, filter.getCondition());
    }
    if (rel instanceof AggregateRelBase) {
      final AggregateRelBase aggregate = (AggregateRelBase) rel;
      final MutableRel input = toMutable(aggregate.getChild());
      return MutableAggregate.of(input, aggregate.getGroupSet(),
          aggregate.getAggCallList());
    }
    throw new RuntimeException("cannot translate " + rel + " to MutableRel");
  }

  void register(MutableRel result, MutableRel query) {
  }

  /**
   * Maps a condition onto a target.
   *
   * <p>If condition is stronger than target, returns the residue.
   * If it is equal to target, returns the expression that evaluates to
   * the constant {@code true}. If it is weaker than target, returns
   * {@code null}.</p>
   *
   * <p>The terms satisfy the relation</p>
   *
   * <pre>
   *     {@code condition = target AND residue}
   * </pre>
   *
   * <p>and {@code residue} must be as weak as possible.</p>
   *
   * <p>Example #1: condition stronger than target</p>
   * <ul>
   * <li>condition: x = 1 AND y = 2</li>
   * <li>target: x = 1</li>
   * <li>residue: y = 2</li>
   * </ul>
   *
   * <p>Note that residue {@code x &gt; 0 AND y = 2} would also satisfy the
   * relation {@code condition = target AND residue} but is stronger than
   * necessary, so we prefer {@code y = 2}.</p>
   *
   * <p>Example #2: target weaker than condition (valid, but not currently
   * implemented)</p>
   * <ul>
   * <li>condition: x = 1</li>
   * <li>target: x = 1 OR z = 3</li>
   * <li>residue: NOT (z = 3)</li>
   * </ul>
   *
   * <p>Example #3: condition and target are equivalent</p>
   * <ul>
   * <li>condition: x = 1 AND y = 2</li>
   * <li>target: y = 2 AND x = 1</li>
   * <li>residue: TRUE</li>
   * </ul>
   *
   * <p>Example #4: condition weaker than target</p>
   * <ul>
   * <li>condition: x = 1</li>
   * <li>target: x = 1 AND y = 2</li>
   * <li>residue: null (i.e. no match)</li>
   * </ul>
   *
   * <p>There are many other possible examples. It amounts to solving
   * whether {@code condition AND NOT target} can ever evaluate to
   * true, and therefore is a form of the NP-complete
   * <a href="http://en.wikipedia.org/wiki/Satisfiability">Satisfiability</a>
   * problem.</p>
   */
  @VisibleForTesting
  public static RexNode splitFilter(
      final RexBuilder rexBuilder, RexNode condition, RexNode target) {
    // First, try splitting into ORs.
    // Given target    c1 OR c2 OR c3 OR c4
    // and condition   c2 OR c4
    // residue is      NOT c1 AND NOT c3
    // Also deals with case target [x] condition [x] yields residue [true].
    RexNode z = splitOr(rexBuilder, condition, target);
    if (z != null) {
      return z;
    }

    RexNode x = andNot(rexBuilder, target, condition);
    if (mayBeSatisfiable(x)) {
      RexNode x2 = andNot(rexBuilder, condition, target);
      return simplify(rexBuilder, x2);
    }
    return null;
  }

  private static RexNode splitOr(
      final RexBuilder rexBuilder, RexNode condition, RexNode target) {
    List<RexNode> targets = RelOptUtil.disjunctions(target);
    for (RexNode e : RelOptUtil.disjunctions(condition)) {
      boolean found = removeAll(targets, e);
      if (!found) {
        return null;
      }
    }
    return RexUtil.composeConjunction(rexBuilder,
        Lists.transform(targets, not(rexBuilder)), false);
  }

  /** Returns a function that applies NOT to its argument. */
  public static Function<RexNode, RexNode> not(final RexBuilder rexBuilder) {
    return new Function<RexNode, RexNode>() {
      public RexNode apply(RexNode input) {
        return input.isAlwaysTrue()
            ? rexBuilder.makeLiteral(false)
            : input.isAlwaysFalse()
            ? rexBuilder.makeLiteral(true)
            : input.getKind() == SqlKind.NOT
            ? ((RexCall) input).operands.get(0)
            : rexBuilder.makeCall(SqlStdOperatorTable.NOT, input);
      }
    };
  }

  /** Removes all expressions from a list that are equivalent to a given
   * expression. Returns whether any were removed. */
  private static boolean removeAll(List<RexNode> targets, RexNode e) {
    int count = 0;
    Iterator<RexNode> iterator = targets.iterator();
    while (iterator.hasNext()) {
      RexNode next = iterator.next();
      if (equivalent(next, e)) {
        ++count;
        iterator.remove();
      }
    }
    return count > 0;
  }

  /** Returns whether two expressions are equivalent. */
  private static boolean equivalent(RexNode e1, RexNode e2) {
    // TODO: make broader;
    // 1. 'x = y' should be equivalent to 'y = x'.
    // 2. 'c2 and c1' should be equivalent to 'c1 and c2'.
    return e1 == e2 || e1.toString().equals(e2.toString());
  }

  /**
   * Returns whether a boolean expression ever returns true.
   *
   * <p>This method may give false positives. For instance, it will say
   * that {@code x = 5 AND x > 10} is satisfiable, because at present it
   * cannot prove that it is not.</p>
   */
  public static boolean mayBeSatisfiable(RexNode e) {
    // Example:
    //  e: x = 1 AND y = 2 AND z = 3 AND NOT (x = 1 AND y = 2)
    //  disjunctions: {x = 1, y = 2, z = 3}
    //  notDisjunctions: {x = 1 AND y = 2}
    final List<RexNode> disjunctions = new ArrayList<RexNode>();
    final List<RexNode> notDisjunctions = new ArrayList<RexNode>();
    RelOptUtil.decomposeConjunction(e, disjunctions, notDisjunctions);

    // If there is a single FALSE or NOT TRUE, the whole expression is
    // always false.
    for (RexNode disjunction : disjunctions) {
      switch (disjunction.getKind()) {
      case LITERAL:
        if (!RexLiteral.booleanValue(disjunction)) {
          return false;
        }
      }
    }
    for (RexNode disjunction : notDisjunctions) {
      switch (disjunction.getKind()) {
      case LITERAL:
        if (RexLiteral.booleanValue(disjunction)) {
          return false;
        }
      }
    }
    // If one of the not-disjunctions is a disjunction that is wholly
    // contained in the disjunctions list, the expression is not
    // satisfiable.
    //
    // Example #1. x AND y AND z AND NOT (x AND y)  - not satisfiable
    // Example #2. x AND y AND NOT (x AND y)        - not satisfiable
    // Example #3. x AND y AND NOT (x AND y AND z)  - may be satisfiable
    for (RexNode notDisjunction : notDisjunctions) {
      final List<RexNode> disjunctions2 =
          RelOptUtil.conjunctions(notDisjunction);
      if (disjunctions.containsAll(disjunctions2)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Simplifies a boolean expression.
   *
   * <p>In particular:</p>
   * <ul>
   * <li>{@code simplify(x = 1 AND y = 2 AND NOT x = 1)}
   * returns {@code y = 2}</li>
   * <li>{@code simplify(x = 1 AND FALSE)}
   * returns {@code FALSE}</li>
   * </ul>
   */
  public static RexNode simplify(RexBuilder rexBuilder, RexNode e) {
    final List<RexNode> disjunctions = RelOptUtil.conjunctions(e);
    final List<RexNode> notDisjunctions = new ArrayList<RexNode>();
    for (int i = 0; i < disjunctions.size(); i++) {
      final RexNode disjunction = disjunctions.get(i);
      final SqlKind kind = disjunction.getKind();
      switch (kind) {
      case NOT:
        notDisjunctions.add(
            ((RexCall) disjunction).getOperands().get(0));
        disjunctions.remove(i);
        --i;
        break;
      case LITERAL:
        if (!RexLiteral.booleanValue(disjunction)) {
          return disjunction; // false
        } else {
          disjunctions.remove(i);
          --i;
        }
      }
    }
    if (disjunctions.isEmpty() && notDisjunctions.isEmpty()) {
      return rexBuilder.makeLiteral(true);
    }
    // If one of the not-disjunctions is a disjunction that is wholly
    // contained in the disjunctions list, the expression is not
    // satisfiable.
    //
    // Example #1. x AND y AND z AND NOT (x AND y)  - not satisfiable
    // Example #2. x AND y AND NOT (x AND y)        - not satisfiable
    // Example #3. x AND y AND NOT (x AND y AND z)  - may be satisfiable
    for (RexNode notDisjunction : notDisjunctions) {
      final List<RexNode> disjunctions2 =
          RelOptUtil.conjunctions(notDisjunction);
      if (disjunctions.containsAll(disjunctions2)) {
        return rexBuilder.makeLiteral(false);
      }
    }
    // Add the NOT disjunctions back in.
    for (RexNode notDisjunction : notDisjunctions) {
      disjunctions.add(
          rexBuilder.makeCall(
              SqlStdOperatorTable.NOT,
              notDisjunction));
    }
    return RexUtil.composeConjunction(rexBuilder, disjunctions, false);
  }

  /**
   * Creates the expression {@code e1 AND NOT e2}.
   */
  static RexNode andNot(RexBuilder rexBuilder, RexNode e1, RexNode e2) {
    return rexBuilder.makeCall(
        SqlStdOperatorTable.AND,
        e1,
        rexBuilder.makeCall(
            SqlStdOperatorTable.NOT,
            e2));
  }

  public RelNode go(RelNode replacement_) {
    MutableRel replacement = toMutable(replacement_);
    assert MutableRels.equalType(
        "target", target, "replacement", replacement, true);
    replacementMap.put(target, replacement);
    final UnifyResult unifyResult = matchRecurse(target);
    if (unifyResult == null) {
      return null;
    }
    final MutableRel node0 = unifyResult.result;
    MutableRel node = node0; // replaceAncestors(node0);
    if (DEBUG) {
      System.out.println(
          "Convert: query:\n"
              + query.deep()
              + "\nunify.query:\n"
              + unifyResult.call.query.deep()
              + "\nunify.result:\n"
              + unifyResult.result.deep()
              + "\nunify.target:\n"
              + unifyResult.call.target.deep()
              + "\nnode0:\n"
              + node0.deep()
              + "\nnode:\n"
              + node.deep());
    }
    return fromMutable(node);
  }

  private static RelNode fromMutable(MutableRel node) {
    switch (node.type) {
    case PROJECT:
      MutableProject project = (MutableProject) node;
      return new ProjectRel(node.cluster,
          node.cluster.traitSetOf(RelCollationImpl.EMPTY),
          fromMutable(project.input),
          project.projects, project.rowType, ProjectRelBase.Flags.NONE);
    default:
      throw new AssertionError(node);
    }
  }

  private UnifyResult matchRecurse(MutableRel target) {
    final List<MutableRel> targetInputs = target.getInputs();
    MutableRel queryParent = null;

    for (MutableRel targetInput : targetInputs) {
      UnifyResult unifyResult = matchRecurse(targetInput);
      if (unifyResult == null) {
        return null;
      }
      queryParent = unifyResult.call.query.replaceInParent(unifyResult.result);
    }

    if (targetInputs.isEmpty()) {
      for (MutableRel queryLeaf : queryLeaves) {
        for (UnifyRule rule : applicableRules(queryLeaf, target)) {
          final UnifyResult x = apply(rule, queryLeaf, target);
          if (x != null) {
            if (DEBUG) {
              System.out.println(
                  "Rule: " + rule
                  + "\nQuery:\n"
                  + queryParent
                  + (x.call.query != queryParent
                     ? "\nQuery (original):\n"
                     + queryParent
                     : "")
                  + "\nTarget:\n"
                  + target.deep()
                  + "\nResult:\n"
                  + x.result.deep()
                  + "\n");
            }
            return x;
          }
        }
      }
    } else {
      assert queryParent != null;
      for (UnifyRule rule : applicableRules(queryParent, target)) {
        final UnifyResult x = apply(rule, queryParent, target);
        if (x != null) {
          if (DEBUG) {
            System.out.println(
                "Rule: " + rule
                + "\nQuery:\n"
                + queryParent.deep()
                + (x.call.query != queryParent
                   ? "\nQuery (original):\n"
                   + queryParent.toString()
                   : "")
                + "\nTarget:\n"
                + target.deep()
                + "\nResult:\n"
                + x.result.deep()
                + "\n");
          }
          return x;
        }
      }
    }
    if (DEBUG) {
      System.out.println(
          "Unify failed:"
          + "\nQuery:\n"
          + queryParent.toString()
          + "\nTarget:\n"
          + target.toString()
          + "\n");
    }
    return null;
  }

  private UnifyResult apply(UnifyRule rule, MutableRel query,
      MutableRel target) {
    final UnifyRuleCall call = new UnifyRuleCall(rule, query, target);
    return rule.apply(call);
  }

  private static List<UnifyRule> applicableRules(MutableRel query,
      MutableRel target) {
    final Class queryClass = query.getClass();
    final Class targetClass = target.getClass();
    final Pair<Class, Class> key = Pair.of(queryClass, targetClass);
    List<UnifyRule> list = RULE_MAP.get(key);
    if (list == null) {
      final ImmutableList.Builder<UnifyRule> builder =
          ImmutableList.builder();
      for (UnifyRule rule : RULES) {
        //noinspection unchecked
        if (rule.mightMatch(queryClass, targetClass)) {
          builder.add(rule);
        }
      }
      list = builder.build();
      RULE_MAP.put(key, list);
    }
    return list;
  }

  /** Exception thrown to exit a matcher. Not really an error. */
  private static class MatchFailed extends ControlFlowException {
    static final MatchFailed INSTANCE = new MatchFailed();
  }

  /** Rule that attempts to match a query relational expression
   * against a target relational expression.
   *
   * <p>The rule declares the query and target types; this allows the
   * engine to fire only a few rules in a given context.</p>
   */
  private interface UnifyRule {
    /**
     * <p>Applies this rule to a particular node in a query. The goal is
     * to convert {@code query} into {@code target}. Before the rule is
     * invoked, Optiq has made sure that query's children are equivalent
     * to target's children.
     *
     * <p>There are 3 possible outcomes:</p>
     *
     * <ul>
     *
     * <li>{@code query} already exactly matches {@code target}; returns
     * {@code target}</li>
     *
     * <li>{@code query} is sufficiently close to a match for
     * {@code target}; returns {@code target}</li>
     *
     * <li>{@code query} cannot be made to match {@code target}; returns
     * null</li>
     *
     * </ul>
     *
     * <p>REVIEW: Is possible that we match query PLUS one or more of its
     * ancestors?</p>
     *
     * @param call Input parameters
     */
    UnifyResult apply(UnifyRuleCall call);

    boolean mightMatch(Class queryClass, Class targetClass);
  }

  /**
   * Arguments to an application of a {@link UnifyRule}.
   */
  private class UnifyRuleCall {
    final UnifyRule rule;
    final MutableRel query;
    final MutableRel target;

    public UnifyRuleCall(UnifyRule rule, MutableRel query, MutableRel target) {
      this.rule = rule;
      this.query = query;
      this.target = target;
    }

    UnifyResult result(MutableRel result) {
      assert MutableRels.contains(result, target);
      assert MutableRels.equalType("result", result, "query", query, true);
      // TODO: equiv(result, query);
      MutableRel replace = replacementMap.get(target);
      if (replace != null) {
        result = MutableRels.replace(result, target, replace);
      }
      register(result, query);
      return new UnifyResult(this, result);
    }

    /**
     * Creates a {@link UnifyRuleCall} based on the parent of {@code query}.
     */
    public UnifyRuleCall create(MutableRel query) {
      return new UnifyRuleCall(rule, query, target);
    }

    public RelOptCluster getCluster() {
      return cluster;
    }
  }

  /**
   * Result of an application of a {@link UnifyRule} indicating that the
   * rule successfully matched {@code query} against {@code target} and
   * generated a {@code result} that is equivalent to {@code query} and
   * contains {@code target}.
   */
  private static class UnifyResult {
    private final UnifyRuleCall call;
    // equivalent to "query", contains "result"
    private final MutableRel result;

    UnifyResult(UnifyRuleCall call, MutableRel result) {
      this.call = call;
      assert MutableRels.equalType(
          "query", call.query, "result", result, true);
      this.result = result;
    }
  }

  /** Abstract base class for implementing {@link UnifyRule}. */
  private abstract static class AbstractUnifyRule implements UnifyRule {
    private final Class<? extends MutableRel> queryClass;
    private final Class<? extends MutableRel> targetClass;

    public AbstractUnifyRule(Class<? extends MutableRel> queryClass,
        Class<? extends MutableRel> targetClass) {
      this.queryClass = queryClass;
      this.targetClass = targetClass;
    }

    public boolean mightMatch(Class queryClass, Class targetClass) {
      return this.queryClass.isAssignableFrom(queryClass)
          && this.targetClass.isAssignableFrom(targetClass);
    }
  }

  /** Implementation of {@link UnifyRule} that matches if the query is already
   * equal to the target (using {@code ==}).
   *
   * <p>Matches scans to the same table, because these will be canonized to
   * the same {@link org.eigenbase.rel.TableAccessRel} instance.</p>
   */
  private static class TrivialRule extends AbstractUnifyRule {
    private static final TrivialRule INSTANCE = new TrivialRule();

    private TrivialRule() {
      super(MutableRel.class, MutableRel.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      if (call.query.equals(call.target)) {
        return call.result(call.query);
      }
      return null;
    }
  }

  /** Implementation of {@link UnifyRule} that matches {@link ProjectRel}. */
  private static class ProjectToProjectUnifyRule extends AbstractUnifyRule {
    public static final ProjectToProjectUnifyRule INSTANCE =
        new ProjectToProjectUnifyRule();

    private ProjectToProjectUnifyRule() {
      super(MutableProject.class, MutableProject.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      final MutableProject target = (MutableProject) call.target;
      final MutableProject query = (MutableProject) call.query;
      final RexShuttle shuttle = getRexShuttle(target);
      final List<RexNode> newProjects;
      try {
        newProjects = shuttle.apply(query.getProjects());
      } catch (MatchFailed e) {
        return null;
      }
      final MutableProject newProject =
          MutableProject.of(
              query.getRowType(), target, newProjects);
      final MutableRel newProject2 = MutableRels.strip(newProject);
      return call.result(newProject2);
    }
  }

  /** Implementation of {@link UnifyRule} that matches a {@link MutableFilter}
   * to a {@link MutableProject}. */
  private static class FilterToProjectUnifyRule extends AbstractUnifyRule {
    public static final FilterToProjectUnifyRule INSTANCE =
        new FilterToProjectUnifyRule();

    private FilterToProjectUnifyRule() {
      super(MutableFilter.class, MutableProject.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      // Child of projectTarget is equivalent to child of filterQuery.
      try {
        // TODO: make sure that constants are ok
        final MutableProject target = (MutableProject) call.target;
        final RexShuttle shuttle = getRexShuttle(target);
        final RexNode newCondition;
        final MutableFilter query = (MutableFilter) call.query;
        try {
          newCondition = query.getCondition().accept(shuttle);
        } catch (MatchFailed e) {
          return null;
        }
        final MutableFilter newFilter = MutableFilter.of(target, newCondition);
        final MutableRel inverse =
            invert(query, newFilter, target);
        return call.result(inverse);
      } catch (MatchFailed e) {
        return null;
      }
    }

    private MutableRel invert(MutableRel model, MutableRel input,
        MutableProject project) {
      if (LOGGER.isLoggable(Level.FINER)) {
        LOGGER.finer("SubstitutionVisitor: invert:\n"
            + "model: " + model + "\n"
            + "input: " + input + "\n"
            + "project: " + project + "\n");
      }
      final List<RexNode> exprList = new ArrayList<RexNode>();
      final RexBuilder rexBuilder = model.cluster.getRexBuilder();
      for (RelDataTypeField field : model.getRowType().getFieldList()) {
        exprList.add(rexBuilder.makeZeroLiteral(field.getType()));
      }
      for (Ord<RexNode> expr : Ord.zip(project.getProjects())) {
        if (expr.e instanceof RexInputRef) {
          final int target = ((RexInputRef) expr.e).getIndex();
          exprList.set(expr.i,
              rexBuilder.makeInputRef(input.rowType, target));
        }
      }
      return MutableProject.of(model.rowType, input, exprList);
    }
  }

  /** Implementation of {@link UnifyRule} that matches a {@link MutableFilter}. */
  private static class FilterToFilterUnifyRule extends AbstractUnifyRule {
    public static final FilterToFilterUnifyRule INSTANCE =
        new FilterToFilterUnifyRule();

    private FilterToFilterUnifyRule() {
      super(MutableFilter.class, MutableFilter.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      // in.query can be rewritten in terms of in.target if its condition
      // is weaker. For example:
      //   query: SELECT * FROM t WHERE x = 1 AND y = 2
      //   target: SELECT * FROM t WHERE x = 1
      // transforms to
      //   result: SELECT * FROM (target) WHERE y = 2
      final MutableFilter query = (MutableFilter) call.query;
      final MutableFilter target = (MutableFilter) call.target;
      final MutableFilter newFilter =
          createFilter(query, target);
      if (newFilter == null) {
        return null;
      }
      return call.result(newFilter);
    }

    MutableFilter createFilter(MutableFilter query, MutableFilter target) {
      final RexNode newCondition =
          splitFilter(query.cluster.getRexBuilder(), query.getCondition(),
              target.getCondition());
      if (newCondition == null) {
        // Could not map query onto target.
        return null;
      }
      if (newCondition.isAlwaysTrue()) {
        return target;
      }
      return MutableFilter.of(target, newCondition);
    }
  }

  /** Implementation of {@link UnifyRule} that matches a {@link MutableProject}
   * to a {@link MutableFilter}. */
  private static class ProjectToFilterUnifyRule extends AbstractUnifyRule {
    public static final ProjectToFilterUnifyRule INSTANCE =
        new ProjectToFilterUnifyRule();

    private ProjectToFilterUnifyRule() {
      super(MutableProject.class, MutableFilter.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      if (call.query.parent instanceof MutableFilter) {
        final UnifyRuleCall in2 = call.create(call.query.parent);
        final MutableFilter query = (MutableFilter) in2.query;
        final MutableFilter target = (MutableFilter) in2.target;
        final MutableFilter newFilter =
            FilterToFilterUnifyRule.INSTANCE.createFilter(
                query, target);
        if (newFilter == null) {
          return null;
        }
        return in2.result(query.replaceInParent(newFilter));
      }
      return null;
    }
  }

  /** Implementation of {@link UnifyRule} that matches a {@link AggregateRel} to
   * a {@link AggregateRel}, provided that they have the same child. */
  private static class AggregateToAggregateUnifyRule extends AbstractUnifyRule {
    public static final AggregateToAggregateUnifyRule INSTANCE =
        new AggregateToAggregateUnifyRule();

    private AggregateToAggregateUnifyRule() {
      super(MutableAggregate.class, MutableAggregate.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      final MutableAggregate query = (MutableAggregate) call.query;
      final MutableAggregate target = (MutableAggregate) call.target;
      assert query != target;
      if (query.getChild() != target.getChild()) {
        return null;
      }
      // in.query can be rewritten in terms of in.target if its groupSet is
      // a subset, and its aggCalls are a superset. For example:
      //   query: SELECT x, COUNT(b) FROM t GROUP BY x
      //   target: SELECT x, y, SUM(a) AS s, COUNT(b) AS cb FROM t GROUP BY x, y
      // transforms to
      //   result: SELECT x, SUM(cb) FROM (target) GROUP BY x
      if (!BitSets.contains(target.getGroupSet(), query.getGroupSet())) {
        return null;
      }
      MutableRel result = unifyAggregates(query, target);
      if (result == null) {
        return null;
      }
      return call.result(result);
    }
  }

  public static MutableAggregate permute(MutableAggregate aggregate,
      MutableRel input, Mapping mapping) {
    BitSet groupSet = Mappings.apply(mapping, aggregate.getGroupSet());
    List<AggregateCall> aggregateCalls =
        apply(mapping, aggregate.getAggCallList());
    return MutableAggregate.of(input, groupSet, aggregateCalls);
  }

  private static List<AggregateCall> apply(final Mapping mapping,
      List<AggregateCall> aggCallList) {
    return Lists.transform(aggCallList,
        new Function<AggregateCall, AggregateCall>() {
          public AggregateCall apply(AggregateCall call) {
            return new AggregateCall(call.getAggregation(), call.isDistinct(),
                Mappings.apply2(mapping, call.getArgList()), call.getType(),
                call.name);
          }
        });
  }

  public static MutableRel unifyAggregates(MutableAggregate query,
      MutableAggregate target) {
    MutableRel result;
    if (query.getGroupSet().equals(target.getGroupSet())) {
      // Same level of aggregation. Generate a project.
      final List<Integer> projects = Lists.newArrayList();
      final int groupCount = query.getGroupSet().cardinality();
      for (int i = 0; i < groupCount; i++) {
        projects.add(i);
      }
      for (AggregateCall aggregateCall : query.getAggCallList()) {
        int i = target.getAggCallList().indexOf(aggregateCall);
        if (i < 0) {
          return null;
        }
        projects.add(groupCount + i);
      }
      result = MutableRels.createProject(target, projects);
    } else {
      // Target is coarser level of aggregation. Generate an aggregate.
      final BitSet groupSet = new BitSet();
      final IntList targetGroupList = BitSets.toList(target.getGroupSet());
      for (int c : BitSets.toIter(query.getGroupSet())) {
        int c2 = targetGroupList.indexOf(c);
        if (c2 < 0) {
          return null;
        }
        groupSet.set(c2);
      }
      final List<AggregateCall> aggregateCalls = Lists.newArrayList();
      for (AggregateCall aggregateCall : query.getAggCallList()) {
        if (aggregateCall.isDistinct()) {
          return null;
        }
        int i = target.getAggCallList().indexOf(aggregateCall);
        if (i < 0) {
          return null;
        }
        aggregateCalls.add(
            new AggregateCall(
                getRollup(aggregateCall.getAggregation()),
                aggregateCall.isDistinct(),
                ImmutableList.of(groupSet.cardinality() + i),
                aggregateCall.type, aggregateCall.name));
      }
      result = MutableAggregate.of(target, groupSet, aggregateCalls);
    }
    return MutableRels.createCastRel(result, query.getRowType(), true);
  }

  /** Implementation of {@link UnifyRule} that matches a {@link AggregateRel} on
   * a {@link ProjectRel} to an {@link AggregateRel} target. */
  private static class AggregateOnProjectToAggregateUnifyRule
      extends AbstractUnifyRule {
    public static final AggregateOnProjectToAggregateUnifyRule INSTANCE =
        new AggregateOnProjectToAggregateUnifyRule();

    private AggregateOnProjectToAggregateUnifyRule() {
      super(MutableAggregate.class, MutableAggregate.class);
    }

    public UnifyResult apply(UnifyRuleCall call) {
      final MutableAggregate query = (MutableAggregate) call.query;
      final MutableAggregate target = (MutableAggregate) call.target;
      if (!(query.getChild() instanceof MutableProject)) {
        return null;
      }
      final MutableProject project = (MutableProject) query.getChild();
      if (project.getChild() != target.getChild()) {
        return null;
      }
      final Mappings.TargetMapping mapping = project.getMapping();
      if (mapping == null) {
        return null;
      }
      final MutableAggregate aggregate2 =
          permute(query, project.getChild(), mapping.inverse());
      final MutableRel result = unifyAggregates(aggregate2, target);
      return result == null ? null : call.result(result);
    }
  }

  public static Aggregation getRollup(Aggregation aggregation) {
    // TODO: count rolls up using sum; etc.
    return aggregation;
  }

  private static RexShuttle getRexShuttle(MutableProject target) {
    final Map<String, Integer> map = new HashMap<String, Integer>();
    for (RexNode e : target.getProjects()) {
      map.put(e.toString(), map.size());
    }
    return new RexShuttle() {
      @Override public RexNode visitInputRef(RexInputRef ref) {
        final Integer integer = map.get(ref.getName());
        if (integer != null) {
          return new RexInputRef(integer, ref.getType());
        }
        throw MatchFailed.INSTANCE;
      }

      @Override public RexNode visitCall(RexCall call) {
        final Integer integer = map.get(call.toString());
        if (integer != null) {
          return new RexInputRef(integer, call.getType());
        }
        return super.visitCall(call);
      }
    };
  }

  /** Type of {@code MutableRel}. */
  private enum MutableRelType {
    SCAN,
    PROJECT,
    FILTER,
    AGGREGATE,
    SORT,
    UNION,
    JOIN,
    VALUES
  }

  /** Visitor over {@link MutableRel}. */
  private static class MutableRelVisitor {
    private MutableRel root;

    public void visit(MutableRel node) {
      node.childrenAccept(this);
    }

    public MutableRel go(MutableRel p) {
      this.root = p;
      visit(p);
      return root;
    }
  }

  /** Mutable equivalent of {@link RelNode}.
   *
   * <p>Each node has mutable state, and keeps track of its parent and position
   * within parent.
   * It doesn't make sense to canonize {@code MutableRels},
   * otherwise one node could end up with multiple parents.
   * It follows that {@code #hashCode} and {@code #equals} are less efficient
   * than their {@code RelNode} counterparts.
   * But, you don't need to copy a {@code MutableRel} in order to change it.
   * For this reason, you should use {@code MutableRel} for short-lived
   * operations, and transcribe back to {@code RelNode} when you are done.</p>
   */
  private abstract static class MutableRel {
    MutableRel parent;
    int ordinalInParent;
    public final RelOptCluster cluster;
    final RelDataType rowType;
    final MutableRelType type;

    private MutableRel(RelOptCluster cluster, RelDataType rowType,
        MutableRelType type) {
      this.cluster = cluster;
      this.rowType = rowType;
      this.type = type;
    }

    public RelDataType getRowType() {
      return rowType;
    }

    public abstract void setInput(int ordinalInParent, MutableRel input);

    public abstract List<MutableRel> getInputs();

    public abstract void childrenAccept(MutableRelVisitor visitor);

    /** Replaces this {@code MutableRel} in its parent with another node at the
     * same position.
     *
     * <p>Before the method, {@code child} must be an orphan (have null parent)
     * and after this method, this {@code MutableRel} is an orphan.
     *
     * @return The parent
     */
    public MutableRel replaceInParent(MutableRel child) {
      final MutableRel parent = this.parent;
      if (this != child) {
/*
        if (child.parent != null) {
          child.parent.setInput(child.ordinalInParent, null);
          child.parent = null;
        }
*/
        if (parent != null) {
          parent.setInput(ordinalInParent, child);
          this.parent = null;
          this.ordinalInParent = 0;
        }
      }
      return parent;
    }

    public abstract StringBuilder digest(StringBuilder buf);

    public final String deep() {
      return new MutableRelDumper().apply(this);
    }

    @Override public String toString() {
      throw new UnsupportedOperationException(); // call deep or digest
    }
  }

  /** Abstract base class for implementations of {@link MutableRel} that have
   * no inputs. */
  private abstract static class MutableLeafRel extends MutableRel {
    protected final RelNode rel;

    MutableLeafRel(MutableRelType type, RelNode rel) {
      super(rel.getCluster(), rel.getRowType(), type);
      this.rel = rel;
    }

    public void setInput(int ordinalInParent, MutableRel input) {
      throw new IllegalArgumentException();
    }

    public List<MutableRel> getInputs() {
      return ImmutableList.of();
    }

    public void childrenAccept(MutableRelVisitor visitor) {
      // no children - nothing to do
    }
  }

  /** Mutable equivalent of {@link SingleRel}. */
  private abstract static class MutableSingleRel extends MutableRel {
    protected MutableRel input;

    MutableSingleRel(MutableRelType type, RelDataType rowType,
        MutableRel input) {
      super(input.cluster, rowType, type);
      this.input = input;
      input.parent = this;
      input.ordinalInParent = 0;
    }

    public void setInput(int ordinalInParent, MutableRel input) {
      if (ordinalInParent >= 1) {
        throw new IllegalArgumentException();
      }
      this.input = input;
      if (input != null) {
        input.parent = this;
        input.ordinalInParent = 0;
      }
    }

    public List<MutableRel> getInputs() {
      return ImmutableList.of(input);
    }

    public void childrenAccept(MutableRelVisitor visitor) {
      visitor.visit(input);
    }

    public MutableRel getChild() {
      return input;
    }
  }

  /** Mutable equivalent of {@link TableAccessRel}. */
  private static class MutableScan extends MutableLeafRel {
    private MutableScan(TableAccessRelBase rel) {
      super(MutableRelType.SCAN, rel);
    }

    static MutableScan of(TableAccessRelBase rel) {
      return new MutableScan(rel);
    }

    @Override public boolean equals(Object obj) {
      return obj == this
          || obj instanceof MutableScan
          && rel == ((MutableScan) obj).rel;
    }

    @Override public int hashCode() {
      return rel.hashCode();
    }

    @Override public StringBuilder digest(StringBuilder buf) {
      return buf.append("Scan(table: ")
          .append(rel.getTable().getQualifiedName()).append(")");
    }
  }

  /** Mutable equivalent of {@link ValuesRelBase}. */
  private static class MutableValues extends MutableLeafRel {
    private MutableValues(ValuesRelBase rel) {
      super(MutableRelType.VALUES, rel);
    }

    static MutableValues of(ValuesRelBase rel) {
      return new MutableValues(rel);
    }

    @Override public boolean equals(Object obj) {
      return obj == this
          || obj instanceof MutableValues
          && rel == ((MutableValues) obj).rel;
    }

    @Override public int hashCode() {
      return rel.hashCode();
    }

    @Override public StringBuilder digest(StringBuilder buf) {
      return buf.append("Values(tuples: ")
          .append(((ValuesRelBase) rel).getTuples()).append(")");
    }
  }

  /** Mutable equivalent of {@link ProjectRel}. */
  private static class MutableProject extends MutableSingleRel {
    private final List<RexNode> projects;

    private MutableProject(RelDataType rowType, MutableRel input,
        List<RexNode> projects) {
      super(MutableRelType.PROJECT, rowType, input);
      this.projects = projects;
    }

    static MutableProject of(RelDataType rowType, MutableRel input,
        List<RexNode> projects) {
      return new MutableProject(rowType, input, projects);
    }

    /** Equivalent to {@link CalcRel#createProject(RelNode, List, List)}
     * for {@link MutableRel}. */
    static MutableRel of(MutableRel child, List<RexNode> exprList,
        List<String> fieldNameList) {
      final RelDataType rowType =
          RexUtil.createStructType(child.cluster.getTypeFactory(), exprList,
              fieldNameList == null
                  ? null
                  : SqlValidatorUtil.uniquify(fieldNameList,
                      SqlValidatorUtil.F_SUGGESTER));
      return of(rowType, child, exprList);
    }

    @Override public boolean equals(Object obj) {
      return obj == this
          || obj instanceof MutableProject
          && projects.equals(((MutableProject) obj).projects)
          && input.equals(((MutableProject) obj).input);
    }

    @Override public int hashCode() {
      return Util.hashV(input, projects);
    }

    @Override public StringBuilder digest(StringBuilder buf) {
      return buf.append("Project(projects: ").append(projects).append(")");
    }

    public List<RexNode> getProjects() {
      return projects;
    }

    public Mappings.TargetMapping getMapping() {
      return ProjectRelBase.getMapping(
          input.getRowType().getFieldCount(), projects);
    }
  }

  /** Mutable equivalent of {@link FilterRel}. */
  private static class MutableFilter extends MutableSingleRel {
    private final RexNode condition;

    private MutableFilter(MutableRel input, RexNode condition) {
      super(MutableRelType.FILTER, input.rowType, input);
      this.condition = condition;
    }

    static MutableFilter of(MutableRel input, RexNode condition) {
      return new MutableFilter(input, condition);
    }

    @Override public boolean equals(Object obj) {
      return obj == this
          || obj instanceof MutableFilter
          && condition.equals(((MutableFilter) obj).condition)
          && input.equals(((MutableFilter) obj).input);
    }

    @Override public int hashCode() {
      return Util.hashV(input, condition);
    }

    @Override public StringBuilder digest(StringBuilder buf) {
      return buf.append("Filter(condition: ").append(condition).append(")");
    }

    public RexNode getCondition() {
      return condition;
    }
  }

  /** Mutable equivalent of {@link AggregateRel}. */
  private static class MutableAggregate extends MutableSingleRel {
    private final BitSet groupSet;
    private final List<AggregateCall> aggCalls;

    private MutableAggregate(MutableRel input, RelDataType rowType,
        BitSet groupSet, List<AggregateCall> aggCalls) {
      super(MutableRelType.AGGREGATE, rowType, input);
      this.groupSet = groupSet;
      this.aggCalls = aggCalls;
    }

    static MutableAggregate of(MutableRel input, BitSet groupSet,
        List<AggregateCall> aggCalls) {
      RelDataType rowType =
          AggregateRelBase.deriveRowType(input.cluster.getTypeFactory(),
              input.getRowType(), groupSet, aggCalls);
      return new MutableAggregate(input, rowType, groupSet, aggCalls);
    }

    @Override public boolean equals(Object obj) {
      return obj == this
          || obj instanceof MutableAggregate
          && groupSet.equals(((MutableAggregate) obj).groupSet)
          && aggCalls.equals(((MutableAggregate) obj).aggCalls)
          && input.equals(((MutableAggregate) obj).input);
    }

    @Override public int hashCode() {
      return Util.hashV(input, groupSet, aggCalls);
    }

    @Override public StringBuilder digest(StringBuilder buf) {
      return buf.append("Aggregate(groupSet: ").append(groupSet)
          .append(", calls: ").append(aggCalls).append(")");
    }

    public BitSet getGroupSet() {
      return groupSet;
    }

    public List<AggregateCall> getAggCallList() {
      return aggCalls;
    }
  }

  /** Mutable equivalent of {@link SortRel}. */
  private static class MutableSort extends MutableSingleRel {
    private final RelCollation collation;
    private final RexNode offset;
    private final RexNode fetch;

    private MutableSort(MutableRel input, RelCollation collation,
        RexNode offset, RexNode fetch) {
      super(MutableRelType.SORT, input.rowType, input);
      this.collation = collation;
      this.offset = offset;
      this.fetch = fetch;
    }

    static MutableSort of(MutableRel input, RelCollation collation,
        RexNode offset, RexNode fetch) {
      return new MutableSort(input, collation, offset, fetch);
    }

    @Override public boolean equals(Object obj) {
      return obj == this
          || obj instanceof MutableSort
          && collation.equals(((MutableSort) obj).collation)
          && Objects.equals(offset, ((MutableSort) obj).offset)
          && Objects.equals(fetch, ((MutableSort) obj).fetch)
          && input.equals(((MutableSort) obj).input);
    }

    @Override public int hashCode() {
      return Util.hashV(input, collation, offset, fetch);
    }

    @Override public StringBuilder digest(StringBuilder buf) {
      buf.append("Sort(collation: ").append(collation);
      if (offset != null) {
        buf.append(", offset: ").append(offset);
      }
      if (fetch != null) {
        buf.append(", fetch: ").append(fetch);
      }
      return buf.append(")");
    }
  }

  /** Utilities for dealing with {@link MutableRel}s. */
  private static class MutableRels {
    public static boolean contains(MutableRel ancestor,
        final MutableRel target) {
      if (ancestor.equals(target)) {
        // Short-cut common case.
        return true;
      }
      try {
        new MutableRelVisitor() {
          @Override public void visit(MutableRel node) {
            if (node.equals(target)) {
              throw Util.FoundOne.NULL;
            }
            super.visit(node);
          }
          // CHECKSTYLE: IGNORE 1
        }.go(ancestor);
        return false;
      } catch (Util.FoundOne e) {
        return true;
      }
    }

    /** Returns whether two relational expressions have the same row-type. */
    public static boolean equalType(String desc0, MutableRel rel0, String desc1,
        MutableRel rel1, boolean fail) {
      return RelOptUtil.equal(desc0, rel0.getRowType(),
          desc1, rel1.getRowType(), fail);
    }

    public static MutableRel replace(MutableRel result, MutableRel target,
        MutableRel replace) {
      throw new UnsupportedOperationException(); // TODO:
    }

    /** Based on {@link RemoveTrivialProjectRule#strip(ProjectRel)}. */
    public static MutableRel strip(MutableProject project) {
      return isTrivial(project) ? project.getChild() : project;
    }

    /** Based on {@link RemoveTrivialProjectRule#isTrivial(ProjectRelBase)}. */
    public static boolean isTrivial(MutableProject project) {
      MutableRel child = project.getChild();
      final RelDataType childRowType = child.getRowType();
      if (!childRowType.isStruct()) {
        return false;
      }
      if (!RemoveTrivialProjectRule.isIdentity(
          project.getProjects(),
          project.getRowType(),
          childRowType)) {
        return false;
      }
      return true;
    }

    /** Equivalent to {@link CalcRel#createProject(RelNode, List)}
     * for {@link MutableRel}. */
    public static MutableRel createProject(final MutableRel child,
        final List<Integer> posList) {
      final RelDataType rowType = child.getRowType();
      if (Mappings.isIdentity(posList, rowType.getFieldCount())) {
        return child;
      }
      final RexBuilder rexBuilder = child.cluster.getRexBuilder();
      return MutableProject.of(
          RelOptUtil.permute(child.cluster.getTypeFactory(), rowType,
              Mappings.source(posList, rowType.getFieldCount())),
          child,
          new AbstractList<RexNode>() {
            public int size() {
              return posList.size();
            }

            public RexNode get(int index) {
              final int pos = posList.get(index);
              return rexBuilder.makeInputRef(rowType, pos);
            }
          });
    }

    /** Equivalence to {@link org.eigenbase.relopt.RelOptUtil#createCastRel}
     * for {@link MutableRel}. */
    public static MutableRel createCastRel(MutableRel rel,
        RelDataType castRowType, boolean rename) {
      RelDataType rowType = rel.getRowType();
      if (RelOptUtil.areRowTypesEqual(rowType, castRowType, rename)) {
        // nothing to do
        return rel;
      }
      List<RexNode> castExps =
          RexUtil.generateCastExpressions(rel.cluster.getRexBuilder(),
              castRowType, rowType);
      final List<String> fieldNames =
          rename ? castRowType.getFieldNames() : rowType.getFieldNames();
      return MutableProject.of(rel, castExps, fieldNames);
    }
  }

  /** Visitor that prints an indented tree of {@link MutableRel}s. */
  private static class MutableRelDumper extends MutableRelVisitor {
    private final StringBuilder buf = new StringBuilder();
    private int level;

    @Override public void visit(MutableRel node) {
      Spaces.append(buf, level * 2);
      if (node == null) {
        buf.append("null");
      } else {
        node.digest(buf);
        buf.append("\n");
        ++level;
        super.visit(node);
        --level;
      }
    }

    public String apply(MutableRel rel) {
      go(rel);
      return buf.toString();
    }
  }
}

// End SubstitutionVisitor.java
