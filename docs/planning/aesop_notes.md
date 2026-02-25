# Aesop

## Key elements

- Backtracking search
- User defined rules
- Custom priority of rules (tactics and rewrites?)
- Customizable simplifier
- Visible and easy to predict
- Custom algorithm for picking metavariables during rewriting 
- Considers more promising rules (and their subgoals) first
- No backtracking for safe rules, only unsafe
- In addition to safe/unsafe, rules can be marked for normalization
- Subgoal priority is initial goal priority multiplied by applied rule priority


## Terms

rule = arbitrary tactic
goal = hypotheses + conclusion
rule = partial function from goal to goals

unsafe rule = doesn't preserve provability

## Differences with Heft

They talk about metavariables across multiple goals, but our goal solving is sequential, maybe we won't have this problem.

Our rules are functions from goal -> thm, where subgoals are handled sequentially by effects

They say that their metavariable instantiation isn't the best, failing to solve nontrivial exists goals, maybe we skip this or only pick witnesses from local context

## Notes

safe rules should preserve provability, so if their subgoals are proved, then the justification should go through (tactics are correct)

ranks both goals and rules with heuristics. For ranking goal/rule combos we might want to add a rankeable type which considers all pairs

aesop is fixed in their heuristic usage, heft will have the ability to change these on the fly

they use indexed trees of pattern->rule to pick, I think that a general ranking on the product of rules x goals would cover this behavior, just slower

When a safe rule applies it adds subgoals to the queue, but not a copy of the original goal (no branch)

### Tree

goal nodes and rule app nodes
nodes are in one of three states
    | proved
    | stuck
    | unknown
node because irrelevant if one of its parents is proved (left side of OR)


## Concrete questions

- How do we skip extra work for irrelevant subgoals? i.e. short circuit when we prove one side of a disjunction?
    - Think we do this automatically because by default we will just choose one goal and then fail if it doesn't work, our searches will just avoid multiple
        resumption in the case where we get a thm output. This is something to note in the paper
- How do we make sure that safe rules don't backtrack? In lean they have an explicit goal queue, but we do not. Safe rules should prevent backtracking
    - A "Cut" effect?
    - I don't think I need cut, just avoid using Choose for subgoals in safe tactics.

## implementation
```ocaml
type _ rankable =
  | Priority : (tactic * priority * goal) list -> (tactic * goal) rankable
```

use a rankable like this to get the tactic/goal and then use choose_term goal to pick the appropriate subgoal to use

