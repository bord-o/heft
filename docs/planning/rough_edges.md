# Rough Edges

- Application with nested quantifier structure
- Negation reasoning is split between ~ and = F
- ppx will silently convert to a var instead of constant if you give an annotation
- With ppx based theorems, they return a goal from the binding instead of a thm. Could silently fail with [@quiet]
    - Should they return option/result? Crash at runtime?
