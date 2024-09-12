# The Satisfiability (SAT) Problem for Propositional Logic

> $F$ is **satisfiable** iff $F$ has *some* model
> **Example**: 
> $F =  (X \rightarrow Y) \rightarrow Y$
> Models: $[X = true, Y = true] \quad [X = false, Y = true] \quad [X = true, Y = false]$
---
> $F$ is ***un*satisfiable** iff $F$ has *no* model
> **Example:** $X \land \lnot Y \land (X \rightarrow Y)$
---
> $F$ is **valid** iff *every* interpretation is a model of $F$ (aka: $\lnot F$ is unsatisfiable)
> **Example:** $X \land (X \rightarrow Y)) \rightarrow Y$

### Task
$F \stackrel{\text{def}}{=} (X \lor Y \lor Z) \land (\lnot X \lor Y) \land (\lnot Z \lor Y) \land (\lnot Z \lor \lnot Y)$
- Is F valid? **NO**, for example: $[X = false, Y = false, Z = false]$
- Is F satisfiable? **YES**: for example: $[X = false, Y = true, Z = false]$

| X   | Y   | Z   | $X \lor Y \lor Z$ | $\lnot X \lor Y$ | $\lnot Z \lor Y$ | $\lnot Z \lor \lnot Y$ | $F$ |
| --- | --- | --- | ----------------- | ---------------- | ---------------- | ---------------------- | --- |
| 0   | 0   | 0   | 0                 | 1                | 1                | 1                      | 0   |
| 0   | 0   | 1   | 1                 | 1                | 0                | 1                      | 0   |
| 0   | 1   | 0   | 1                 | 1                | 1                | 1                      | 1   |
| 0   | 1   | 1   | 1                 | 1                | 1                | 0                      | 0   |
| 1   | 0   | 0   | 1                 | 0                | 1                | 1                      | 0   |
| 1   | 0   | 1   | 1                 | 0                | 0                | 1                      | 0   |
| 1   | 1   | 0   | 1                 | 1                | 1                | 1                      | 1   |
| 1   | 1   | 1   | 1                 | 1                | 1                | 0                      | 0   |
## SAT

> **SAT:** Given a propositional logic formula, decide whether it is satisfiable ( and provide a model as a **witness** if possible)

**SAT** is *the* classical **NP-complete problem**:
- We can efficiently check whether a *given* interpretations is a model
- Every algorithm ultimately searches through all possible interpretations
- Finding a model is expensive:
  $n$ variables $\rightsquigarrow 2^n$  interpretations
- Many interesting problems can be efficiently encoded as instances of **SAT** e.g circuit design, vehicle routing etc.
![[sat-slide.png]]
![[sat-bpt-example.png]]