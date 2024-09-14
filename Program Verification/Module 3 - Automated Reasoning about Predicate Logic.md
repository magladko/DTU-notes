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

# Using SAT Solver

![[using-sat-solver-slide.png]]

**Example**
```smt2
; declare variables
( declare-const X Bool )
( declare-const Y Bool )
( declare-const Z Bool )
; define formula using
; and , or , not , =>, =, xor
( assert (=> X Y Z))
( assert X) ; add and X
( check-sat ); sat or unsat
( get-model )
```
output:
```txt
$ z3 01-example.smt2
sat
 (model
	(define-fun Z () Bool false)
	(define-fun X () Bool true)
	(define-fun Y () Bool false)
)
```

# Using SAT Solver for Program Verification

![[Pasted image 20240914112504.png]]

# First Order Predicate Logic (FOL)

![[Pasted image 20240914134100.png]]

## Ingredients:

| WHAT                                          | EXAMPLE                                                              |
| --------------------------------------------- | -------------------------------------------------------------------- |
| 1. **Variables**                              | x, y, z, ...                                                         |
| 2. **Function symbols**                       |                                                                      |
| -- constants (arity 0)                        | 0, 1.5, $\pi$                                                        |
| -- operators (arity > 0)                      | +, exp, *                                                            |
| -- building blocks of **terms** (expressions) | 0, x, $x + \pi + 17 * (\exp(x)+1)$                                   |
| 3. **Relation symbols**                       | <, prime, ==                                                         |
| -- turn **terms** into logical propositions   | x<0, prime(y+17), x == x+1                                           |
| 4. **Logical connectives and quantifiers**    | $\land, \lor, \lnot, \rightarrow, \leftrightarrow, \exists, \forall$ |
| -- building blocks of **formulae**            | $x == y+1 \land \exists y. prime(y+17)$                              |

## Signatures

![[Pasted image 20240914135002.png]]
## Terms
and $\Upsigma$-terms
![[Pasted image 20240914135211.png]]

## Formulae

![[Pasted image 20240914135338.png]]

## Models of Formulae

![[Pasted image 20240914135552.png]]

## Structures

![[Pasted image 20240914135815.png]]

## Interpretations

![[Pasted image 20240914140551.png]]

## Semantics of First-Order Predicate Logic

![[Pasted image 20240914140807.png]]


