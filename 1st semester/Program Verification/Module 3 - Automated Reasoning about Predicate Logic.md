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

![[using-sat-solver-slide 1.png]]

# First Order Predicate Logic (FOL)

![[proplogic-not-enough-slide.png]]

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

![[signatures-slide.png]]
## Terms
and $\Upsigma$-terms
![[terms-slide.png]]
## Formulae

![[formulae-slide.png]]
## Models of Formulae

![[models-of-formulae-slide.png]]
## Structures

![[structures-slide.png]]
## Interpretations

![[interpretations-slide.png]]
## Semantics of First-Order Predicate Logic

![[semantics-of-fol-slide.png]]

# Satisfiability Modulo Theories (SMT)
## FOL Satisfiability

![[fol-satisfiability-slide.png]]

## SMT

![[smt-slide.png]]

## Axiom Systems
 ![[axioms-systems-slide.png]]

## Example

### Theory of Equality EQ
- **Signature:** $\upsigma \stackrel{\text{def}}{=} \langle \emptyset, \set{ == /2}\rangle$
- **Axioms** determining the theory:
	- $\forall x. x == x$                                                (reflexivity)
	- $\forall x. \forall y. x == y \rightarrow y == x$                          (symmetry)
	- $\forall x. \forall y. \forall z. (x ==y \land y == z) \rightarrow x == z$   (transitivity)

Are these formulae satisfiable module EQ?
1. $x == y \land \lnot(y == z)$ **OK**
2. $x == y \land \lnot (y == z) \land (z == x \lor x == z)$ **NOT**
3.  $\exists x. \lnot(x==y)$ **OK**

### Theory of Equality with Uninterpreted Functions EUF
- **Signature:** $\upsigma \stackrel{def}{=}\langle \set{f_1/n_1,f_2/n_2,...}, \set{== /2}$
- **Axioms** determining the theory:
	- $\forall x. x ==x$
	- $\forall x. \forall y. x == y \rightarrow y == x$
	- $\forall x. \forall y. \forall z. (x == y \land y == z) \rightarrow x == z$
	- for all $f/n \in \textbf{Fun}$:
		- $\forall x_1. \forall y_1. \text{...} \forall x_n. \forall y_n. (x_1 == y_1 \land ... \land x_n == y_n) \rightarrow f(x_1, ..., x_n) == f(y_1, ..., y_n)$

![[euf-example-slide.png]]

## Exercise
Consider the signature $\Sigma \stackrel{def}{=}\langle\emptyset, \set{E/2, ==/2}\rangle$
Give axioms determining the theory of...

starting from EQ axioms:
$\forall x.x == x \quad \forall x. \forall y.x == y \rightarrow y == x \quad \forall x. \forall y. \forall z. (x == y \land y == z) \rightarrow x == z$
1. undirected graphs with edge relation E and without self-loops
$$
\begin{aligned}
\forall x. \forall y. E(x,y) \rightarrow E(y,x) \\
\forall x. \forall y. E(x,y) \rightarrow \lnot (x == y)
\end{aligned}
$$
2. structures whose universe contains more than two elements
$$
\exists x. \exists y. \exists z. \lnot (x == y) \land \lnot (x == z) \land \lnot (y == z)
$$
## Decidability of SMT
- EUF: decidable for quantifier-free formulae
- Arithmetic (with canonical axioms)
	- Presburger arithmetic - decidable
	- Peano arithmetic - undecidable
	- Real arithmetic - decidable
![[smt-decidability.png]]

## Many-Sorted First-Order Predicate Logic
**Working with multiple data types**
nothing new, just convenient syntax on top of FOL

![[many-sorted-fol-slide.png]]

### Example

**Theory of Arrays**
- Sorts: Array, Int
- Function symbols: 
	- **read**: Array Int Int
	- **write**: Array Int Int Array
- Relation symbols: 
	- == : Int Int
	- == : Array Array
- Selected **axioms**:
	- $\forall a: \text{Array}. \forall i: \text{Int}. \forall v: \text{Int}. \text{read}(\text{write}(a, i, v), i) == v$
	- $\forall a: \text{Array}. \forall i: \text{Int}. \forall j: \text{Int}. \forall v: \text{Int}. \lnot (i == j) \rightarrow \text{read}(\text{write}(a,i,v),j) == \text{read}(a,j)$
	- $\forall a: \text{Array}. \forall b: \text{Array}. (\forall i: \text{Int}. \text{read}(a,i) == \text{read}(b,i)) \rightarrow a == b$
# Summary

- $\Sigma$: **signature** that determines the symbols we are allowed to use
- Many-sorted setting: $\Sigma$ also defines available types; all symbols must be *well-typed*
- t: **$\Sigma$-term**, i.e. expression over the allowed symbols
- F: **$\Sigma$-formula**, i.e. logical formula over the allowed symbols
- $\mathfrak{A}$: **$\Sigma$-structure** that determines the *meaning* of symbols
	- Universe **A**: set of concrete values (of variables, that can be returned by functions, etc.)
	- $f^\mathfrak{A}$: actual function assigned to the symbol $f$ by $\mathfrak{A}$
- $\Sigma$-interpretation $\mathfrak{I}$: structure $+$ assignment of concrete values to variables 
	- (*everything needed to evaluate terms and formulae*)
- $\mathfrak{I}$ is a **model** of $F$ iff $F$ evaluates to true for interpretation $\mathfrak{I}$
- **$\Sigma$-theory Th**: set of formulae that constrain the interpretations of interest
- **Satisfiability module theory Th**: Find a model of $F$ and all formulae in **Th**
![[fol-smt-summary.png]]

# First SMT Example

## SMT-LIB

![[smt-lib-slide.png]]
## Z3Py

![[smt-z3py-slide.png]]

## Built-in Theories
easiest -> hardest
![[built-in-theories-marked-slide.png]]
- **(Quantifier-Free) Linear Integer/Real Arithmetic**
	- QF_LIA, LIA / QF_LRA, LRA **(Presburger \[for int\]/DECIDABLE)**
	- 19*x + 2*y == 42
- **Non-Linear Integer/Real Arithmetic**
	- NIA / NRA **(Peano \[for int\]/UNDECIDABLE)**
	- x * y + 2*x * y + 1 == (x + y) * (x + y)
- **Quantifier-free fixed-size bitvector arithmetic**:
	- QF_BV
	- $x \& y \leq x \textbar y$

```smt2
(set-logic QF_LIA) ; prevent automatic logic selection
```
-> good to self-check if problem stays in the expected theory set

```smt2
(set-logic QF_NIA) ; UNDECIDABLE
(set-option :timeout 5000) ; <- as undecidable, can consume all resources
```

# Incorporating Custom Theories in Program Verification

![[custom-theories-in-PV-slide.png]]


## Axioms as trusted codebase
![[axioms-trustedcodebase-slide.png]]

# Limitations of SMT Solvers

![[limits-of-smt-solvers-slide.png]]

![[limits-of-smt-solvers-summary-slide.png]]

![[universal-quantifier-instantiation-idea.png]]

![[univ-quantifier-instantiation-problems-slide.png]]\

![[picking-terms-for-uq-slide.png]]

**Problem: Search Space Explosion**
![[search-space-explosion-slide.png]]

![[patterns-triggers-slide.png]]

![[e-matching-slide.png]]
return unknown if no more terms e-match the quantifier's pattern


![[e-matching-z3-slide.png]]

![[m3-wrap-up.png]]
