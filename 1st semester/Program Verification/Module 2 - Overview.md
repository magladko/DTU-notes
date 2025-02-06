[Slides](https://learn.inside.dtu.dk/d2l/le/lessons/215949/topics/867655)

# Goal: build a verifier for a toy programming language

- **The Ground-Truth**: what is a "correct" toy program $\models \set{\set{\quad F \quad}}\quad C \quad \set{\set{\quad G \quad}}$
- **Floyd-Hoare (Program) Logic**: how do we write formal correctness proofs on paper? $\dashv \set{\set{F}} C \set{\set{G}}$
- **Soundness**: why can we trust our proofs? $\dashv ... \text{implies} \models ...$
- **Completeness**: what can we prove? Every valid triple
- **Automation**: how do we systematically construct proofs? Use SMT solver like Z3 to discharge the *verification condition* $F \models wp[C](G)$

# Expressions, Formulae, and Commands

## Definition (Syntax of Toy Language)

| def                                                                                                      | what                              | note                                     |
| -------------------------------------------------------------------------------------------------------- | --------------------------------- | ---------------------------------------- |
| $a ::= k \textbar x \textbar a + a$                                                                      | arithmetic expressions            | $k \in \mathbb{Z}$ and $x$ is a variable |
| $F ::= a > a \textbar \lnot F \textbar F \land F \textbar \exists x. F$                                  | logical formulae                  |                                          |
| $b::= a>a \textbar \lnot b \textbar b \land b$                                                           | Boolean expressions; no $\exists$ |                                          |
| $C::=\textbf{skip} \textbar x:=a \textbar C;C \textbar \textbf{ if } (b) \set{C} \textbf{ else} \set{C}$ | commands                          |                                          |
|                                                                                                          |                                   |                                          |

\+ **syntactic sugar**
$$
\begin{aligned}
5*x & \stackrel{\text{def}}{=} & x+x+x+x+x \\
a_1 == a_2 & \stackrel{\text{def}}{=} &(\lnot(a_1>a_2)\land(\lnot(a_2>a_1)) \\
F \lor G & \stackrel{\text{def}}{=} & \lnot(\lnot F \land \lnot G) \\
F \rightarrow G & \stackrel{\text{def}}{=} & (\lnot F) \lor G
\end{aligned}
$$

![[01-operational-semantics.png]]
### Toy program execution
![[toy program execution.png]]
# 1-3 Valid Triples

## Exercise 
#### Definition (read $\models$ as the triple is **valid**)

> $\models \set{\set{F}} C \set{\set{G}}$ iff
> for all $\mathfrak{m}$, $m'$, if $m \models F$ and $<C, m> \implies^* <done, m'>$ then $m' \models G$.

#### Task
Argue whether the following triple is valid or not:
$$
\models \set{\set{y > 0}}\text{ if }(x ==0) \set{skip}\text{ else }\set{y := x + x}; z := y + x + y \set{\set{z == 5 * x}}
$$
##### Solution: the triple is *not* valid

**Counterexample:** $\mathfrak{m} \models y > 0$ and 
$$
\begin{aligned}
& (\text{if }(x == 0)\set{skip}\text{ else }\set{y := x+x};z := y + x + y, \mathfrak{m}) \\
\implies & (\textbf{skip};z:=y+x+y, \mathfrak{m}) \\
\implies & (z:=y+x+y, \mathfrak{m}) \\
\implies & (\text{done}, \mathfrak{m}[z \leftarrow 10]) \\
& \mathfrak{m}[z \leftarrow 10] \not\models z == 5*x \text{ since } \mathfrak{m}[z \leftarrow 10 ](z)
\end{aligned}
$$
for

| $x$ | $\mathfrak{m}(x)$ | $\mathfrak{m}[z \leftarrow 10](x)$ |
| --- | ----------------- | ---------------------------------- |
| $x$ | 0                 | 0                                  |
| $y$ | 5                 | 5                                  |
| $z$ | 0                 | 10                                 |

[[Module 2 - Floyd-Hoare logic]]

# Theorem (Soundness)

$$
\vdash \set{\set{F}} C \set{\set{G}} \text{ implies } \models \set{\set{F}} C \set{\set{G}}
$$\

Intuition: as discussed for each F-H rule
Detailed proof: by rule induction, see lecture notes

# Proof outlines

![[proof-outlines.png]]

# Obstacles to Automation
![[obstacles-to-automation-slide.png]]

# The Weakest Precondition
## Main idea

$wp[C](G)$: *all initial memories* $\mathfrak{m}$ such that $<C,\mathfrak{m}>$ terminates in memories satisfying $G$

**Think:** input sanitization "In what inputs will the command behave correctly"

![[weakest-precondition.png]]

**We will show:** no choices need, using the rule of consequence once suffices
$$
F \models wp[C](G) \text{ iff } \models \set{\set{F}} C \set{\set{G}}
$$

**The Weakest Precondition - Definition**

| $C$                                                   | $wp[C](G)$                                                        |
| ----------------------------------------------------- | ----------------------------------------------------------------- |
| **skip**                                              | $G$                                                               |
| $x:=a$                                                | $G[x:=a]$                                                         |
| $C_1;C_2$                                             | $wp[C_1](wp[C_2](G))$                                             |
| $\textbf{if } (b) \set{C_1} \textbf{ else} \set{C_2}$ | $(b \rightarrow wp[C_1](G))\land(\lnot b \rightarrow wp[C_2](G))$ |
**Lemma (Soundness of wp)**
$$
\vdash \set{\set{wp[C](G)}} C \set{\set{G}}
$$
**Lemma**
If $\mathfrak{m} \not\models wp[C](G)$ and $<C,\mathfrak{m}> \implies^* <done, \mathfrak{m'}>$ then $\mathfrak{m'} \not\models G$.

**Theorem (Soundness and Completeness of Weakest Precondition)**
$$
F \models wp[C](G) \quad \text{iff} \quad \models \set{\set{F}} C \set{\set{G}}
$$

## Weakest Precondition exercise

```
{{ y == 7 & x == 3 }}
z:=x;
{{ y == 7 & z == 3 }}
x:=y;
{{ x == 7 & z == 3 }}
y:=z
{{ x == 7 & y == 3 }}
```

# Automation of Program Verification

- **Previously:** To prove $\models \set{\set{F}} C \set{\set{G}}$, it suffices to show $F \models wp[C](G)$
- **Problem:** How do we prove entailments $F \models H$?
- **Good news:** There are automated provers for *satisfiability* of logical formulae
> $H$ is *satisfiable* iff there is a state $\mathfrak{m}$ such that $\mathfrak{m} \models H$
- **Reduction:** 
$$
\begin{aligned}
H \models H & \text{ iff} \quad \text{there is no } \mathfrak{m} \text{ such that } \mathfrak{m} \models F \land \lnot H \\
& \text{ iff} \quad F \land \lnot H \text{ unsatisfiable}
\end{aligned}
$$

## Languages and Tools
### SMT-LIB

![[smt-lib.png]]
### Z3

![[z3.png]]
