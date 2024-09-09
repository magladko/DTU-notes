[Slides](https://learn.inside.dtu.dk/d2l/le/lessons/215949/topics/867655)

# Goal: build a verifier for a toy programming language

- **The Ground-Truth**: what is a "correct" toy program $\models \set{\set{\quad F \quad}}\quad C \quad \set{\set{\quad G \quad}}$
- **Floyd-Hoare (Program) Logic**: how do we write formal correctness proofs on paper?
- **Soundness**: why can we trust our proofs?
- **Completeness**: what can we prove?
- **Automation**: how do we systematically construct proofs?

# Expressions, Formulae, and Commands

## Definition (Syntax of Toy Language)
$a ::= k \quad | \quad x \quad | \quad a + a$  (arithmetic expressions) | note: $k \in \mathbb{Z}$ and $x$ is a variable

| def                                                                     | what                   | note                                     |
| ----------------------------------------------------------------------- | ---------------------- | ---------------------------------------- |
| $a ::= k \textbar x \textbar a + a$                                     | arithmetic expressions | $k \in \mathbb{Z}$ and $x$ is a variable |
| $F ::= a > a \textbar \lnot F \textbar F \land F \textbar \exists x. F$ | logical formulae       |                                          |
| ...                                                                     |                        |                                          |

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

# 1-4 Floyd-Hoare Logic

> **Idea**: define judgements $\vdash \set{\set{F}}X\set{\set{G}}$ (read $\vdash$ as *provable*) such that
> $\vdash \set{\set{F}}C \set{\set{G}}$ implies $\models \set{\set{F}}C\set{\set{G}}$

Judgement $\vdash$ is bashed on *proof rules* without computing explicit executions

## Proof trees

$\frac{}{\text{conclusion}} \text{AXIOM}$  | $\frac{premises}{conclusion}\text{RULE}$

$$
\frac{\frac{}{\text{axiom}} \quad \frac{\frac{}{\text{other axiom}}}{\text{some premise}}}{\vdash \set{\set{F}} C \set{\set{G}}}
$$

Sketched proof tree with conclusions
$$
\vdash \set{\set{F}} C \set{\set{G}}
$$
### The skip rule

$$
\frac{}{\vdash \set{\set{F}} \textbf{ skip} \set{\set{F}}}\text{SKIP}
$$
**NOTE**: skip rule does not admit conclusions (sth like ~~x > 0 -> x >= 0~~)
![[fh-skip.png]]

### The consequence rule
**Entailment** $F \models G$: for all $\mathfrak{m}$, if $\mathfrak{m} \models F$ then also $\mathfrak{m} \models G$
$$
\frac{F \models F' \quad \vdash \set{\set{F}} C \set{\set{G'}} \quad G' \models G}{\vdash \set{\set{F}} C \set{\set{G}}}\text{CONSEQUENCE}
$$
![[fh-consequence.png]]
### The sequential composition rule
**Main idea**: decompose triples into smaller ones until we end up with obvious facts

$$
\frac{\vdash \set{\set{F}} C_1 \set{\set{H}} \quad \vdash \set{\set{H}} C_2 \set{\set{G}}}{\vdash \set{\set{F}}C_1; C_2 \set{\set{G}}}\text{SEQUENCE}
$$
![[fh-sequence.png]]



