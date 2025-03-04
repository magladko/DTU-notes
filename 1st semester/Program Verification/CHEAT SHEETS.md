# Propositional Logic
![[propositional-logic-cheatsheet.png]]
# Syntax of Toy Language (Definition)

| def                                                                                                      | what                              | note                                     |
| -------------------------------------------------------------------------------------------------------- | --------------------------------- | ---------------------------------------- |
| $a ::= k \textbar x \textbar a + a$                                                                      | arithmetic expressions            | $k \in \mathbb{Z}$ and $x$ is a variable |
| $F ::= a > a \textbar \lnot F \textbar F \land F \textbar \exists x. F$                                  | logical formulae                  |                                          |
| $b::= a>a \textbar \lnot b \textbar b \land b$                                                           | Boolean expressions; no $\exists$ |                                          |
| $C::=\textbf{skip} \textbar x:=a \textbar C;C \textbar \textbf{ if } (b) \set{C} \textbf{ else} \set{C}$ | commands                          |                                          |

\+ **syntactic sugar**
$$
\begin{aligned}
5*x & \stackrel{\text{def}}{=} & x+x+x+x+x \\
a_1 == a_2 & \stackrel{\text{def}}{=} &(\lnot(a_1>a_2)\land(\lnot(a_2>a_1)) \\
F \lor G & \stackrel{\text{def}}{=} & \lnot(\lnot F \land \lnot G) \\
F \rightarrow G & \stackrel{\text{def}}{=} & (\lnot F) \lor G
\end{aligned}
$$
# Operational Semantics
![[01-operational-semantics.png]]

# Floyd-Hoare Logic for Toy Programs (execution steps)
![[fh-cheatsheet.png]]
# Weakest Precondition
![[weakest-precondition-cheatsheet.png]]

# Semantics of First-Order Predicate Logic (FOL)

![[semantics-of-fol-slide.png]]

# FOL/SMT Summary
![[fol-smt-summary.png]]
# Decidability
![[smt-decidability.png]]

# Sets of preconditions
![[swp.png]]