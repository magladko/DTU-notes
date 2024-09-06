[Source website](https://pv24.cmath.eu/00-preliminaries.html)
# Exercises

## Exercise 1.1
Give an inductive definition of the set Var(F) of all variables that appear in formula F. For example, we have}

$Var(false \lor (X \rightarrow Y \land Z)) = \set{X,Y,Z}$
### Answer

$$
\begin{aligned}

\dfrac{F \in \set{true, false}}{Var(F) = \emptyset} \\\\

\dfrac{X \in Var}{Var(X) = \set{X}} \\\\

\dfrac{F \in Prop}{Var(\lnot F) = Var(F)} \\\\

\dfrac{Var(F) = M \quad Var(G) = N \quad \oplus \in \set{\land, \lor, \rightarrow, \leftrightarrow}}{Var(F \oplus G) = Var(F) \cup Var(G)} \\\\

\end{aligned}
$$
## Exercise 1.2 
Consider the set E of simple arithmetic expressions given by the following grammar:
$$
\begin{aligned}
e ::= \quad & k && \text{(constant integer number)} \\
    | \quad & e \oplus e && \text{(addition)} \\
    | \quad & e \ominus e && \text{(subtraction)}
\end{aligned}
$$

Give an inductive definition of a binary evaluation relation
$$
\rightarrow \subseteq \boldsymbol{E} \times \mathbb{Z}
$$
such that $(e,v) \in \rightarrow$, which we also write as $e \rightarrow v$, holds if and only if $v$ is the value obtained from evaluating expression $e$.

For example, we have $(19 \oplus 23) \ominus 42 \rightarrow 0$.
### Answer

$$
\begin{aligned}
\frac{}{k \rightarrow k} \quad \text{(Const)}\\\\
\frac{e_1 \rightarrow v_1 \quad e_2 \rightarrow v_2}{e_1 \oplus e_2 \rightarrow v_1 + v_2} \\\\
\frac{e_1 \rightarrow v_1 \quad e_2 \rightarrow v_2}{e_1 \ominus e_2 \rightarrow v_1 - v_2} \\\\

\end{aligned}
$$
## Exercise 1.3
