# Exercises

## Exercise 1.1
Give an inductive definition of the set Var(F) of all variables that appear in formula F. For example, we have}

$Var(false \lor (X \rightarrow Y \land Z)) = \set{X,Y,Z}$

$$
\begin{aligned}

\dfrac{F \in \set{true, false}}{Var(F) = \emptyset} \\\\

\dfrac{X \in Var}{Var(X) = \set{X}} \\\\

\dfrac{F \in Prop}{Var(\lnot F) = Var(F)} \\\\

\dfrac{Var(F) = M \quad Var(G) = N \quad \bigoplus \in \set{\land, \lor, \rightarrow, \leftrightarrow}}{Var(F \bigoplus G) = Var(F) \cup Var(G)} \\\\

\end{aligned}
$$
