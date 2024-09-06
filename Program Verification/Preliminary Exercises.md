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
Show that, for every formula F, we have

$Var(F) \subseteq sub(F)$

In other words, every variable that appears in $F$ is a subformula of $F$.

### Answer

$$
\begin{aligned}
%% \frac{F \in Prop \quad X \in Var}{Var(F) \in \set{true, false, X}} \\\\
%% \frac{}{sub(X) = \set{X}}

\frac{X \in {true, false}}{Var(F) = \emptyset \quad sub(F)=\set{F}}


%% \frac{sub(F) = \set{true}}{Var(F) = sub(F)} \\\\
%% \frac{sub(F) = \set{false}}{Var(F) = sub(F)} \\\\
%% \frac{X \in Var \quad sub(F) = \set{X}}{Var(F) = sub(F)} \\\\
%% \frac{sub(F \oplus G) \quad \oplus \in \set{\land,\lor,\rightarrow}}{sub(F \oplus G)=sub(F \oplus G)\cup sub(F) \cup sub(G)} \\\\

\end{aligned}
$$




---
I'd be happy to provide some hints and a covered answer for this exercise. Let's start with some hints to guide you through the problem:

Hints:

1. Consider the structure of propositional formulas. How are they built up?

2. Think about the definitions of Var(F) and sub(F). How are they defined for different types of formulas?

3. The proof might be best approached using structural induction. What would be your base cases and inductive steps?

4. For the base cases, consider the simplest formulas: true, false, and atomic propositions (variables).

5. For the inductive steps, think about how Var(F) and sub(F) are defined for compound formulas (those involving connectives like ∧, ∨, →, ¬).

6. Remember that to prove A ⊆ B, you need to show that every element of A is also an element of B.

These hints should help you structure your proof. If you'd like to see a full answer, you can reveal the spoiler below. However, I encourage you to try working through the proof yourself first using these hints.

<spoiler>
Proof:
We will prove that Var(F) ⊆ sub(F) for every formula F by structural induction on F.

Base cases:
1) For F = true or F = false:
   Var(F) = ∅ and sub(F) = {F}
   Clearly, ∅ ⊆ {F}, so Var(F) ⊆ sub(F)

2) For F = X, where X is a propositional variable:
   Var(F) = {X} and sub(F) = {X}
   Since {X} ⊆ {X}, we have Var(F) ⊆ sub(F)

Inductive steps:
Assume the property holds for formulas G and H, i.e., Var(G) ⊆ sub(G) and Var(H) ⊆ sub(H).

3) For F = ¬G:
   Var(F) = Var(G)
   sub(F) = {F} ∪ sub(G)
   Since Var(G) ⊆ sub(G) and sub(G) ⊆ sub(F), we have Var(F) ⊆ sub(F)

4) For F = G ∧ H (similar for ∨, →):
   Var(F) = Var(G) ∪ Var(H)
   sub(F) = {F} ∪ sub(G) ∪ sub(H)
   Since Var(G) ⊆ sub(G) and Var(H) ⊆ sub(H), and both sub(G) and sub(H) are subsets of sub(F),
   we have Var(F) ⊆ sub(F)

By the principle of structural induction, we conclude that Var(F) ⊆ sub(F) holds for all formulas F.
</spoiler>

Let me know if you need any clarification on the hints or if you'd like to discuss your approach to the proof!