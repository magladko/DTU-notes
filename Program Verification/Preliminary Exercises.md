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

If $F \in \set{true, false}$, then we have $Var(F) = \emptyset$ and $sub(F) = \set{F}$ and $\emptyset \subseteq F$, so
$$
\frac{F \in \set{true, false}}{Var(F) \subseteq sub(F)}
$$
If F = X, where $X \in \textbf{Var}$, then $Var(F) = \set{F}$ and $sub(F) = \set{F}$, so
$$
\frac{F = X \quad X \in \text{Var}}{Var(F) \subseteq sub(F)}
$$
From I.H. for $G, H \in \textbf{Prop}$ we have $Var(G) \subseteq sub(G)$ and $Var(H) \subseteq sub(G)$

If $F = \lnot{G}$, where $G \in \textbf{Prop}$ then 
- $Var(F) = Var(G)$ and 
- $sub(F) = \set{F} \cup sub(G)$
Since $Var(G) ⊆ sub(G)$ and $sub(G) ⊆ sub(F)$, we have $Var(F) ⊆ sub(F)$
$$
\frac{F = \lnot G \quad G \in \textbf{Prop}}{Var(F) \subseteq sub(F)}
$$
If $F = G ∧ H$ then 
- $Var(F) = Var(G) \cup Var(H)$ which is the same as $Var(F) = \emptyset \cup Var(G) \cup Var(H)$
- $sub(F) = \set{F} \cup sub(G) \cup sub(H)$
and we know that 
$\emptyset \cup Var(G) \cup Var(H) \subseteq \set{F} \cup sub(G) \cup sub(H)$, hence
$$Var(F) \subseteq sub(F)$$
The cases for $F=G∨H,G→H,G↔H$ are completely analogous.
$$\blacksquare$$
## Exercise 1.4

Use structural induction to show that your evaluation relation $→$ from **Exercise 1.2** is $deterministic$, i.e. every expression always evaluates to a unique value. More precisely, show that, for every expression $e∈E$ and all integers $n$ and $m$, we have
$$e \rightarrow n \text{ and } e \rightarrow m \text{ implies } n = m$$
### Answer

#### Base case
If $e = k$ where $k = const$, then 
1. $e \rightarrow n$ implies $k \rightarrow n$ by the (Const) rule, so $k = n$
2. $e \rightarrow m$ implies $k \rightarrow m$ by the (Const) rule, so $k = m$
3. Hence $n = m$
#### Inductive cases


Certainly, I'd be happy to provide some hints and then give a full solution. Let's start with the hints:

1. Remember that structural induction follows the structure of the grammar. You'll need to consider three cases: constants, addition, and subtraction.

2. For the base case (constants), think about how a constant evaluates and why it's deterministic.

3. For the inductive cases (addition and subtraction), you'll need to use the induction hypothesis on the subexpressions.

4. Consider what the evaluation rules tell you about the relationship between the values of subexpressions and the final result.

5. You'll need to show that if two evaluations of the same expression yield different results, it leads to a contradiction with the induction hypothesis.

Now, here's the full solution hidden as requested:

> [!question]- Solution
> We will prove this by structural induction on the expression e.
> 
> Base case: e = k (constant)
> For any constant k, the only applicable rule is (Const), which states k → k.
> Therefore, if e → n and e → m, we must have n = k and m = k, so n = m.
> 
> Inductive case 1: e = e₁ ⊕ e₂
> Induction hypothesis: The statement holds for e₁ and e₂.
> Suppose e → n and e → m. By the evaluation rule for addition:
> e₁ → v₁ and e₂ → v₂ and n = v₁ + v₂
> e₁ → v₁' and e₂ → v₂' and m = v₁' + v₂'
> By the induction hypothesis, v₁ = v₁' and v₂ = v₂'
> Therefore, n = v₁ + v₂ = v₁' + v₂' = m
> 
> Inductive case 2: e = e₁ ⊖ e₂
> The proof is analogous to the addition case, using subtraction instead.
> 
> Therefore, by structural induction, for all e ∈ E and all integers n and m,
> if e → n and e → m, then n = m.
> This proves that the evaluation relation is deterministic.

This proof demonstrates that no matter how we evaluate an expression, we always get the same result, which is the essence of determinism in this context.
