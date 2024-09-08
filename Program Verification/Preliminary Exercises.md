[1. Preliminaries — Program Verification](https://pv24.cmath.eu/00-preliminaries.html)
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
Inductive case 1: $e = e₁ ⊕ e₂$ 
Induction hypothesis: The statement holds for $e₁$ and $e₂$.  
Suppose $e → n$ and $e → m$. By the evaluation rule for addition:
$e₁ → v₁$ and $e₂ → v₂$ and $n = v₁ + v₂$  
$e₁ → v₁'$ and $e₂ → v₂'$ and $m = v₁' + v₂'$  
By the induction hypothesis, $v₁ = v₁'$ and $v₂ = v₂'$  
Therefore, $n = v₁ + v₂ = v₁' + v₂' = m$

Inductive case 2: $e = e₁ ⊖ e₂$
The proof is analogous to the addition case, using subtraction instead.

Therefore, by structural induction, for all $e ∈ E$ and all integers n and m,  
if $e → n$ and $e → m$, then $n = m$.  
This proves that the evaluation relation is deterministic.
$$\blacksquare$$
### Exercise 1.5
Determine all models $\mathfrak{I}:{X,Y}→\set{true,false}$ of the following formulae:

1. $(X→Y)→Y$
2. $X∧¬Y∧(X→Y)$
3. $(X \land (X \rightarrow Y)) \rightarrow Y$

#### Answer
##### 1. 
| $X$ | $Y$ | $X \rightarrow Y$ | $(X \rightarrow Y) \rightarrow Y$ |
| --- | --- | ----------------- | --------------------------------- |
| 0   | 0   | 1                 | 0                                 |
| 0   | 1   | 1                 | 1                                 |
| 1   | 0   | 0                 | 1                                 |
| 1   | 1   | 1                 | 1                                 |
$$
\begin{aligned}
\frac{X,Y = false}{\mathfrak{I} \not \models (X→Y)→Y} \\\\
\frac{\{(X, Y) \mid (X, Y) \in \{(\text{false}, \text{true}), (\text{true}, \text{false}), (\text{true}, \text{true})\}\}}{\mathfrak{I} \models (X→Y)→Y}
\end{aligned}
$$
##### 2.
| $X$ | $Y$ | $\lnot Y$ | $X \rightarrow Y$ | $X \land \lnot Y$ | $X \land \lnot Y \land (X \rightarrow Y)$ |
| --- | --- | --------- | ----------------- | ----------------- | ----------------------------------------- |
| 0   | 0   | 1         | 1                 | 0                 | 0                                         |
| 0   | 1   | 0         | 1                 | 0                 | 0                                         |
| 1   | 0   | 1         | 0                 | 1                 | 0                                         |
| 1   | 1   | 0         | 1                 | 0                 | 0                                         |
$$
\frac{X,Y \in \textbf{Var}}{\mathfrak{I} \not \models X \land \lnot Y \land (X \rightarrow Y)}
$$
##### 3.
| $X$ | $Y$ | $X \rightarrow Y$ | $X \land (X \rightarrow Y)$ | $(X \land (X \rightarrow Y)) \rightarrow Y$ |
| --- | --- | ----------------- | --------------------------- | ------------------------------------------- |
| 0   | 0   | 1                 | 0                           | 1                                           |
| 0   | 1   | 1                 | 0                           | 1                                           |
| 1   | 0   | 0                 | 0                           | 1                                           |
| 1   | 1   | 1                 | 1                           | 1                                           |
$$
\frac{X,Y \in \textbf{Var}}{\mathfrak{I} \models (X \land (X \rightarrow Y)) \rightarrow Y}
$$
##### Probably better way of answering
- For $(X→Y)→Y$: Models = {$\mathfrak{I}_1, \mathfrak{I}_2, \mathfrak{I}_3$} where: 
	- $\mathfrak{I}_1 = \set{(X,false), (Y,true)}$ 
	- $\mathfrak{I}_2 = \set{(X,true), (Y,false)}$ 
	- $\mathfrak{I}_3 = \set{(X,true), (Y,true)}$
- For $X∧¬Y∧(X→Y)$: Models = {} (empty set, as there are no models)
- For $(X \land (X \rightarrow Y)) \rightarrow Y$: Models = {$\mathfrak{I}$ | $\mathfrak{I}:{X,Y}→\set{true,false}$} (All possible interpretations are models)
### Exercise 1.6
Consider the following formula F:
$F \stackrel{\text{def}}{=} (X∨Y∨Z)∧(¬X∨Y)∧(¬Z∨Y)∧(¬Z∨¬Y)$
Is $F$ satisfiable? Is $F$ valid? Justify your answer.

#### Answer

|     |     |     | $a$               | $b$              | $c$              | $d$                    |                             |
| --- | --- | --- | ----------------- | ---------------- | ---------------- | ---------------------- | --------------------------- |
| $X$ | $Y$ | $Z$ | $X \lor Y \lor Z$ | $\lnot X \lor Y$ | $\lnot Z \lor Y$ | $\lnot Z \lor \lnot Y$ | $a \land b \land c \land d$ |
| 0   | 0   | 0   | 0                 | 1                | 1                | 1                      | 0                           |
| 0   | 0   | 1   | 1                 | 1                | 0                | 1                      | 0                           |
| 0   | 1   | 0   | 1                 | 1                | 1                | 1                      | 1                           |
| 0   | 1   | 1   | 1                 | 1                | 1                | 0                      | 0                           |
| 1   | 0   | 0   | 1                 | 0                | 1                | 1                      | 0                           |
| 1   | 0   | 1   | 1                 | 0                | 0                | 1                      | 0                           |
| 1   | 1   | 0   | 1                 | 1                | 1                | 1                      | 1                           |
| 1   | 1   | 1   | 1                 | 1                | 1                | 0                      | 0                           |
1. F is satisfiable as there exists an interpretation to satisfy $F$, for example $\mathfrak{I_1} \models F$, where $\mathfrak{I_1} = \set{(X, false), (Y, true), (Z, false)}$ 
2. $F$ is not valid, as there exists a certain $\mathfrak{I_2} \not \models F$, i.e. $\mathfrak{I_2} = \set{(X, false), (Y, false), (Z, false)}$


#### LLM Revised Answer
Consider the following formula F: $F \stackrel{\text{def}}{=} (X∨Y∨Z)∧(¬X∨Y)∧(¬Z∨Y)∧(¬Z∨¬Y)$ Is $F$ satisfiable? Is $F$ valid? Justify your answer.

1. F is satisfiable as there exists an interpretation that satisfies F. From the truth table, we can see that $\mathfrak{I_1} \models F$, where $\mathfrak{I_1} = \set{(X, false), (Y, true), (Z, false)}$. This interpretation makes all clauses of F true, resulting in F being true.
2. F is not valid, as there exists an interpretation $\mathfrak{I_2}$ such that $\mathfrak{I_2} \not\models F$. From the truth table, we can see that $\mathfrak{I_2} = {(X, false), (Y, false), (Z, false)}$ makes F false. Specifically, this interpretation makes the first clause $(X∨Y∨Z)$ false, resulting in the entire formula being false.

The truth table confirms these conclusions by showing that F is true for some rows (satisfiable) but not for all rows (not valid).

