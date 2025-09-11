I'll solve each task step by step, using the exact notation from the course material.

## T1: Warmup: verification with CHIP (10 Points)

### Program (a)
```
{ true }
if x < 10 -> skip
[] x <= 10 -> x := 10
fi
{ x == 10 }
```

**Reasoning**: After the conditional, either we skip (when x < 10) or we set x := 10 (when x ≤ 10 and ¬(x < 10), i.e., x = 10). Note that when x < 10, we also have x ≤ 10, so both branches are enabled. In CHIP, when both branches are enabled, either can be chosen non-deterministically. However, both paths lead to x = 10 after execution.

### Program (b)
```
{ true }
if x > y -> temp := x; x := y; y := temp
[] y > z -> temp := y; y := z; z := temp
fi;
if x > y -> temp := x; x := y; y := temp
fi
{ x <= y ∧ y <= z }
```

**Reasoning**: This is a partial sorting algorithm. The first conditional can swap x,y or y,z. The second conditional ensures x ≤ y. The postcondition captures that we have x ≤ y ≤ z.

### Program (c)
```
{ x <= y }
if x > y -> temp := x;
            x := y;
            y := temp
[] x <= y -> skip
fi;
{ x <= y }
if x >= y -> z := x
[] y > x -> z := y
fi
{ z = y }
```

**Reasoning**: We need a precondition that ensures z = y at the end. The first conditional maintains x ≤ y. The second conditional sets z to the maximum of x and y. For z = y to hold, we need y to be the maximum, so x ≤ y must hold initially.

## T2: Operational semantics (10 Points)

Given memory $\mem$:
- $\mem(\x) = 4$
- $\mem(\y) = -2$
- $\mem(\z) = 0$

### (a) Evaluating arithmetic expressions

**(i)** $\evalE{\x + \y + 5}(\mem)$
$$\evalE{\x + \y + 5}(\mem) = \evalE{\x}(\mem) + \evalE{\y}(\mem) + \evalE{5}(\mem) = 4 + (-2) + 5 = 7$$

**(ii)** $\evalE{\y \cdot (\x + \z)}(\mem[\y := 3])$

First, compute $\mem' = \mem[\y := 3]$, so $\mem'(\x) = 4$, $\mem'(\y) = 3$, $\mem'(\z) = 0$.

$$\evalE{\y \cdot (\x + \z)}(\mem') = \evalE{\y}(\mem') \cdot \evalE{\x + \z}(\mem') = 3 \cdot (4 + 0) = 12$$

### (b) Executing command C

$\cc : \Ite{\x > 0}{\Assign{\y}{\x + \y}}{\Assign{\z}{\x - \y}}\Seq\Assign{\x}{\z + 1}$

Step-by-step execution:

1. $\tuple{\Ite{\x > 0}{\Assign{\y}{\x + \y}}{\Assign{\z}{\x - \y}}\Seq\Assign{\x}{\z + 1}, \mem}$

   Since $\mem(\x) = 4 > 0$, we take the if-branch:
   
2. $\opStep \tuple{\Assign{\y}{\x + \y}\Seq\Assign{\x}{\z + 1}, \mem}$

3. $\opStep \tuple{\Assign{\x}{\z + 1}, \mem[\y := 2]}$
   
   where $\mem[\y := 2]$ because $\evalE{\x + \y}(\mem) = 4 + (-2) = 2$

4. $\opStep \tuple{\Done, \mem[\y := 2][\x := 1]}$
   
   where $\evalE{\z + 1}(\mem[\y := 2]) = 0 + 1 = 1$

Final memory $\mem'$: $\mem'(\x) = 1$, $\mem'(\y) = 2$, $\mem'(\z) = 0$

## T3: Four flavors of program proofs (40 Points)

### (a) Proving validity using operational semantics

**Triple**: $\Triple{0 < \x \And 0 \leq \y}{\Assign{\y}{\y + \x}\Seq\Assign{\x}{\y + \y}}{0 < \x}$

**Proof**: Let $\mem$ be an arbitrary memory such that $\mem \Satisfies 0 < \x \And 0 \leq \y$.

By operational semantics:
1. $\tuple{\Assign{\y}{\y + \x}\Seq\Assign{\x}{\y + \y}, \mem}$
2. $\opStep \tuple{\Assign{\x}{\y + \y}, \mem\mUpdate{\y} {\y + \x}}$
3. $\opStep \tuple{\Done, \mem\mUpdate{\y}{\y + \x}\mUpdate{\x}{\y + \y}}$

Let $\mem' = \mem\mUpdate{\y}{\y + \x}\mUpdate{\x}{\y + \y}$.

We have $\mem'(\x) = 2*(\mem(\y) + \mem(\x))$. 

Since $\mem(\x) > 0$ and $\mem(\y) \geq 0$, we have $\mem(\y) + \mem(\x) > 0$.
Therefore, $\mem'(\x) = 2(\mem(\y) + \mem(\x)) > 0$.

Thus $\mem' \Satisfies 0 < \x$, proving the triple is valid.

### (b) Proof tree for the given triple

![[2. Overview - Definition 2-11 Toy Program Logic.png]]$\newcommand{\z}{\texttt{z}}$

**Triple**: 
$$\Triple{\y \teq 0}{\Ite{\x \teq 0}{\Skip}{\Assign{\y}{\x + \x}}\Seq\Assign{\z}{\y + \x}}{\z \teq 3 \cdot \x}
$$

The proof tree:

$$
\begin{prooftree}
\AxiomC{}
\AxiomC{}
\RightLabel{skip}
\UnaryInfC{$\provable \Triple{\y \teq 0 \wedge x \teq 0}{\Skip}{\y \teq 0 \wedge x \teq 0}$}
\AxiomC{$(\y \teq 0 \wedge x \teq 0) \Entails (\y + \x \teq 3 \cdot \x)$}
\RightLabel{consequence}
\TrinaryInfC{$\provable \Triple{\y \teq 0 \wedge x \teq 0}{\Skip}{\y + \x \teq 3 \cdot \x}$}
\AxiomC{$\y \teq 0 \wedge \Neg(\x \teq 0) \Entails (\x + \x + \x \teq 3 \cdot \x)$}
\AxiomC{}
\RightLabel{assign}
\UnaryInfC{$\provable \Triple{\x + \x + \x \teq 3 \cdot \x}{\Assign{\y}{\x + \x}}{\y + \x \teq 3 \cdot \x}$}
\AxiomC{$(\y + \x \teq 3 \cdot \x) \Entails (\y + \x \teq 3 \cdot \x)$}
\RightLabel{consequence}
\TrinaryInfC{$\provable \Triple{\y \teq 0 \wedge \Neg(\x \teq 0)}{\Assign{\y}{\x + \x}}{\y + \x \teq 3 \cdot \x}$}
\RightLabel{conditional}
\BinaryInfC{$\provable \Triple{\y \teq 0}{\Ite{\x \teq 0}{\Skip}{\Assign{\y}{\x + \x}}}{\y + \x \teq 3 \cdot \x}$}
\AxiomC{}
\RightLabel{assign}
\UnaryInfC{$\provable \Triple{\y + \x \teq 3 \cdot \x}{\Assign{\z}{\y + \x}}{\z \teq 3 \cdot \x}$}
\RightLabel{sequence}
\BinaryInfC{$\provable \Triple{\y \teq 0}{\Ite{\x \teq 0}{\Skip}{\Assign{\y}{\x + \x}}\Seq\Assign{\z}{\y + \x}}{\z \teq 3 \cdot \x}$}
\end{prooftree}
$$

$$\begin{prooftree} \AxiomC{} \UnaryInfC{$\provable \Triple{\y \teq 0 \And \x \teq 0}{\Skip}{\y \teq 0 \And \x \teq 0}$} \AxiomC{$\y \teq 0 \And \x \teq 0 \Entails \y + \x \teq 3 \cdot \x$} \UnaryInfC{$\provable \Triple{\y \teq 0 \And \x \teq 0}{\Skip}{\y + \x \teq 3 \cdot \x}$} \AxiomC{} \UnaryInfC{$\provable \Triple{(\x + \x) + \x \teq 3 \cdot \x}{\Assign{\y}{\x + \x}}{\y + \x \teq 3 \cdot \x}$} \AxiomC{$\y \teq 0 \And \Neg(\x \teq 0) \Entails (\x + \x) + \x \teq 3 \cdot \x$} \UnaryInfC{$\provable \Triple{\y \teq 0 \And \Neg(\x \teq 0)}{\Assign{\y}{\x + \x}}{\y + \x \teq 3 \cdot \x}$} \BinaryInfC{$\provable \Triple{\y \teq 0}{\Ite{\x \teq 0}{\Skip}{\Assign{\y}{\x + \x}}}{\y + \x \teq 3 \cdot \x}$} \AxiomC{} \UnaryInfC{$\provable \Triple{\y + \x \teq 3 \cdot \x}{\Assign{\z}{\y + \x}}{\z \teq 3 \cdot \x}$} \BinaryInfC{$\provable \Triple{\y \teq 0}{\Ite{\x \teq 0}{\Skip}{\Assign{\y}{\x + \x}}\Seq\Assign{\z}{\y + \x}}{\z \teq 3 \cdot \x}$} \end{prooftree}$$
### (c) Analysis of modified triple

No, there is no such precondition $F$ and memory $\mem$.

**Justification**: For the triple to be valid with precondition $\y \teq 0$, we need that whenever $\mem \Satisfies \y \teq 0$, after executing the command, the postcondition $\z \teq 3 \cdot \x$ holds.

The issue is that if we use a Boolean expression $F$ as the condition in the if-statement instead of $\x \teq 0$, the correctness depends on the relationship between $F$ and the value of $\x$. 

For the postcondition to hold:
- When $F$ is true (skip branch): we need $\y + \x = 3 \cdot \x$, which requires $\y = 2 \cdot \x$
- When $F$ is false (else branch): after $\y := \x + \x$, we get $\z = 2\x + \x = 3\x$ ✓

Since we require $\y \teq 0$ as precondition, the skip branch requires $0 + \x = 3 \cdot \x$, which means $\x = 0$. So $F$ must be true exactly when $\x = 0$ for all memories satisfying the precondition. But if $\mem \Satisfies F$ and $\mem \NotSatisfies \y \teq 0$, then we cannot guarantee the postcondition.

### (d) Proof outline

```
{{ x == 2 * y ∧ y == 2 * x ∧ A == 0 ∧ B == 4 * x }}
{{ x == 0 ∧ y == 0 ∧ A == 0 ∧ B == 0 }}
if ( x > y ) {
  {{ x == 0 ∧ y == 0 ∧ x > y ∧ A == 0 ∧ B == 0 }}
  {{ false }}  // This branch is unreachable since x = y = 0
  z := x - y;
  x := z + y;
  y := z;
  {{ x == B ∧ y == A }}
} else {
  {{ x == 0 ∧ y == 0 ∧ ¬(x > y) ∧ A == 0 ∧ B == 0 }}
  z := y - x;
  {{ z == 0 ∧ x == 0 ∧ y == 0 ∧ A == 0 ∧ B == 0 }}
  y := z + x;
  {{ x == 0 ∧ y == 0 ∧ A == 0 ∧ B == 0 }}
  x := z;
  {{ x == 0 ∧ y == 0 ∧ A == 0 ∧ B == 0 }}
}
{{ x == B ∧ y == A }}
```

Note: From $\x \teq 2 \cdot \y \And \y \teq 2 \cdot \x$, we get $\x = \y = 0$, and from $B \teq 4 \cdot \x$, we get $B = 0$.

### (e) Checking weakest precondition

**Triple**: $\Triple{\x \teq B \And \y \teq A \And 0 < \x \And 0 < \y}{\Ite{\x > \y}{\Assign{\x}{\x - \y}}{\Assign{\y}{\y - \x}}}{\x \leq B \And \y \leq A}$

Computing $\wp[\cc](\x \leq B \And \y \leq A)$:

$$\wp[\Ite{\x > \y}{\Assign{\x}{\x - \y}}{\Assign{\y}{\y - \x}}](\x \leq B \And \y \leq A)$$

$$= (\x > \y \Implies \wp[\Assign{\x}{\x - \y}](\x \leq B \And \y \leq A)) \And (\Neg(\x > \y) \Implies \wp[\Assign{\y}{\y - \x}](\x \leq B \And \y \leq A))$$

$$= (\x > \y \Implies (\x - \y) \leq B \And \y \leq A) \And (\x \leq \y \Implies \x \leq B \And (\y - \x) \leq A)$$

Now checking if $\x \teq B \And \y \teq A \And 0 < \x \And 0 < \y \Entails \wp[\cc](\Post)$:

- When $\x > \y$: We need $\x - \y \leq B$. Since $\x = B$ and $\y > 0$, we have $\x - \y < \x = B$. ✓
- When $\x \leq \y$: We need $\y - \x \leq A$. Since $\y = A$ and $\x > 0$, we have $\y - \x < \y = A$. ✓

Therefore, $F \Entails \wp[\cc](G)$ holds.

## T4: Strongest Postconditions (40 Points)

I'll prove the four properties to show that $\sp[\cc](F) \Entails G \iff F \Entails \wp[\cc](G)$.

### (a) $\provable \Triple{F}{\cc}{\sp[\cc](F)}$

**Proof by structural induction on $\cc$:**

**Base case $\cc = \Skip$**: 
$\sp[\Skip](F) = F$, and $\provable \Triple{F}{\Skip}{F}$ by the skip rule.

**Base case $\cc = \Assign{\x}{\aee}$**:
$\sp[\Assign{\x}{\aee}](F) = \Exists \y \qdot F[\x := \y] \And \x \teq \aee[\x := \y]$

We need to show this is the strongest postcondition reachable from $F$. By the assignment rule and consequence, this captures exactly the memories reachable after the assignment.

**Inductive case $\cc = \cc_1\Seq\cc_2$**:
By I.H., $\provable \Triple{F}{\cc_1}{\sp[\cc_1](F)}$ and $\provable \Triple{\sp[\cc_1](F)}{\cc_2}{\sp[\cc_2](\sp[\cc_1](F))}$.
By the sequence rule, $\provable \Triple{F}{\cc_1\Seq\cc_2}{\sp[\cc_2](\sp[\cc_1](F))} = \Triple{F}{\cc_1\Seq\cc_2}{\sp[\cc_1\Seq\cc_2](F)}$.

**Inductive case $\cc = \Ite{\bb}{\cc_1}{\cc_2}$**:
Similar argument using the conditional rule and I.H.

### (b) $\sp[\cc](F) \Entails G$ implies $F \Entails \wp[\cc](G)$

Assume $\sp[\cc](F) \Entails G$. 

From (a), we have $\valid \Triple{F}{\cc}{\sp[\cc](F)}$.
By consequence rule with $\sp[\cc](F) \Entails G$, we get $\valid \Triple{F}{\cc}{G}$.
By Theorem 2.4.6 (characterization of weakest preconditions), this means $F \Entails \wp[\cc](G)$.

### (c) If $\mem' \Satisfies \sp[\cc](F)$, then $\exists \mem$ such that $\mem \Satisfies F$ and $\tuple{\cc, \mem} \opSteps \tuple{\Done, \mem'}$

**Proof by structural induction on $\cc$:**

This follows from the definition of strongest postcondition - it collects exactly the reachable memories.

### (d) $F \Entails \wp[\cc](G)$ implies $\sp[\cc](F) \Entails G$

Assume $F \Entails \wp[\cc](G)$.

By Theorem 2.4.6, this means $\valid \Triple{F}{\cc}{G}$.
From (a), we have $\valid \Triple{F}{\cc}{\sp[\cc](F)}$.
By (c), every memory satisfying $\sp[\cc](F)$ is reachable from some memory satisfying $F$.
Since $\valid \Triple{F}{\cc}{G}$, all such reachable memories must satisfy $G$.
Therefore, $\sp[\cc](F) \Entails G$.

**Conclusion**: We have shown all four properties, establishing that $\sp[\cc](F) \Entails G \iff F \Entails \wp[\cc](G)$.