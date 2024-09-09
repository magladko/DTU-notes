# 2.1

Define a toy logical formula G that is equivalent to the informal constraint $z == 2∗min(x,y)$. That is, for every memory m, your formula G should satisfy the following:
$$
\begin{aligned}
m⊨G \text{ iff }m(z)=2∗min(m(x),m(y)),
\end{aligned}
$$
where min(i,j) denotes the minimum of the numbers i and j.

## Answer

$$
G \equiv ((x > y)\land(z == 2 * y))\lor(\lnot(x>y)\land (z == 2*x))
$$
or 
$$
G ≡ (x > y → z == 2*y) ∧ (\lnot(x > y) → z == 2*x)
$$

# 2.2

Compute all possible execution steps starting from the configuration $⟨C, m⟩$, where $C$ is the command below and m is the memory given by $m(x)=3$, $m(y)=7$, and $m(z)=0$.

```
if (x<y) {
	z := x
} else {
	z := y
}; 
z := z+z
```

What is the value of z after the execution has terminated?


| $x$ | $\mathfrak{m}(x)$ | $\mathfrak{m}[z \leftarrow 3](x)$ | $\mathfrak{m}[z \leftarrow 6](x)$ |
| --- | ----------------- | --------------------------------- | --------------------------------- |
| $x$ | 3                 | 3                                 | 3                                 |
| $y$ | 7                 | 7                                 | 7                                 |
| $z$ | 0                 | 3                                 | 6                                 |

$$
\begin{aligned}
& (\text{if } (x<y) \set{z:=x} \text{ else} \set{z:=y};z:=z+z,\mathfrak{m}) \\
\implies & (z:=x; z:=z+z, \mathfrak{m}) \\
\implies & (z:=z+z, \mathfrak{m}[z\leftarrow 3]) \\
\implies & (done, \mathfrak{m}[z\leftarrow 6])
\end{aligned}
$$
After terminated execution $z = 6$

# 2.3
We extend our toy programming language by a command `alert(x,a)`, which waits for a number of execution steps determined by $a$. After $a$ steps have been performed, the command should raises an alarm by setting the variable $x$ to $1$. If $a$ is initially negative, the behavior of `alert(x,a)` is undefined.

1. Formalize the operational semantics of `alert(x,a)` by providing inference rules similarly to the ones in [Fig. 2.1](https://pv24.cmath.eu/01-overview.html#fig-01-operational-semantics).

2. Change your semantics such that an error is raised if we attempt to run `alert(x,a)` and a evaluates to a negative number. You might want to add a new termination indicator, similarly to done.

3. Give a toy command $C$ that simulates `alert(x,a)`, i.e. if $[a](m)>0$, then executions of $⟨C, m⟩$ and $⟨alert(x,a), m⟩$ should end up with the same final memory.

