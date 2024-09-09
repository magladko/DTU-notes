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

