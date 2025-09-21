Best-case running time
$$
T_b^R(n) := \text{min}\{t | \mathbf{P}[T^R(\mathbf{X})=t]>0, ||X||=n\}
$$

Worst-case running time:
$$
T_w^R := \text{max}\{t | \mathbf{P}[T^R(\mathbf{X})=t]>0, ||X||=n\}
$$

Expected running time of randomized algorithm
$$
E[X] = \sum_{n=0}^\inf P[X = n] \cdot n 
$$
Geometric Series formula
$$
\sum_{n=0}^\inf n \cdot \left( \frac{1}{2} \right)^{n+1} = \frac{q}{(1-q)^2}
$$

![[class-p.png]]
![[class-np1.png]]
![[class-np2.png]]
![[class-rp.png]]
![[class-bpp.png]]
![[class-zpp.png]]
![[class-relations.png]]
Summary table

| Class           | True answer YES                         | True answer NO |
| --------------- | --------------------------------------- | -------------- |
| $\mathcal{NP}$  | $\boldsymbol{\mathit{P}}[\text{YES}]<3$ | $$             |
| $\mathcal{RP}$  | $$                                      | $$             |
| $\mathcal{BPP}$ | $$                                      | $$             |
| $\mathcal{ZPP}$ | $$                                      | $$             |
