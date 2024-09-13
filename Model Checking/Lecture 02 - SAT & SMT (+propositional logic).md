---
tags:
  - ModelChecking
---
Party problem
1. + 2. $Me \leftrightarrow Je \land Mo \leftrightarrow Ra$
3. $Je \rightarrow Ra$
4. $\lnot (Mo \land Ha)$
5. $Le \land Pi$

# DPLL

CNF -> SAT | UNSAT

![[dpll-intro.png]]
![[dpll-fyi.png]]

| 1,1 | 1,2 | 1,3 | 1,4 |
| --- | --- | --- | --- |
| 2,1 | 2,2 | 2,3 | 2,4 |
| 3,1 | 3,2 | 3,3 | 3,4 |
| 4,1 | 4,2 | 4,3 | 4,4 |
## Satellite problem
- diagonals:
$$
\bigwedge_{0<i<i'\leq4}\biggl( \bigwedge_{j,j':i+j=i'+j'} \lnot(p_{ij} \land p_{i'j'}) \lor \bigwedge_{j,j':i-j=i'-j'}\lnot(p_{ij}\land p_{i'j'})\biggr)
$$

# 3 classical encodings

$k \in \mathbb{Z}$
## "At most k": $\sum^{n}_{i=1} x_i \leq k$

## "At least k": $\sum^{n}_{i=1} x _i \geq k$

## "Exactly k": $\sum^{n}_{i=1} x_i = k$
