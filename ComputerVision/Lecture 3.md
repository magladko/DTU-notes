**Essential matrix (E)** - world coords
$$
p_{2}^T E p_{1} = 0
$$

**Fundamental matrix (F)** - image coords

$$
q_{2}^T F q_{1} = 0
$$

$$
\begin{align}
p_{2}^T E p_{1} = 0\\
(K^{-1}q_{2})^T E (K^{-1}q_{1}) = 0 \\
q_{2}^T (K^{-1})^T E A^{-1} q_{1} = 0 \\
q_{2}^T F q_{1} = 0
\end{align}
$$

---
$$
\begin{bmatrix}
a_{1} \\
a_{2} \\
a_{3}
\end{bmatrix}
\times
\begin{bmatrix}
b_{1} \\
b_{2} \\
b_{3} \\
\end{bmatrix}
=
\begin{bmatrix}
a_{2}b_{3} - a_{3}b_{2} \\
a_{3}b_{1} - a_{1}b_{3} \\
a_{1}b_{2}-a_{2}b_{1}
\end{bmatrix}
=
\begin{bmatrix}
0 & -a_{3} & a_{2} \\
a_{3} & 0 & -a_{1} \\
-a_{2} & a_{1} & 0
\end{bmatrix}
\begin{bmatrix}
b_{1} \\
b_{2} \\
b_{3}
\end{bmatrix}
$$

