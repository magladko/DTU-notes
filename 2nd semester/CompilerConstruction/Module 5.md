## Exercise 24

Write the reductions of the following expression, in a runtime environment R. Show all reductions until the expression reduces into a value.

$$
\begin{split}
\begin{array}{l}
  \hygLetMutInit{x}{0} \\
  \hygLetMutInit{y}{0} \\
  \qquad\hygAssign{x}{\hygAssign{y}{1}}; \\
  \qquad x + y
\end{array}
\end{split}
$$