
$$
% We extend the Hygge operational semantics with enhanced assertion handling:

\[

\begin{array}{c}

\inferrule*[right={[R-Assert-Eval]}]{

\hygSemanticConf{R}{e} \to \hygSemanticConf{R'}{e'}

}{

\hygSemanticConf{R}{\mathsf{assert}(e)} \;\to\; \hygSemanticConf{R'}{\mathsf{assert}(e')}

}

\\

\inferrule*[right={[R-Assert-True]}]{}{

\hygSemanticConf{R}{\mathsf{assert}(\mathsf{true})} \;\to\; \hygSemanticConf{R}{()}

}

\\

\inferrule*[right={[R-Assert-False]}]{

\mathsf{vars}(e) = \{x_1, \ldots, x_n\} \\

R(x_1) = v_1, \ldots, R(x_n) = v_n \\

\mathsf{src}(e) = s

}{

\hygSemanticConf{R}{\mathsf{assert}(\mathsf{false})} \;\to\; \hygSemanticConf{R}{\mathsf{printError}(s, x_1, v_1, \ldots, x_n, v_n); \mathsf{false}}

}

\end{array}

\]

  

Where:

\begin{itemize}

\item $\mathsf{vars}(e)$ denotes the set of free variables referenced in the key expression $e$

\item $\mathsf{src}(e)$ retrieves the source code snippet containing expression $e$

\item $\mathsf{printError}(s, x_1, v_1, \ldots, x_n, v_n)$ prints the error message with source snippet $s$ and the values of relevant variables

\end{itemize}

  

% We also extend the hygge0 operational semantics for enhanced printing of data structures:

\[

\begin{array}{c}

\inferrule*[right={[R-Print-Struct]}]{

v = \mathsf{struct} \{ f_1 = v_1, \ldots, f_n = v_n \}

}{

\hygSemanticConf{R}{\mathsf{print}(v)} \;\to\; \hygSemanticConf{R}{\mathsf{print}("struct \{ f_1 = "); \mathsf{print}(v_1); \ldots; \mathsf{print}(v_n); \mathsf{print}(" \}")}

}

\\

\inferrule*[right={[R-Print-Array]}]{

v = \mathsf{array}(l, \_)

}{

\hygSemanticConf{R}{\mathsf{print}(v)} \;\to\; \hygSemanticConf{R}{\mathsf{print}("Array\{ length: "); \mathsf{print}(l); \mathsf{print}(" \}")}

}

\end{array}

\]

  

% Additionally, to support the enhanced assertion mechanism, we define a substitution rule for assertions:

\[

\begin{array}{rcl}

\subst{\mathsf{assert}(e)}{x}{e'} & = & \mathsf{assert}(\subst{e}{x}{e'})

\end{array}

\]

  

% To complete our semantics for the extension, we include rules for the decoration of assertions:

\[

\begin{array}{c}

\inferrule*[right={[R-Decorate-Assert]}]{

\mathsf{keyExpr}(e) = e_k \\

\mathsf{vars}(e_k) = \{x_1, \ldots, x_n\}

}{

\mathsf{decorate}(\mathsf{assert}(e)) \;\to\; \mathsf{assert}(\mathsf{let}~r = e_k~\mathsf{in}~\mathsf{if}~r~\mathsf{then}~\mathsf{true}~\mathsf{else}~\mathsf{printVars}(x_1, \ldots, x_n);~r)

}

\end{array}

\]

  

Where $\mathsf{keyExpr}(e)$ identifies the key expression that determines the assertion result.
$$