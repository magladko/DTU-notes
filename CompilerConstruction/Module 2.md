## Language definition

$$
\begin{split}
\begin{array}{rrcll}
    \text{Expression} & e & ::=
             & \hygType{x}{t}{e} & \text{(Declare $x$ as an alias of type $t$ in scope $e$)}
    \\
    & & \mid & \hygLetU{x}{e_1}{e_2} & \text{(Declare $x$ as $e_1$ in scope $e_2$)}
    \\
    & & \mid & \hygLet{x}{t}{e_1}{e_2} & \text{(Declare $x$ of type $t$ as $e_1$ in scope $e_2$)}
    \\
    & & \mid & e_1;\; e_2 & \text{(Sequencing)}
    \\
    & & \mid & \{\,e\,\} & \text{(Expression in curly brackets)}
    \\
    & & \mid & \hygCond{e_1}{e_2}{e_3} & \text{(Conditional)}
    \\
    & & \mid & \hygOr{e_1}{e_2} & \text{(Logical "or")}
    \\
    & & \mid & \hygAnd{e_1}{e_2} & \text{(Logical "and")}
    \\
    & & \mid & e_1 = e_2 & \text{(Relation: equality)}
    \\
    & & \mid & e_1 < e_2 & \text{(Relation: less than)}
    \\
    & & \mid & e_1 + e_2 & \text{(Addition)}
    \\
    & & \mid & e_1 * e_2 & \text{(Multiplication)}
    \\
    & & \mid & \mathop{\hygNot{e}} & \text{(Logical negation)}
    \\
    & & \mid & \hygReadInt & \text{(Read integer from console)}
    \\
    & & \mid & \hygReadFloat & \text{(Read float from console)}
    \\
    & & \mid & \hygPrint{e} & \text{(Print on console)}
    \\
    & & \mid & \hygPrintln{e} & \text{(Print on console with newline)}
    \\
    & & \mid & \hygAssert{e} & \text{(Assertion)}
    \\
    & & \mid & e : t & \text{(Type ascription)}
    \\
    & & \mid & (\,e\,) & \text{(Expression in parentheses)}
    \\
    & & \mid & x & \text{(Variable)}
    \\
    & & \mid & v & \text{(Value)}
    \\[5mm]
    \text{Value} & v & ::= & 1 \mid 2 \mid 3 \mid \ldots & \text{(Integers)}
    \\
    & & \mid & \text{true} \mid \text{false} & \text{(Booleans)}
    \\
    & & \mid & \text{"Hello"} \mid \text{"Hej"} \mid \ldots & \text{(Strings)}
    \\
    & & \mid & 3.14\text{f} \mid 42.0\text{f} \mid \ldots & \text{(Single-precision float values)}
    \\
    & & \mid & () & \text{(Unit value)}
    \\[5mm]
    \text{Variable} & x & ::= & \text{z} \mid \text{foo} \mid \text{a123} \mid \ldots & \text{(Any non-reserved identifier)}
    \\[5mm]
    \text{Pretype} & t & ::= & \text{int} \mid \text{string} \mid \text{unit} \mid \text{foo} \mid \ldots & \text{(Any non-reserved identifier)}
\end{array}
\end{split}
$$

## Structural Operational Semantics of Hygge0

$$
\begin{split}
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-L}{$\hygEvalConf{R}{e + e_2} \;\to\; \hygEvalConf{R'}{e' + e_2}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-R}{$\hygEvalConf{R}{v + e} \;\to\; \hygEvalConf{R'}{v + e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 + v_2 = v_3$}
    \UnaryInfCLab{R-Add-Res}{$\hygEvalConf{R}{v_1 + v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-L}{$\hygEvalConf{R}{e * e_2} \;\to\; \hygEvalConf{R'}{e' * e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-R}{$\hygEvalConf{R}{v * e} \;\to\; \hygEvalConf{R'}{v * e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 \times v_2 = v_3$}
    \UnaryInfCLab{R-Mul-Res}{$\hygEvalConf{R}{v_1 * v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
  \\[2mm]
  \vdots
  \\[2mm]
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Par-Eval}{$\hygEvalConf{R}{(e)} \;\to\; \hygEvalConf{R'}{(e')}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Par-Res}{$\hygEvalConf{R}{(v)} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Curly-Eval}{$\hygEvalConf{R}{\{e\}} \;\to\; \hygEvalConf{R'}{\{e'\}}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Curly-Res}{$\hygEvalConf{R}{\{v\}} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Seq-Eval}{$\hygEvalConf{R}{e;\,e_2} \;\to\; \hygEvalConf{R'}{e';\,e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Seq-Res}{$\hygEvalConf{R}{v;\,e} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Let-Eval-Init}{$\hygEvalConf{R}{\hygLetU{x}{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygLetU{x}{e'}{e_2}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Let-Subst}{$\hygEvalConf{R}{\hygLetU{x}{v}{e}} \;\to\; \hygEvalConf{R}{\subst{e}{x}{v}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Type-Res}{$\hygEvalConf{R}{\hygType{x}{t}{e}} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Ascr-Res}{$\hygEvalConf{R}{e:t} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Assert-Eval-Arg}{$\hygEvalConf{R}{\hygAssert{e}} \;\to\; \hygEvalConf{R'}{\hygAssert{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Assert-Res}{$\hygEvalConf{R}{\hygAssert{\text{true}}} \;\to\; \hygEvalConf{R}{()}$}
  \end{prooftree}
  \\[2mm]
  \vdots
  \\[2mm]
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Print-Eval-Arg}{$\hygEvalConf{R}{\hygPrint{e}} \;\to\; \hygEvalConf{R'}{\hygPrint{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\envField{R}{Printer}$ is defined}
    \UnaryInfCLab{R-Print-Res}{$\hygEvalConf{R}{\hygPrint{v}} \;\to\; \hygEvalConf{R}{()}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\envField{R}{Reader}$ is defined}
    \AxiomC{$\envField{R}{Reader}$ yields $v$}
    \BinaryInfCLab{R-Read-Int}{$\hygEvalConf{R}{\hygReadInt} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\envField{R}{Reader}$ is defined}
    \AxiomC{$\envField{R}{Reader}$ yields $v$}
    \BinaryInfCLab{R-Read-Float}{$\hygEvalConf{R}{\hygReadFloat} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
\end{array}
\end{split}
$$

## exercise 10

```hygge0
let x = {
	let y if (2 < 42) then 0 else 42;
	y + 1
};
println
```

![[CC_exercise10.excalidraw]]
## exercise 11
$2*3 < 2+5$ - possible ambiguities
1. $(2*3)<(2+5)$
2. $2*(3<(2+5))$
3. $((2*3)<2)+5$

## exercise 12
### Substitution of a Variable in an Hygge0 Expression
$$
\begin{split}
\begin{array}{rcl}
  \subst{x}{x}{e'} & = & e'
  \\
  \subst{y}{x}{e'} & = & y \quad \text{(when $y \neq x$)}
  \\
  \subst{v}{x}{e'} & = & v
  \\
  \subst{(\,e\,)}{x}{e'} & = & (\,\subst{e}{x}{e'}\,)
  \\
  \subst{e : t}{x}{e'} & = & (\subst{e}{x}{e'}) : t
  \\
  \subst{\hygAssert{e}}{x}{e'} & = & \hygAssert{\subst{e}{x}{e'}}
  \\
  \subst{\hygPrintln{e}}{x}{e'} & = & \hygPrintln{\subst{e}{x}{e'}}
  \\
  \subst{\hygPrint{e}}{x}{e'} & = & \hygPrint{\subst{e}{x}{e'}}
  \\
  \subst{\hygReadFloat}{x}{e'} & = & \hygReadFloat
  \\
  \subst{\hygReadInt}{x}{e'} & = & \hygReadInt
  \\
  \subst{\mathop{\hygNot{e}}}{x}{e'} & = & \mathop{\hygNot{(\subst{e}{x}{e'})}}
  \\
  \subst{(e_1 + e_2)}{x}{e'} & = & \subst{e_1}{x}{e'} + \subst{e_2}{x}{e'}
  \\
  \subst{(e_1 * e_2)}{x}{e'} & = & \subst{e_1}{x}{e'} * \subst{e_2}{x}{e'}
  \\
  \subst{(e_1 < e_2)}{x}{e'} & = & \subst{e_1}{x}{e'} < \subst{e_2}{x}{e'}
  \\
  \subst{(e_1 = e_2)}{x}{e'} & = & \subst{e_1}{x}{e'} = \subst{e_2}{x}{e'}
  \\
  \subst{\hygAnd{e_1}{e_2}}{x}{e'} & = & \hygAnd{\subst{e_1}{x}{e'}}{\subst{e_2}{x}{e'}}
  \\
  \subst{\hygOr{e_1}{e_2}}{x}{e'} & = & \hygOr{\subst{e_1}{x}{e'}}{\subst{e_2}{x}{e'}}
  \\
  \subst{(\hygCond{e_1}{e_2}{e_3})}{x}{e'} & = & \hygCond{\subst{e_1}{x}{e'}}{\subst{e_2}{x}{e'}}{\subst{e_3}{x}{e'}}
  \\
  \subst{\{\,e\,\}}{x}{e'} & = & \{\,\subst{e}{x}{e'}\,\}
  \\
  \subst{(e_1;\; e_2)}{x}{e'} & = & \subst{e_{1}}{x}{e'};\;\subst{e_{2}}{x}{e'}
  \\
  \subst{(\hygLet{x}{t}{e_1}{e_2})}{x}{e'} & = & \hygLet{x}{t}{\subst{e_1}{x}{e'}}{e_2}
  \\
  \subst{(\hygLetU{x}{e_1}{e_2})}{x}{e'} & = & \hygLetU{x}{\subst{e_1}{x}{e'}}{e_2}
  \\
  \subst{(\hygLetU{y}{e_1}{e_2})}{x}{e'} & = & \hygLetU{y}{\subst{e_1}{x}{e'}}{\subst{e_2}{x}{e'}} \quad \text{(when $y \neq x$)}
  \\
  \subst{(\hygType{y}{t}{e})}{x}{e'} & = & \hygType{y}{t}{\subst{e}{x}{e'}}
\end{array}
\end{split}
$$
## exercise 13

$$
\newcommand{\hygStrucRed}[4]{
\begin{prooftree}
  \AxiomC{#1}
  \UnaryInfCLab{#2}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        #3
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        #4
      \end{array}
    }}
  $}
\end{prooftree}
}
$$
- $\hygLetU{x}{3 + 2}{\;x + 1}$

$$
\begin{prooftree}
  \AxiomC{}
  \UnaryInfCLab{R-Let-Eval-Init}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygLetUInit{x}{3 + 2} \\
        x + 1
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygLetUInit{x}{5} \\
        x + 1
      \end{array}
    }}
  $}
\end{prooftree}
$$
$$
\begin{prooftree}
  \AxiomC{}
  \UnaryInfCLab{R-Let-Eval-Subst}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygLetUInit{x}{5} \\
        x + 1
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        5 + 1
      \end{array}
    }}
  $}
\end{prooftree}
$$
$$
\begin{prooftree}
  \AxiomC{5 + 1 = 6}
  \UnaryInfCLab{R-Add-Res}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        5 + 1
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        6
      \end{array}
    }}
  $}
\end{prooftree}
$$

- $\hygLetU{x}{3 + 2}{\;\hygPrint{x + 1}}$
$$
\begin{prooftree}
  \AxiomC{}
  \UnaryInfCLab{R-Let-Eval-Init}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygLetUInit{x}{3 + 2} \\
        \hygPrint{x+1}
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygLetUInit{x}{5} \\
        \hygPrint{x+1}
      \end{array}
    }}
  $}
\end{prooftree}
$$
$$
\begin{prooftree}
  \AxiomC{}
  \UnaryInfCLab{R-Let-Eval-Subst}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygLetUInit{x}{5} \\
        \hygPrint{x+1}
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygPrint{5+1}
      \end{array}
    }}
  $}
\end{prooftree}
$$
$$
\begin{prooftree}
  \AxiomC{}
  \UnaryInfCLab{R-Print-Eval-Arg}{$
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygPrint{5+1}
      \end{array}
    }} \;\to\;
    \hygEvalConf{R}{\boxed{
      \begin{array}{l}
        \hygPrint{6}
      \end{array}
    }}
  $}
\end{prooftree}
$$
$$
\hygStrucRed{$\envField{R}{Printer}$ is defined}{R-Print-Res}{\hygPrint{6}}{\hygEvalConf{R}{()}}
$$

- $\hygLetU{x}{3 + 2}{\;\hygPrint{x + 1}; \;\hygPrint{x + 2}}$

$$
\hygStrucRed{}{R-Let-Eval-Init}{
  \hygLetUInit{x}{3+2} \\
  \hygPrint{x+1}; \\
  \hygPrint{x+2}
}{
  \hygLetUInit{x}{5} \\
  \hygPrint{x+1}; \\
  \hygPrint{x+2}
}
$$
$$
\hygStrucRed{}{R-Let-Subst}{
  \hygLetUInit{x}{5} \\
  \hygPrint{x+1}; \\
  \hygPrint{x+2}
}{
  \hygPrint{5+1}; \\
  \hygPrint{5+2}
}
$$
$$
\hygStrucRed{}{R-Print-Eval-Arg}{
  \hygPrint{5+1}; \\
  \hygPrint{5+2}
}{
  \hygPrint{6}; \\
  \hygPrint{5+2}
}
$$
$$
\hygStrucRed{$\envField{R}{Printer}$ is defined}{R-Print-Res}{
  \hygPrint{6}; \\
  \hygPrint{5+2}
}{
  \hygPrint{5+2}
}
$$
$$
\hygStrucRed{}{R-Print-Eval-Arg}{
  \hygPrint{5+2}
}{
  \hygPrint{7}
}
$$
$$
\hygStrucRed{$\envField{R}{Printer}$ is defined}{R-Print-Res}{
  \hygPrint{7}
}{
  ()
}
$$

## exercise 14
### Structural Operational Semantics of Hygge0
$$
%\begin{split}
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-L}{$\hygEvalConf{R}{e + e_2} \;\to\; \hygEvalConf{R'}{e' + e_2}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-R}{$\hygEvalConf{R}{v + e} \;\to\; \hygEvalConf{R'}{v + e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 + v_2 = v_3$}
    \UnaryInfCLab{R-Add-Res}{$\hygEvalConf{R}{v_1 + v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-L}{$\hygEvalConf{R}{e * e_2} \;\to\; \hygEvalConf{R'}{e' * e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-R}{$\hygEvalConf{R}{v * e} \;\to\; \hygEvalConf{R'}{v * e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 \times v_2 = v_3$}
    \UnaryInfCLab{R-Mul-Res}{$\hygEvalConf{R}{v_1 * v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% LESS THAN
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Lt-L}{$\hygEvalConf{R}{e < e_2} \;\to\; \hygEvalConf{R'}{e' < e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Lt-R}{$\hygEvalConf{R}{v < e} \;\to\; \hygEvalConf{R'}{v < e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 < v_2) = v_3$}
    \UnaryInfCLab{R-Lt-Res}{$\hygEvalConf{R}{v_1 < v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% EQ
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Eq-L}{$\hygEvalConf{R}{e = e_2} \;\to\; \hygEvalConf{R'}{e' = e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Eq-R}{$\hygEvalConf{R}{v = e} \;\to\; \hygEvalConf{R'}{v = e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 < v_2) = v_3$}
    \UnaryInfCLab{R-Eq-Res}{$\hygEvalConf{R}{v_1 = v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% if then else
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-If-Cond}{$\hygEvalConf{R}{\hygCond{e}{e_{2}}{e_{3}}} \;\to\; \hygEvalConf{R'}{\hygCond{e'}{e_{2}}{e_{3}}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v = \text{true} $}
    \UnaryInfCLab{R-If-Then}{$\hygEvalConf{R}{\hygCond{v}{e}{e_{2}}} \;\to\; \hygEvalConf{R'}{e}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v = \text{false} $}
    \UnaryInfCLab{R-If-Else}{$\hygEvalConf{R}{\hygCond{v}{e_{2}}{e}} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
\end{array}
$$

$$
%\begin{split}
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-L}{$\hygEvalConf{R}{e + e_2} \;\to\; \hygEvalConf{R'}{e' + e_2}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-R}{$\hygEvalConf{R}{v + e} \;\to\; \hygEvalConf{R'}{v + e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 + v_2 = v_3$}
    \UnaryInfCLab{R-Add-Res}{$\hygEvalConf{R}{v_1 + v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-L}{$\hygEvalConf{R}{e * e_2} \;\to\; \hygEvalConf{R'}{e' * e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-R}{$\hygEvalConf{R}{v * e} \;\to\; \hygEvalConf{R'}{v * e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 \times v_2 = v_3$}
    \UnaryInfCLab{R-Mul-Res}{$\hygEvalConf{R}{v_1 * v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% LESS THAN
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Lt-L}{$\hygEvalConf{R}{e < e_2} \;\to\; \hygEvalConf{R'}{e' < e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Lt-R}{$\hygEvalConf{R}{v < e} \;\to\; \hygEvalConf{R'}{v < e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 < v_2) = v_3$}
    \UnaryInfCLab{R-Lt-Res}{$\hygEvalConf{R}{v_1 < v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% EQ
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Eq-L}{$\hygEvalConf{R}{e = e_2} \;\to\; \hygEvalConf{R'}{e' = e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Eq-R}{$\hygEvalConf{R}{v = e} \;\to\; \hygEvalConf{R'}{v = e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 < v_2) = v_3$}
    \UnaryInfCLab{R-Eq-Res}{$\hygEvalConf{R}{v_1 = v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% let x : t = e_{1}; e_{2}
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Let-Eval-Init}{$\hygEvalConf{R}{\hygLet{x}{t}{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygLetU{x}{e'}{e_2}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Let-Subst}{$\hygEvalConf{R}{\hygLet{x}{t}{v}{e}} \;\to\; \hygEvalConf{R}{\subst{e}{x}{v}}$}
  \end{prooftree}
\end{array}
$$
$$
%% OR %%
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Or-L}{$\hygEvalConf{R}{\hygOr{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygOr{e'}{e_2}}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Or-R}{$\hygEvalConf{R}{\hygOr{v}{e}} \;\to\; \hygEvalConf{R'}{\hygOr{v}{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 \lor v_2) = v_3$}
    \UnaryInfCLab{R-Or-Res}{$\hygEvalConf{R}{\hygOr{v_1}{v_2}} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
%% AND %%
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-And-L}{$\hygEvalConf{R}{\hygAnd{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygAnd{e'}{e_2}}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-And-R}{$\hygEvalConf{R}{\hygAnd{v}{e}} \;\to\; \hygEvalConf{R'}{\hygAnd{v}{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 \lor v_2) = v_3$}
    \UnaryInfCLab{R-And-Res}{$\hygEvalConf{R}{\hygAnd{v_1}{v_2}} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$

$$
%\begin{split}
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-L}{$\hygEvalConf{R}{e + e_2} \;\to\; \hygEvalConf{R'}{e' + e_2}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Add-R}{$\hygEvalConf{R}{v + e} \;\to\; \hygEvalConf{R'}{v + e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 + v_2 = v_3$}
    \UnaryInfCLab{R-Add-Res}{$\hygEvalConf{R}{v_1 + v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-L}{$\hygEvalConf{R}{e * e_2} \;\to\; \hygEvalConf{R'}{e' * e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Mul-R}{$\hygEvalConf{R}{v * e} \;\to\; \hygEvalConf{R'}{v * e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v_1 \times v_2 = v_3$}
    \UnaryInfCLab{R-Mul-Res}{$\hygEvalConf{R}{v_1 * v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% LESS THAN
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Lt-L}{$\hygEvalConf{R}{e < e_2} \;\to\; \hygEvalConf{R'}{e' < e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Lt-R}{$\hygEvalConf{R}{v < e} \;\to\; \hygEvalConf{R'}{v < e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 < v_2) = v_3$}
    \UnaryInfCLab{R-Lt-Res}{$\hygEvalConf{R}{v_1 < v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% EQ
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Eq-L}{$\hygEvalConf{R}{e = e_2} \;\to\; \hygEvalConf{R'}{e' = e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Eq-R}{$\hygEvalConf{R}{v = e} \;\to\; \hygEvalConf{R'}{v = e'}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 < v_2) = v_3$}
    \UnaryInfCLab{R-Eq-Res}{$\hygEvalConf{R}{v_1 = v_2} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
% let x : t = e_{1}; e_{2}
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Let-Eval-Init}{$\hygEvalConf{R}{\hygLet{x}{t}{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygLetU{x}{e'}{e_2}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Let-Subst}{$\hygEvalConf{R}{\hygLet{x}{t}{v}{e}} \;\to\; \hygEvalConf{R}{\subst{e}{x}{v}}$}
  \end{prooftree}
\end{array}
$$
$$
%% OR %%
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Or-L}{$\hygEvalConf{R}{\hygOr{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygOr{e'}{e_2}}$}
  \end{prooftree}
  \;\;
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Or-R}{$\hygEvalConf{R}{\hygOr{v}{e}} \;\to\; \hygEvalConf{R'}{\hygOr{v}{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$(v_1 \lor v_2) = v_3$}
    \UnaryInfCLab{R-Or-Res}{$\hygEvalConf{R}{\hygOr{v_1}{v_2}} \;\to\; \hygEvalConf{R}{v_3}$}
  \end{prooftree}
\end{array}
$$
$$
%% NOT %%
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Not}{$\hygEvalConf{R}{\hygNot{e}} \;\to\; \hygEvalConf{R'}{\hygNot{e'}}$}
  \end{prooftree}
  \;\;
  \\\\
  \begin{prooftree}
    \AxiomC{$(\neg v_1) = v_2$}
    \UnaryInfCLab{R-And-Res}{$\hygEvalConf{R}{\hygNot{v_1}} \;\to\; \hygEvalConf{R}{v_2}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Par-Eval}{$\hygEvalConf{R}{(e)} \;\to\; \hygEvalConf{R'}{(e')}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Par-Res}{$\hygEvalConf{R}{(v)} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Curly-Eval}{$\hygEvalConf{R}{\{e\}} \;\to\; \hygEvalConf{R'}{\{e'\}}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Curly-Res}{$\hygEvalConf{R}{\{v\}} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Seq-Eval}{$\hygEvalConf{R}{e;\,e_2} \;\to\; \hygEvalConf{R'}{e';\,e_2}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Seq-Res}{$\hygEvalConf{R}{v;\,e} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Let-Eval-Init}{$\hygEvalConf{R}{\hygLetU{x}{e}{e_2}} \;\to\; \hygEvalConf{R'}{\hygLetU{x}{e'}{e_2}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Let-Subst}{$\hygEvalConf{R}{\hygLetU{x}{v}{e}} \;\to\; \hygEvalConf{R}{\subst{e}{x}{v}}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Type-Res}{$\hygEvalConf{R}{\hygType{x}{t}{e}} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Ascr-Res}{$\hygEvalConf{R}{e:t} \;\to\; \hygEvalConf{R}{e}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Assert-Eval-Arg}{$\hygEvalConf{R}{\hygAssert{e}} \;\to\; \hygEvalConf{R'}{\hygAssert{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{R-Assert-Res}{$\hygEvalConf{R}{\hygAssert{\text{true}}} \;\to\; \hygEvalConf{R}{()}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Print-Eval-Arg}{$\hygEvalConf{R}{\hygPrint{e}} \;\to\; \hygEvalConf{R'}{\hygPrint{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\envField{R}{Printer}$ is defined}
    \UnaryInfCLab{R-Print-Res}{$\hygEvalConf{R}{\hygPrint{v}} \;\to\; \hygEvalConf{R}{()}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygEvalConf{R}{e} \to \hygEvalConf{R'}{e'}$}
    \UnaryInfCLab{R-Println-Eval-Arg}{$\hygEvalConf{R}{\hygPrintln{e}} \;\to\; \hygEvalConf{R'}{\hygPrintln{e'}}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\envField{R}{Printer}$ is defined}
    \UnaryInfCLab{R-Println-Res}{$\hygEvalConf{R}{\hygPrintln{v}} \;\to\; \hygEvalConf{R}{()}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\envField{R}{Reader}$ is defined}
    \AxiomC{$\envField{R}{Reader}$ yields $v$}
    \BinaryInfCLab{R-Read-Int}{$\hygEvalConf{R}{\hygReadInt} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$\envField{R}{Reader}$ is defined}
    \AxiomC{$\envField{R}{Reader}$ yields $v$}
    \BinaryInfCLab{R-Read-Float}{$\hygEvalConf{R}{\hygReadFloat} \;\to\; \hygEvalConf{R}{v}$}
  \end{prooftree}
\end{array}
$$
TODO: What about $x$ and $v$?

$$
\hygStrucRed{}{R-If-Cond}{
  \hygCond{5+8 = 3}{\hygPrint{\text{"A"}}}{\hygPrintln{\text{"B"}}}
}{
  \hygCond{\text{false}}{\hygPrint{\text{"A"}}}{\hygPrintln{\text{"B"}}}
}
$$
$$
\hygStrucRed{}{R-If-Else}{
  \hygCond{5+8 = 3}{\hygPrint{\text{"A"}}}{\hygPrintln{\text{"B"}}}
}{
  \hygPrintln{\text{"B"}}
}
$$
$$
\hygStrucRed{$\envField{R}{Printer}$ is defined}{R-Println-Res}{
  \hygCond{5+8 = 3}{\hygPrint{\text{"A"}}}{\hygPrintln{\text{"B"}}}
}{
  ()
}
$$

## exercise 15

$$
\hygTypeCheckJ{
 \left\{\text{Vars} = \emptyset;\; \text{TypeVars} = \emptyset\right\}
\;}{\;(4 + 2) + 1\;}{\;\tInt}
$$

$$
\begin{split}
    \begin{array}{c}
      \begin{prooftree}
        \AxiomC{$
          \begin{prooftree}
            \AxiomC{$4 \text{ is an integer value}$}
            \UnaryInfCLab{T-Val-Int}{$
              \hygTypeCheckJ{
                \left\{
                  \begin{array}{@{}l@{}}
                    \text{Vars} = \emptyset \\
                    \text{TypeVars} = \emptyset
                  \end{array}
                \right\}
              }{4}{\tInt}
            $}
            \AxiomC{$2 \text{ is an integer value}$}
            \UnaryInfCLab{T-Val-Int}{$
              \hygTypeCheckJ{
                \left\{
                  \begin{array}{@{}l@{}}
                    \text{Vars} = \emptyset \\
                    \text{TypeVars} = \emptyset
                  \end{array}
                \right\}
              }{2}{\tInt}
            $}
            \BinaryInfCLab{T-Add}{$
            \hygTypeCheckJ{
              \left\{
                \begin{array}{@{}l@{}}
                  \text{Vars} = \emptyset \\
                  \text{TypeVars} = \emptyset
                \end{array}
              \right\}
            }{4+2}{\tInt}
            $}
          \end{prooftree}$}
        \UnaryInfCLab{T-Par}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{(4+2)}{\tInt}
        $}
        \AxiomC{$1 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{1}{\tInt}
        $}
        \BinaryInfCLab{T-Add}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          \;}{\;
            %\left(
              \boxed{
              \begin{array}{@{}l@{}}
                (4+2)+1
              \end{array}
              }
            %\right)
          \;}{\;\tInt}
        $}
      \end{prooftree}
    \end{array}
\end{split}
$$

$$
\hygTypeCheckJ{
 \left\{\text{Vars} = \emptyset;\; \text{TypeVars} = \emptyset\right\}
\;}{\;\hygCond{\hygTrue}{\hygStr{Hello}}{\hygStr{World}}\;}{\;\tString}
$$

$$
\begin{split}
    \begin{array}{c}
      \begin{prooftree}
        \AxiomC{$\text{true} \in \{ \text{true}, \text{false} \}$}
        \UnaryInfCLab{T-Val-Bool}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\text{true}}{\tBool}
        $}
        \AxiomC{$\text{"Hello" is a string value}$}
        \UnaryInfCLab{T-Val-String}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\text{"Hello"}}{\tString}
        $}
        \AxiomC{$\text{"World" is a string value}$}
        \UnaryInfCLab{T-Val-String}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\text{"World"}}{\tString}
        $}
        \TrinaryInfCLab{T-Cond}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          \;}{\;
            %\left(
              \boxed{
              \begin{array}{@{}l@{}}
                \hygCond{\text{true}}{\text{"Hello"}}{\text{"World"}}
              \end{array}
              }
            %\right)
          \;}{\;\tString}
        $}
      \end{prooftree}
    \end{array}
\end{split}
$$


$$
\hygTypeCheckJ{
 \left\{\text{Vars} = \{x \mapsto \tInt\};\; \text{TypeVars} = \emptyset\right\}
\;}{\;(x + 2) + 1\;}{\;\tInt}
$$
> [!note] skipped parenthesis in analysis for simplicity

$$
\begin{split}
    \begin{array}{c}
      \begin{prooftree}
        \AxiomC{$\envField{\Gamma}{Vars}(x) = T$}
        \UnaryInfCLab{T-Var}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{x}{\tInt}
        $}
        \AxiomC{$2 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{2}{\tInt}
        $}
        \BinaryInfCLab{T-Add}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{x+2}{\tInt}
        $}
        \AxiomC{$1 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{1}{\tInt}
        $}
        \BinaryInfCLab{T-Add}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          \;}{\;
            %\left(
              \boxed{
              \begin{array}{@{}l@{}}
                (x+2) + 1
              \end{array}
              }
            %\right)
          \;}{\;\tInt}
        $}
      \end{prooftree}
    \end{array}
\end{split}
$$

$$
\hygTypeCheckJ{
 \left\{\text{Vars} = \emptyset;\; \text{TypeVars} = \emptyset\right\}
\;}{\;\hygLet{x}{\tInt}{42}{\;(x + 2) + 1}\;}{\;\tInt}
$$

$$
\begin{split}
    \begin{array}{c}
      \begin{prooftree}
        \AxiomC{}
        \UnaryInfCLab{TRes-Int}{$
          \hygTypeResJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\text{"int"}}{\tInt}
        $}
        \AxiomC{$42 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{42}{\tInt}
        $}
        \AxiomC{$\dots$}
        \UnaryInfCLab{T-Add}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{(x+2)+1}{\tInt}
        $}
        \TrinaryInfCLab{T-Let-T}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          \;}{\;
            %\left(
              \boxed{
              \begin{array}{@{}l@{}}
                \hygLetInit{x}{\tInt}{42} \\
                (x+2)+1
              \end{array}
              }
            %\right)
          \;}{\;\tInt}
        $}
      \end{prooftree}
    \end{array}
\end{split}
$$

$$
\hygTypeCheckJ{
 \left\{\text{Vars} = \emptyset;\; \text{TypeVars} = \emptyset\right\}
\,}{\,\hygLet{x}{\tInt}{2 + 1}{\,\hygPrint{x + 2}};\, \hygStr{Bye!}\,}{\,\tString}
$$

$$
\begin{split}
    \begin{array}{c}
      \begin{prooftree}
        \AxiomC{}
        \UnaryInfCLab{TRes-Int}{$
          \hygTypeResJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\text{"int"}}{\tInt}
        $}
        \AxiomC{$2 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{2}{\tInt}
        $}
        \AxiomC{$1 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{1}{\tInt}
        $}
        \BinaryInfCLab{T-Add}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{2+1}{\tInt}
        $}
        \AxiomC{$\tInt \in \{ \tBool, \tInt, \tFloat, \tString \}$}
        \AxiomC{$\Gamma \vdash x : \tInt$}
        \UnaryInfCLab{T-Var}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{x}{\tInt}
        $}
        \AxiomC{$2 \text{ is an integer value}$}
        \UnaryInfCLab{T-Val-Int}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{2}{\tInt}
        $}
        \BinaryInfCLab{T-Add}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\;
              x+2
          }{\tInt}
        $}
        \BinaryInfCLab{T-Print}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\;
              \hygPrint{x+2}
          }{\tUnit}
        $}
        \AxiomC{"Bye!" is as string value}
        \UnaryInfCLab{T-Val-String}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\;
              \text{"Bye!"}
          }{\tString}
        $}
        \BinaryInfCLab{T-Seq}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \{ x \mapsto \tInt \} \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          }{\;
            \begin{array}{@{}l@{}}
              \hygPrint{x+2}; \\
              \text{"Bye!"}
            \end{array}
          }{\tString}
        $}
        \TrinaryInfCLab{T-Let-T}{$
          \hygTypeCheckJ{
            \left\{
              \begin{array}{@{}l@{}}
                \text{Vars} = \emptyset \\
                \text{TypeVars} = \emptyset
              \end{array}
            \right\}
          \;}{\;
            %\left(
              \boxed{
              \begin{array}{@{}l@{}}
                \hygLetInit{x}{\tInt}{2+1} \\
                \hygPrint{x+2};  \\
                \text{"Bye!"}
              \end{array}
              }
            %\right)
          \;}{\;\tString}
        $}
      \end{prooftree}
    \end{array}
\end{split}
$$


## exercise 16

$$
\begin{split}
\begin{array}{l}
  \hygLetUInit{x}{2} \\
  y + x * \text{"Hello"}
\end{array}
\end{split}
$$

Answer: **The multiplication operation only supports numbers - not strings (deduced from T-Add rule).**

## exercise 17

### Type System of Hygge0

$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$v$ is an integer value}
    \UnaryInfCLab{T-Val-Int}{$\Gamma \vdash v : \text{int}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{$v$ is a string value}
    \UnaryInfCLab{T-Val-String}{$\Gamma \vdash v : \text{string}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v \in \{\text{true}, \text{false}\}$}
    \UnaryInfCLab{T-Val-Bool}{$\Gamma \vdash v : \text{bool}$}
  \end{prooftree}
  \quad
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{T-Val-Unit}{$\Gamma \vdash () : \text{unit}$}
  \end{prooftree}
  \\\\
  \begin{prooftree}
    \AxiomC{$v$ is a single-precision float value}
    \UnaryInfCLab{T-Val-Float}{$\Gamma \vdash v : \text{float}$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\envField{\Gamma}{Vars}(x) = T$}
    \UnaryInfCLab{T-Var}{$\Gamma \vdash x : T$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$T \in \{\text{int}, \text{float}\}$}
    \AxiomC{$\Gamma \vdash e_1 : T$}
    \AxiomC{$\Gamma \vdash e_2 : T$}
    \TrinaryInfCLab{T-Add}{$\Gamma \vdash e_1 + e_2 : T$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$T \in \{\text{int}, \text{float}\}$}
    \AxiomC{$\Gamma \vdash e_1 : T$}
    \AxiomC{$\Gamma \vdash e_2 : T$}
    \TrinaryInfCLab{T-Mul}{$\Gamma \vdash e_1 * e_2 : T$}
  \end{prooftree}
\end{array}
$$
$$
\begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash e_1 : \text{bool}$}
    \AxiomC{$\Gamma \vdash e_2 : T$}
    \AxiomC{$\Gamma \vdash e_3 : T$}
    \TrinaryInfCLab{T-Cond}{$\Gamma \vdash \hygCond{e_1}{e_2}{e_3} : T$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash e_1 : T$}
    \AxiomC{$\Gamma \vdash e_2 : T'$}
    \BinaryInfCLab{T-Seq}{$\Gamma \vdash e_1; e_2 : T'$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash e_1 : T$}
    \AxiomC{$\left\{\Gamma \text{ with } \text{Vars} + (x \mapsto T)\right\} \vdash e_2 : T'$}
    \BinaryInfCLab{T-Let}{$\Gamma \vdash \hygLetU{x}{e_1}{e_2} : T'$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeResJ{\Gamma}{t}{T}$}
    \AxiomC{$\Gamma \vdash e_1 : T$}
    \AxiomC{$\left\{\Gamma \text{ with } \text{Vars} + (x \mapsto T)\right\} \vdash e_2 : T'$}
    \TrinaryInfCLab{T-Let-T}{$\Gamma \vdash \hygLet{x}{t}{e_1}{e_2} : T'$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$
      \begin{array}{c}
        x \not\in \{\text{bool}, \text{int}, \text{float}, \text{string}, \text{unit}\}
        \qquad
        x \not\in \envField{\Gamma}{TypeVars}
        \qquad
        \hygTypeResJ{\Gamma}{t}{T}
        \\
        \left\{\Gamma \text{ with } \text{TypeVars} + (x \mapsto T)\right\} \vdash e : T'
        \qquad
        x \not\in T'
      \end{array}
    $}
    \UnaryInfCLab{T-Type}{$\Gamma \vdash \hygType{x}{t}{e} : T'$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeResJ{\Gamma}{t}{T}$}
    \AxiomC{$\Gamma \vdash e : T$}
    \BinaryInfCLab{T-Ascr}{$\Gamma \vdash (e:t) : T$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash e : \text{bool}$}
    \UnaryInfCLab{T-Assert}{$\Gamma \vdash \hygAssert{e} : \text{unit}$}
  \end{prooftree}
\end{array} $$ $$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$T \in \{\text{bool}, \text{int}, \text{float}, \text{string}\}$}
    \AxiomC{$\Gamma \vdash e : T$}
    \BinaryInfCLab{T-Print}{$\Gamma \vdash \hygPrint{e} : \text{unit}$}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$T \in \{\text{bool}, \text{int}, \text{float}, \text{string}\}$}
    \AxiomC{$\Gamma \vdash e : T$}
    \BinaryInfCLab{T-Println}{$\Gamma \vdash \hygPrintln{e} : \text{unit}$}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash e : T$}
    \UnaryInfCLab{T-Par}{$
      \hygTypeCheckJ{\Gamma}{(e)}{T}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\Gamma \vdash e : T$}
    \UnaryInfCLab{T-Par}{$
      \hygTypeCheckJ{\Gamma}{\{ e \}}{T}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{T-ReadInt}{$
      \hygTypeCheckJ{\Gamma}{\hygReadInt}{\tInt}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{}
    \UnaryInfCLab{T-ReadFloat}{$
      \hygTypeCheckJ{\Gamma}{\hygReadFloat}{\tFloat}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e}{\tBool}$}
    \UnaryInfCLab{T-Not}{$
      \hygTypeCheckJ{\Gamma}{\text{not } e}{\tBool}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{1}}{\tBool}$}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{2}}{\tBool}$}
    \BinaryInfCLab{T-And}{$
      \hygTypeCheckJ{\Gamma}{\hygAnd{e_{1}}{e_{2}} }{\tBool}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{1}}{\tBool}$}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{2}}{\tBool}$}
    \BinaryInfCLab{T-Or}{$
      \hygTypeCheckJ{\Gamma}{\hygOr{e_{1}}{e_{2}} }{\tBool}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{1}}{T}$}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{2}}{T'}$}
    \AxiomC{$T=T'$}
    \TrinaryInfCLab{T-Or}{$
      \hygTypeCheckJ{\Gamma}{e_{1} < e_{2}}{\tBool}
    $}
  \end{prooftree}
\end{array}
$$
$$ \begin{array}{c}
  \begin{prooftree}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{1}}{T}$}
    \AxiomC{$\hygTypeCheckJ{\Gamma}{e_{2}}{T'}$}
    \AxiomC{$T=T'$}
    \TrinaryInfCLab{T-Eq}{$
      \hygTypeCheckJ{\Gamma}{e_{1} = e_{2}}{\tBool}
    $}
  \end{prooftree}
\end{array}
$$
## exercise 18
[Module 2: The Hygge0 Language Specification — 02247 Compiler Construction — Spring 2025](https://courses.compute.dtu.dk/02247/f25/hygge0-spec.html#hygge0-spec-exercise-34)


## free Vars definition
$$
\begin{split}
\begin{array}{rcl}
  \fv{x} & = & \{x\}
  \\
  \fv{v} & = & \emptyset \qquad \text{(when $v$ is not a lambda term)}
  \\
  \fv{\hygLambda{x_1: t_1, \ldots, x_n: t_n}{e}} & = & \fv{e} \setminus \{x_1, \ldots, x_n\}
  \\
  \fv{e_1 + e_2} & = & \fv{e_1} \cup \fv{e_2}
  \\
  \fv{e_1 * e_2} & = & \fv{e_1} \cup \fv{e_2}
  \\
  \fv{e_1;\, e_2} & = & \fv{e_1} \cup \fv{e_2}
  \\
  & \vdots &
  \\
  \fv{\hygStruct{f_1 {=} e_1; \ldots; f_n {=} e_n}} & = & \fv{e_1} \cup \ldots \cup \fv{e_n}
  \\
  \fv{\hygApp{e}{e_1, \ldots, e_n}} & = & \fv{e} \cup \fv{e_1} \cup \ldots \cup \fv{e_n}
  \\
  & \vdots &
  \\
  \fv{\hygLetU{x}{e_1}{e_2}} & = & \fv{e_1} \cup \left(\fv{e_2} \setminus \{x\}\right)
  \\
  \fv{\hygLet{x}{t}{e_1}{e_2}} & = & \fv{e_1} \cup \left(\fv{e_2} \setminus \{x\}\right)
  \\
  \fv{\hygLetMut{x}{e_1}{e_2}} & = & \fv{e_1} \cup \left(\fv{e_2} \setminus \{x\}\right)
  \\
  & \vdots &
  \\
  \fv{\hygType{x}{t}{e}} & = & \fv{e}
\end{array}
\end{split}
$$
