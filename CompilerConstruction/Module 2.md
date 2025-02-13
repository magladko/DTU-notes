
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

