Poor man's analysis

## Levels of Syntax (7)

<svg viewBox="6.843 223.209 488.494 88.902" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <linearGradient gradientUnits="userSpaceOnUse" x1="254.646" y1="278.02" x2="254.646" y2="294.897" id="gradient-0" gradientTransform="matrix(0.003361, 1.338326, -12.026458, 0.054091, 3700.594971, -65.778923)">
      <stop offset="0" style="stop-color: rgb(84.706% 84.706% 84.706%)"></stop>
      <stop offset="1" style="stop-color: rgb(48.42% 48.42% 48.42%)"></stop>
    </linearGradient>
  </defs>
  <g transform="matrix(1, 0, 0, 1, 0, 0.846497)" class="fragment">
    <rect x="25.249" y="234.53" width="47.674" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre;" x="31.487" y="253.308">bits</text>
  </g>
  <g transform="matrix(1, 0, 0, 1, -137.945663, -82.323517)" class="fragment">
    <rect x="226.163" y="317.7" width="47.674" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre;" x="233.195" y="337.721">text</text>
  </g>
  <g transform="matrix(1, 0, 0, 1, 3.645673, 4.512505)" class="fragment">
    <rect x="147.54" y="230.864" width="62.68" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre;" x="153.674" y="250.885">tokens</text>
  </g>
  <g transform="matrix(1, 0, 0, 1, -3.349004, 5.823509)" class="fragment">
    <rect x="232.509" y="229.553" width="47.674" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre;" x="243.742" y="249.574">CST</text>
  </g>
  <g transform="matrix(1, 0, 0, 1, -1.829674, 0.5765)" class="fragment">
    <rect x="293.958" y="234.8" width="47.674" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre; transform-box: fill-box; transform-origin: 131.633% -103.302%;" x="306.233" y="281.672" transform="matrix(1, 0, 0, 1, -1.042415, -26.85125)">AST<tspan x="306.2330017089844" dy="1em">​</tspan></text>
  </g>
  <g transform="matrix(1, 0, 0, 1, 4.457662, 4.274498)" class="fragment">
    <rect x="350.639" y="231.102" width="36.082" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre; transform-origin: 393.459px 218.994px;" x="360.276" y="251.123">IR</text>
  </g>
  <g>
    <rect x="26.969" y="279.847" width="454.152" height="22.587" style="fill: url('#gradient-0');"></rect>
    <text style="fill: rgb(255, 255, 255); font-family: Monaco; font-size: 14px; white-space: pre;" x="31.923" y="296.605">Intention</text>
    <text style="fill: rgb(15, 15, 15); font-family: Monaco; font-size: 14px; text-anchor: end; white-space: pre;" x="476.309" y="296.435">Structure</text>
  </g>
  <g transform="matrix(1, 0, 0, 1, 0, 3.518494)" class="fragment">
    <rect x="406.473" y="231.858" width="76.04" height="29.247" style="fill: rgb(216, 216, 216); stroke: rgb(0, 0, 0);"></rect>
    <text style="fill: rgb(51, 51, 51); font-family: Monaco; font-size: 14px; white-space: pre; transform-origin: 444.07px 219.75px;" x="410.887" y="251.879">Bytecode</text>
  </g></svg>
CST: Concrete Syntax Tree -- collection of all tokens in the program
AST: Abstract Syntax Tree -- CST, but dropped unimportant information
IR: Intermedia Representation

### Useful information:
- **bits**: The encoding of the file.
- **text**: The number of characters or unknown tokens.
- **tokens**: The number of tokens.
- **CST**: Syntax level confusions, like the example above.
- **AST**: Dangerous code constructions, like `query("SELECT FROM db WHERE name=" + user_input)`
- **IR**: Uses of deprecated functions.
- **bytecode**: Detection of unoptimized code.

## Goal of Syntactic Analysis

- **Sound**: accepting only good programs (impossible)
- **Complete**: rejecting no good program

## Patterns

>[!Definition]
> A language $L$ over the alphabet $\Sigma$, is a subset of all words $w\in \Sigma*$ from the alphabet $\subseteq \Sigma^*$.

- **Decider**: Determine if a word is in a language or not (machine/Automaton)
- **Recognizer**: --||--  + is allowed to never give an answer (run forever)

> [!example] 
> Halting problem is recognizable, but not decidable.
> If a program terminates, we know it terminates. 
> If not, we need to wait and see if it does.

$$
L_{\text{halt}} = \{p~|~p~\text{terminates}, p \in L_{\text{Java}}\}
$$
> [!important] Sound vs Complete
> **Sound**: $\text{SA}_{\text{halt}}(p) \implies p \in L_{\text{halt}}$
> **Complete**: $p \in L_{\text{halt}} \implies \text{SA}_{\text{halt}}(p)$

> [!definition] Grammar
> A grammar G is a [quadruple](https://simple.wikipedia.org/wiki/Tuple_names) $(N,\Sigma,\to,S)$, where N is a set of non-terminals ($A, B, C$), $\Sigma$ is the alphabet, $\to$ is a set of production rules, and $S$ is the start symbol.
> The language of the grammar is:
> $$
> \text{LG}=\{w~|~w\in \Sigma^*,S\to^*w\}
> $$
> 
> Where $\to^*$ means applying the rules in $\to$ until no non-terminal is left.

<div class="note example"><h4 class="name">Generate <span><math display="inline" xmlns="http://www.w3.org/1998/Math/MathML"><mrow><mo stretchy="false" form="prefix">(</mo><mo stretchy="false" form="prefix">(</mo><mi>a</mi><mi>b</mi><mo stretchy="false" form="postfix">)</mo><mi>b</mi><mo stretchy="false" form="postfix">)</mo></mrow></math></span></h4><p>Consider the grammar <span><math display="inline" xmlns="http://www.w3.org/1998/Math/MathML"><mrow><mo stretchy="false" form="prefix">(</mo><mo stretchy="false" form="prefix">{</mo><mi>S</mi><mo>,</mo><mi>X</mi><mo stretchy="false" form="postfix">}</mo><mo>,</mo><mo stretchy="false" form="prefix">{</mo><mi>a</mi><mo>,</mo><mi>b</mi><mo>,</mo><mo stretchy="false" form="prefix">(</mo><mo>,</mo><mo stretchy="false" form="postfix">)</mo><mo stretchy="false" form="postfix">}</mo><mo>,</mo><mo>→</mo><mo>,</mo><mi>S</mi><mo stretchy="false" form="postfix">)</mo></mrow></math></span>, where <span><math display="inline" xmlns="http://www.w3.org/1998/Math/MathML"><mo>→</mo></math></span> is defined like this:</p> <div><math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>S</mi></mtd><mtd columnalign="left" style="padding-left: 0"><msup><mo>→</mo><mn>1</mn></msup><mo stretchy="false" form="prefix">(</mo><mi>S</mi><mi>X</mi><mo stretchy="false" form="postfix">)</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>S</mi></mtd><mtd columnalign="left" style="padding-left: 0"><msup><mo>→</mo><mn>2</mn></msup><mi>a</mi></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>X</mi></mtd><mtd columnalign="left" style="padding-left: 0"><msup><mo>→</mo><mn>3</mn></msup><mi>b</mi></mtd></mtr></mtable></math></div><div><p>It can generate the following word in the language <span><math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mrow><mi>S</mi><mrow class="fragment"><msup><mo>→</mo><mn>1</mn></msup><mo stretchy="false" form="prefix">(</mo><mi>S</mi><mi>X</mi><mo stretchy="false" form="postfix">)</mo></mrow><mrow class="fragment"><msup><mo>→</mo><mn>3</mn></msup><mo stretchy="false" form="prefix">(</mo><mi>S</mi><mi>b</mi><mo stretchy="false" form="postfix">)</mo></mrow><mrow class="fragment"><msup><mo>→</mo><mn>1</mn></msup><mo stretchy="false" form="prefix">(</mo><mo stretchy="false" form="prefix">(</mo><mi>S</mi><mi>X</mi><mo stretchy="false" form="postfix">)</mo><mi>b</mi><mo stretchy="false" form="postfix">)</mo></mrow><mrow class="fragment"><msup><mo>→</mo><mn>2</mn></msup><mo stretchy="false" form="prefix">(</mo><mo stretchy="false" form="prefix">(</mo><mi>a</mi><mi>X</mi><mo stretchy="false" form="postfix">)</mo><mi>b</mi><mo stretchy="false" form="postfix">)</mo></mrow><mrow class="fragment"><msup><mo>→</mo><mn>3</mn></msup><mo stretchy="false" form="prefix">(</mo><mo stretchy="false" form="prefix">(</mo><mi>a</mi><mi>b</mi><mo stretchy="false" form="postfix">)</mo><mi>b</mi><mo stretchy="false" form="postfix">)</mo></mrow></mrow></math></span></p></div></div>
## Language Types

![[Language Types.png]]

- **type 3**: can be defined as RegEx
- **type 2**: words defined by nesting (useful for e.g. nested parenthesis) -- recognizable by push down automaton
- **type 1**: recursion with context -- e.g. is a variable in scope
```C
int hello(int x) { 
  // Context { x , y }
  int y; 
  { 
    int z; 
    // Context { x , y, z} is z in scope? Yes
  }
  // Context { x , y} is z in scope? No
}
```
- **type 0**: a set of words which can be recognized by a Turing machine. One example is all programs that terminate.

### Pattern Matching in Practise
#### RegEx grammar (_Backus-Naur form_)

<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>e</mi><mspace width="0.222em"></mspace></mtd><mtd columnalign="left" style="padding-left: 0"><mo>:=</mo></mtd><mtd columnalign="right" style="padding-right: 0"><mi>ϵ</mi></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mtext mathvariant="normal">– an empty string </mtext><mspace width="0.333em"></mspace></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace></mtd><mtd columnalign="right" style="padding-right: 0"><mi>a</mi></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mtext mathvariant="normal">– symbol </mtext><mspace width="0.333em"></mspace></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace></mtd><mtd columnalign="right" style="padding-right: 0"><msub><mi>e</mi><mn>1</mn></msub><msub><mi>e</mi><mn>2</mn></msub></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mtext mathvariant="normal">– a concatenation </mtext><mspace width="0.333em"></mspace></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace></mtd><mtd columnalign="right" style="padding-right: 0"><msub><mi>e</mi><mn>1</mn></msub><mo>+</mo><msub><mi>e</mi><mn>2</mn></msub></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mtext mathvariant="normal">– an alternative </mtext><mspace width="0.333em"></mspace></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace></mtd><mtd columnalign="right" style="padding-right: 0"><msub><mi>e</mi><mn>1</mn></msub><mo>*</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mtext mathvariant="normal">– a Kleene star</mtext></mtd></mtr></mtable></math>
#### Denotational semantics

<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mi>ϵ</mi><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mo stretchy="false" form="prefix">{</mo><mi>ϵ</mi><mo stretchy="false" form="postfix">}</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mi>a</mi><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mo stretchy="false" form="prefix">{</mo><mi>a</mi><mo stretchy="false" form="postfix">}</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><msub><mi>e</mi><mn>1</mn></msub><msub><mi>e</mi><mn>2</mn></msub><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mo stretchy="false" form="prefix">{</mo><mi>u</mi><mi>w</mi><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace><mi>u</mi><mo>∈</mo><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mi>A</mi><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo><mo>,</mo><mi>w</mi><mo>∈</mo><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mi>B</mi><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">}</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><msub><mi>e</mi><mn>1</mn></msub><mo>+</mo><msub><mi>e</mi><mn>2</mn></msub><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mi>A</mi><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo><mo>∪</mo><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mi>B</mi><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mrow><msub><mi>e</mi><mn>1</mn></msub><mo>*</mo></mrow><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo></mtd><mtd columnalign="left" style="padding-left: 0"><msup><mo>=</mo><mo>†</mo></msup><mo stretchy="false" form="prefix">{</mo><mi>ϵ</mi><mo stretchy="false" form="postfix">}</mo><mo>∪</mo><mo stretchy="false" form="prefix">{</mo><mi>u</mi><mi>w</mi><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace><mi>u</mi><mo>∈</mo><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><msub><mi>e</mi><mn>1</mn></msub><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo><mo>,</mo><mi>w</mi><mo>∈</mo><mo stretchy="false" form="prefix">[</mo><mo stretchy="false" form="prefix">[</mo><mrow><msub><mi>e</mi><mn>1</mn></msub><mo>*</mo></mrow><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">]</mo><mo stretchy="false" form="postfix">}</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"></mtd></mtr></mtable></math>
where $\dagger$ is the smallest solution to the equation.


