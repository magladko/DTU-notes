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
