$$
% Type-related commands
\newcommand{\hygTypeNoInit}[1]{\mathop{\text{type }} {#1} = \vphantom{x}}
\newcommand{\hygTypeInit}[2]{\mathop{\text{type }} {#1} = {#2};\;}
\newcommand{\hygType}[3]{\hygTypeInit{#1}{#2} {#3}}
\newcommand{\hygVar}[1]{\mathit{#1\,}}

% Let-related commands
\newcommand{\hygLetNoInit}[2]{\mathop{\text{let }} \mathit{#1}: {#2} = \vphantom{x}}
\newcommand{\hygLetInit}[3]{\hygLetNoInit{#1}{#2} {#3};\;}
\newcommand{\hygLet}[4]{\hygLetInit{#1}{#2}{#3} {#4}}
\newcommand{\hygLetUNoInit}[1]{\mathop{\text{let }} \mathit{#1} = \vphantom{x}}
\newcommand{\hygLetUInit}[2]{\hygLetUNoInit{#1} {#2};\;}
\newcommand{\hygLetU}[3]{\hygLetUInit{#1}{#2} {#3}}
\newcommand{\hygLetMutNoInit}[1]{\mathop{\text{let mutable }} {#1} = \vphantom{x}}
\newcommand{\hygLetMutInit}[2]{\hygLetMutNoInit{#1} {#2};\;}
\newcommand{\hygLetMut}[3]{\hygLetMutInit{#1}{#2} {#3}}
\newcommand{\hygLetRecNoInit}[2]{\mathop{\text{let rec }} {#1}: {#2} = \vphantom{x}}
\newcommand{\hygLetRecInit}[3]{\hygLetRecNoInit{#1}{#2} {#3};\;}
\newcommand{\hygLetRec}[4]{\hygLetRecInit{#1}{#2}{#3} {#4}}

% Control flow commands
\newcommand{\hygWhileNoBody}[1]{\text{while }{#1}\text{ do }}
\newcommand{\hygWhile}[2]{\hygWhileNoBody{#1}{#2}}
\newcommand{\hygDoWhileNoCond}[1]{\text{do }{#1}\text{ while }}
\newcommand{\hygDoWhile}[2]{\hygDoWhileNoCond{#1}{#2}}
\newcommand{\hygFor}[4]{\text{for }({#1}; {#2}; {#3})\; {#4}}

% Conditional commands
\newcommand{\hygCondNoThenElse}[1]{\mathop{\text{if }} {#1} \mathbin{\text{ then }} \vphantom{X}}
\newcommand{\hygElse}[1]{\text{else }{#1}}
\newcommand{\hygCond}[3]{\hygCondNoThenElse{#1} {#2} \mathbin{\text{ else }} {#3}}

% Assert and print commands
\newcommand{\hygAssert}[1]{\text{assert}({#1})}
\newcommand{\hygPrint}[1]{\text{print}({#1})}
\newcommand{\hygPrintln}[1]{\text{println}({#1})}
\newcommand{\hygReadInt}{\text{readInt}()}
\newcommand{\hygReadFloat}{\text{readFloat}()}

% Logical operators
\newcommand{\hygNot}[1]{\text{not }{#1}}
\newcommand{\hygAssign}[2]{{#1}\mathbin{\leftarrow}{#2}}
\newcommand{\hygTrue}{\text{true}}
\newcommand{\hygFalse}{\text{false}}
\newcommand{\hygStr}[1]{\text{"#1"}}
\newcommand{\hygOr}[2]{{#1} \mathbin{\text{or}} {#2}}
\newcommand{\hygAnd}[2]{{#1} \mathbin{\text{and}} {#2}}

% Function and lambda commands
\newcommand{\hygLambdaNoBody}[1]{\operatorname{\lambda}{\left({#1}\right)} \rightarrow \vphantom{X}}
\newcommand{\hygLambda}[2]{\hygLambdaNoBody{#1}{#2}}
\newcommand{\hygFunNoInit}[3]{\text{fun }\mathit{#1}\left({#2}\right): {#3} = \vphantom{X}}
\newcommand{\hygFunInit}[4]{\hygFunNoInit{#1}{#2}{#3} {#4};}
\newcommand{\hygFun}[5]{\hygFunInit{#1}{#2}{#3}{#4}\;{#5}}
\newcommand{\hygApp}[2]{{#1}\left({#2}\right)}
\newcommand{\hygRecFunNoInit}[3]{\text{rec fun }\mathit{#1}\left({#2}\right): {#3} = \vphantom{X}}
\newcommand{\hygRecFunInit}[4]{\hygRecFunNoInit{#1}{#2}{#3} {#4};}
\newcommand{\hygRecFun}[5]{\hygRecFunInit{#1}{#2}{#3}{#4}\;{#5}}

% Structure and union commands
\newcommand{\hygStructNoFields}{\text{struct }}
\newcommand{\hygStruct}[1]{\hygStructNoFields\left\{{#1}\right\}}
\newcommand{\hygField}[1]{\mathit{#1\,}}
\newcommand{\hygFieldSel}[2]{{#1}{.}\hygField{#2}}
\newcommand{\hygPtr}[1]{\mathsf{#1}}
\newcommand{\hygUnionInst}[2]{{#1}\left\{{#2}\right\}}

% Pattern matching commands
\newcommand{\hygMatchCase}[3]{{#1}\{{#2}\}\rightarrow{#3}}
\newcommand{\hygMatchNoCases}[1]{\text{match }{#1}\text{ with}}
\newcommand{\hygMatch}[2]{\hygMatchNoCases{#1}\;\left\{{#2}\right\}}

% Heap and evaluation commands
\newcommand{\hygHeapMax}[1]{\text{maxAddr}({#1})}
\newcommand{\hygEvalConf}[2]{\left\langle{#1}\bullet{#2}\right\rangle}
\newcommand{\subst}[3]{{#1}\left[{#2} \mapsto {#3}\right]}
\newcommand{\envField}[2]{{#1}{.}{\text{#2}}}

% Rule and inference commands
\newcommand{\ruleVertSep}{2mm}
\newcommand{\UnaryInfCLab}[2]{\RightLabel{[#1]}\UnaryInfC{#2}}
\newcommand{\BinaryInfCLab}[2]{\RightLabel{[#1]}\BinaryInfC{#2}}
\newcommand{\TrinaryInfCLab}[2]{\RightLabel{[#1]}\TrinaryInfC{#2}}
\newcommand{\QuaternaryInfCLab}[2]{\RightLabel{[#1]}\QuaternaryInfC{#2}}
\newcommand{\ruleFmt}[1]{\text{[#1]}}

% Type judgment commands
\newcommand{\hygTypeResJ}[3]{{#1} \vdash {#2} \triangleright {#3}}
\newcommand{\hygTypeCheckJ}[3]{{#1} \vdash {#2} : {#3}}
\newcommand{\hygSubtypingJ}[3]{{#1} \vdash {#2} \leqslant {#3}}
\newcommand{\hygSubtypingAJ}[4]{{#1},{#2} \vdash {#3} \leqslant {#4}}
\newcommand{\mapEntry}[2]{{#1} \mapsto {#2}}
\newcommand{\hlight}[1]{{\colorbox{yellow}{#1}}}
\newcommand{\hlightM}[1]{{\colorbox{yellow}{$#1$}}}

% Type constructors
\newcommand{\tBool}{\text{bool}}
\newcommand{\tInt}{\text{int}}
\newcommand{\tFloat}{\text{float}}
\newcommand{\tString}{\text{string}}
\newcommand{\tUnit}{\text{unit}}
\newcommand{\tFun}[2]{\left({#1}\right) \rightarrow {#2}}
\newcommand{\tStructNoCases}{\text{struct}\,}
\newcommand{\tStruct}[1]{\tStructNoCases\left\{{#1}\right\}}
\newcommand{\tUnionNoFields}{\text{union}\,}
\newcommand{\tUnion}[1]{\tUnionNoFields\left\{{#1}\right\}}

% Analysis operators
\newcommand{\fv}[1]{\operatorname{fv}\!\left({#1}\right)}
\newcommand{\captures}[1]{\operatorname{cv}\!\left({#1}\right)}
\newcommand{\lub}[2]{\operatorname{lub}\!\left({#1},{#2}\right)}
\newcommand{\hygToANFDefs}[1]{\operatorname{toANFDefs}\!\left({#1}\right)}
\newcommand{\hygToANF}[2]{\operatorname{toANF}\!\left({#1},{#2}\right)}
\newcommand{\hygToANFOneArg}[1]{\operatorname{toANF}\!\left({#1}\right)}
$$
