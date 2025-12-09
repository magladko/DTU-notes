Natural Deduction and Gentzen-style proofs
<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mrow><mfrac><mrow><msub><mrow><mi>𝑝</mi><mi>𝑟</mi><mi>𝑒</mi><mi>𝑚</mi><mi>𝑖</mi><mi>𝑠</mi></mrow><mn>1</mn></msub><mspace width="1.0em"></mspace><mi>…</mi><mspace width="1.0em"></mspace><msub><mrow><mi>𝑝</mi><mi>𝑟</mi><mi>𝑒</mi><mi>𝑚</mi><mi>𝑖</mi><mi>𝑠</mi></mrow><mi>n</mi></msub></mrow><mrow><mi>𝑐</mi><mi>𝑜</mi><mi>𝑛</mi><mi>𝑐</mi><mi>𝑙</mi><mi>𝑢</mi><mi>𝑠</mi><mi>𝑖</mi><mi>𝑜</mi><mi>𝑛</mi></mrow></mfrac><mo stretchy="false" form="prefix">(</mo><mi>n</mi><mi>a</mi><mi>m</mi><mi>e</mi><mo stretchy="false" form="postfix">)</mo></mrow></math>

Program semantics is about assigning meaning to programs.

## Axiomatic Semantics

Pre+Post condition to all statements in the program (can use Hoare triplets).
$$
\{P\}C\{Q\}
$$

## Denotational Semantics

The idea behind denotational semantics is to map the semantics of the program we want to analyse to something we know well.

<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mrow><mi>e</mi><mo>∈</mo><mrow><mi>𝔼</mi><mi>𝕏</mi></mrow><mo>:=</mo><msub><mi>e</mi><mn>1</mn></msub><mo>+</mo><msub><mi>e</mi><mn>2</mn></msub><mrow><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace></mrow><mi>x</mi><mrow><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mspace width="0.222em"></mspace></mrow><mi>n</mi></mrow></math>
<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>ℰ</mi><mrow><mo stretchy="false" form="prefix">⟦</mo><mi>𝚗</mi><mo stretchy="false" form="postfix">⟧</mo></mrow><mi>σ</mi></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mtext mathvariant="normal">toNat</mtext><mo stretchy="false" form="prefix">(</mo><mrow><mo stretchy="false" form="prefix">⟦</mo><mi>𝚗</mi><mo stretchy="false" form="postfix">⟧</mo></mrow><mo stretchy="false" form="postfix">)</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>ℰ</mi><mrow><mo stretchy="false" form="prefix">⟦</mo><mi>𝚡</mi><mo stretchy="false" form="postfix">⟧</mo></mrow><mi>σ</mi></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mtext mathvariant="normal">lookup</mtext><mo stretchy="false" form="prefix">(</mo><mrow><mo stretchy="false" form="prefix">⟦</mo><mi>𝚡</mi><mo stretchy="false" form="postfix">⟧</mo></mrow><mo>,</mo><mi>σ</mi><mo stretchy="false" form="postfix">)</mo></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>ℰ</mi><mrow><mo stretchy="false" form="prefix">⟦</mo><mrow><msub><mi>𝚎</mi><mn>𝟷</mn></msub><mo mathvariant="monospace">+</mo><msub><mi>𝚎</mi><mn>𝟸</mn></msub></mrow><mo stretchy="false" form="postfix">⟧</mo></mrow><mi>σ</mi></mtd><mtd columnalign="left" style="padding-left: 0"><mo>=</mo><mi>ℰ</mi><mrow><mo stretchy="false" form="prefix">⟦</mo><msub><mi>𝚎</mi><mn>𝟷</mn></msub><mo stretchy="false" form="postfix">⟧</mo></mrow><mi>σ</mi><mo>+</mo><mi>ℰ</mi><mrow><mo stretchy="false" form="prefix">⟦</mo><msub><mi>𝚎</mi><mn>𝟸</mn></msub><mo stretchy="false" form="postfix">⟧</mo></mrow><mi>σ</mi></mtd></mtr></mtable></math>

## Operational Semantics
Operational semantics describes the semantic of a program as changes to a state.

Furthermore, the **Structural Operational Semantics** are defined exactly as you would write a interpreter, which is handy because you are going to write one.

The **Structural Operational Semantics** or **Small Step Semantics** are written as judgments of the type ($\psi \vdash \sigma \to \overline{\sigma}$ ) which means given the environment $\psi$, the state of the program σ can be turned into $\overline{\sigma}$.


**Big Step semantics**: easy to read, unable to encode infinite behavior
**Small Step semantics**: translates directly to interpreter behavior

## Transition System and Traces

> [!definition] Transition System
> A Transition system is a triplet $\langle \mathbf{State}_{P}, \delta_{P}, I_{P} \rangle$ where $\mathbf{State}_{P}$ is the set of program states, $\delta_{P}$ is the transition relation (defined by the single step semantics) and $I_{P}$ are possible initial states.

A $\mathbf{Trace}_{P}$ is the possible infinite sequence of states and operations of the program.
$$
\mathbf{Trace}_{P} = \mathbf{State}^*_{P}
$$

A program can be described as a set of traces it exhibits.

<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mtext mathvariant="normal">Sem</mtext></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mspace width="0.222em"></mspace><mo>:</mo><mspace width="0.222em"></mspace></mrow><mrow><mi>𝐏</mi><mi>𝐫</mi><mi>𝐨</mi><mi>𝐠</mi><mi>𝐫</mi><mi>𝐚</mi><mi>𝐦</mi></mrow><mo>→</mo><msup><mn>2</mn><mrow><mi>𝐓</mi><mi>𝐫</mi><mi>𝐚</mi><mi>𝐜</mi><mi>𝐞</mi></mrow></msup></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mtext mathvariant="normal">Sem</mtext></mtd><mtd columnalign="left" style="padding-left: 0"><mo stretchy="false" form="prefix">(</mo><mi>P</mi><mo stretchy="false" form="postfix">)</mo><mo>=</mo><mrow><mo stretchy="true" form="prefix">{</mo><mi>τ</mi><mo>∈</mo><msubsup><mrow><mi>𝐒</mi><mi>𝐭</mi><mi>𝐚</mi><mi>𝐭</mi><mi>𝐞</mi></mrow><mi>P</mi><mi>n</mi></msubsup><mi>&nbsp;|&nbsp;</mi><mi>n</mi><mo>∈</mo><mo stretchy="false" form="prefix">[</mo><mn>1</mn><mo>,</mo><mi>∞</mi><mo stretchy="false" form="postfix">]</mo><mo>,</mo><msub><mi>τ</mi><mn>0</mn></msub><mo>∈</mo><msub><mi>I</mi><mi>P</mi></msub><mo>,</mo><mo>∀</mo><mi>i</mi><mo>∈</mo><mo stretchy="false" form="prefix">[</mo><mn>1</mn><mo>,</mo><mi>n</mi><mo>−</mo><mn>1</mn><mo stretchy="false" form="postfix">]</mo><mo>,</mo><msub><mi>δ</mi><mi>P</mi></msub><mo stretchy="false" form="prefix">(</mo><msub><mi>τ</mi><mrow><mi>i</mi><mo>−</mo><mn>1</mn></mrow></msub><mo>,</mo><msub><mi>τ</mi><mi>i</mi></msub><mo stretchy="false" form="postfix">)</mo><mo stretchy="true" form="postfix">}</mo></mrow></mtd></mtr></mtable></math>
Also called **Maximal Trace Semantics**. 
Properties can now be described (e.g. halt):
<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mrow><msub><mi>ℒ</mi><mtext mathvariant="normal">halt</mtext></msub><mo>=</mo><mo stretchy="false" form="prefix">{</mo><mi>P</mi><mrow><mi>&nbsp;|&nbsp;</mi><mo>⁡</mo></mrow><mi>P</mi><mo>∈</mo><mi>ℒ</mi><mo>,</mo><mo>∀</mo><mi>τ</mi><mo>∈</mo><mtext mathvariant="normal">Sem</mtext><mo stretchy="false" form="prefix">(</mo><mi>P</mi><mo stretchy="false" form="postfix">)</mo><mi>.</mi><mspace width="0.222em"></mspace><mo stretchy="false" form="prefix">|</mo><mi>τ</mi><mo stretchy="false" form="prefix">|</mo><mo>≠</mo><mi>∞</mi><mo stretchy="false" form="postfix">}</mo></mrow></math>
## JVM & Java Bytecode

bytecode ($\text{bc}$) judgements:
- $\text{bc} \vdash s \to s$
- $\text{bc} \vdash s \to \text{ok}$
- $\text{bc} \vdash s \to \text{err('msg')}$

Program Counter ($\iota$)
<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="text-align: right"><mi>ι</mi><mo>=</mo><mrow><mo stretchy="true" form="prefix">⟨</mo><msub><mi>ι</mi><mi>m</mi></msub><mo>,</mo><msub><mi>ι</mi><mi>o</mi></msub><mo stretchy="true" form="postfix">⟩</mo></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="text-align: right"><mi>ι</mi><mo>+</mo><mi>n</mi><mo>=</mo><mrow><mo stretchy="true" form="prefix">⟨</mo><msub><mi>ι</mi><mi>m</mi></msub><mo>,</mo><msub><mi>ι</mi><mi>o</mi></msub><mo>+</mo><mi>n</mi><mo stretchy="true" form="postfix">⟩</mo></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="text-align: right"><mi>n</mi><mi>/</mi><mi>ι</mi><mo>=</mo><mrow><mo stretchy="true" form="prefix">⟨</mo><msub><mi>ι</mi><mi>m</mi></msub><mo>,</mo><mi>n</mi><mo stretchy="true" form="postfix">⟩</mo></mrow></mtd></mtr></mtable></math>


- **Operator stack**: intermediate values
- **Locals**: storage local to the method (indexed)
- **Heap**: global memory

Values are dynamically typed -> every value carries around type info.
- **stack values**: $V_{\sigma} := (\text{int }n)~|~(\text{float }f)~|~(\text{ref }r)$
- **heap values**: $V_{\eta} := V_{\sigma}~|~(\text{byte }b)~|~(\text{char }c)~|~(\text{short }s)~|~(\text{array }t~a)~|~(\text{object }cn~fs)$

> [!note] long and double purposefully omited (pain in the ass)

