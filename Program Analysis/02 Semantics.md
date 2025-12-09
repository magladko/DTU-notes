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

