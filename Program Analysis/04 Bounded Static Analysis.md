The Bounded Static Analysis on a program $P$ can defined as the set of traces of depth n: $\mathbf{BSA}_{P}^n$. We can get this set using a many-stepping function 𝚜𝚝𝚎𝚙. It takes a set of traces and steps them one step.

$$
\mathtt{step}_{P}(T) = \{ \tau's ~|~ s \in \Sigma, \tau' \in T, \delta_{P}(\tau'_{|\tau'|}, s) \}
$$
- $\delta$ is a transition relation defined by the single step semantics.
- $\tau's$ means appending $s$ to $\tau'$ 

- **Must analysis**: underestimate the set of traces
- **May analysis**: overestimate the set of traces

## Abstractions

$$ 
\mathbf{Sign} = \{ +, 0, - \}
$$
<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>α</mi><mo stretchy="false" form="prefix">(</mo><mrow><mo stretchy="true" form="prefix">{</mo><mn>1</mn><mo>,</mo><mn>2</mn><mo>,</mo><mn>3</mn><mo stretchy="true" form="postfix">}</mo></mrow><mo stretchy="false" form="postfix">)</mo><mspace width="0.222em"></mspace><mo>=</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mo stretchy="true" form="prefix">{</mo><mi>+</mi><mo stretchy="true" form="postfix">}</mo></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>α</mi><mo stretchy="false" form="prefix">(</mo><mrow><mo stretchy="true" form="prefix">{</mo><mn>0</mn><mo stretchy="true" form="postfix">}</mo></mrow><mo stretchy="false" form="postfix">)</mo><mspace width="0.222em"></mspace><mo>=</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mo stretchy="true" form="prefix">{</mo><mn>0</mn><mo stretchy="true" form="postfix">}</mo></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>α</mi><mo stretchy="false" form="prefix">(</mo><mrow><mo stretchy="true" form="prefix">{</mo><mi>−</mi><mn>1</mn><mo>,</mo><mn>3</mn><mo stretchy="true" form="postfix">}</mo></mrow><mo stretchy="false" form="postfix">)</mo><mspace width="0.222em"></mspace><mo>=</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mo stretchy="true" form="prefix">{</mo><mi>+</mi><mo>,</mo><mi>−</mi><mo stretchy="true" form="postfix">}</mo></mrow></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mi>α</mi><mo stretchy="false" form="prefix">(</mo><mrow><mo stretchy="true" form="prefix">{</mo><mi>−</mi><mn>1</mn><mo>,</mo><mn>0</mn><mo>,</mo><mn>3</mn><mo stretchy="true" form="postfix">}</mo></mrow><mo stretchy="false" form="postfix">)</mo><mo>=</mo></mtd><mtd columnalign="left" style="padding-left: 0"><mrow><mo stretchy="true" form="prefix">{</mo><mn>0</mn><mo>,</mo><mi>+</mi><mo>,</mo><mi>−</mi><mo stretchy="true" form="postfix">}</mo></mrow></mtd></mtr></mtable></math>

### Partially Ordered Sets (Posets)

