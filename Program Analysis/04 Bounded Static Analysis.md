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
A _partially ordered set_ or **poset is a tuple** (L,⊑) set of elements L and an ordering ⊑, that uphold:
<math display="block" xmlns="http://www.w3.org/1998/Math/MathML"><mtable><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mtext mathvariant="normal">reflexive</mtext></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="1.0em"></mspace><mo>∀</mo><mi>a</mi><mi>.</mi><mspace width="0.222em"></mspace><mi>a</mi><mo>⊑</mo><mi>a</mi></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mtext mathvariant="normal">antisymetric</mtext></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="1.0em"></mspace><mo>∀</mo><mi>a</mi><mi>.</mi><mspace width="0.222em"></mspace><mi>a</mi><mo>⊑</mo><mi>b</mi><mo>∧</mo><mi>b</mi><mo>⊑</mo><mi>a</mi><mo>⟹</mo><mi>a</mi><mo>=</mo><mi>b</mi></mtd></mtr><mtr class="fragment"><mtd columnalign="right" style="padding-right: 0"><mtext mathvariant="normal">transitive</mtext></mtd><mtd columnalign="left" style="padding-left: 0"><mspace width="1.0em"></mspace><mo>∀</mo><mi>a</mi><mi>.</mi><mspace width="0.222em"></mspace><mi>a</mi><mo>⊑</mo><mi>b</mi><mo>∧</mo><mi>b</mi><mo>⊑</mo><mi>c</mi><mo>⟹</mo><mi>a</mi><mo>⊑</mo><mi>c</mi></mtd></mtr></mtable></math>
> [!example] Posets examples
> - Integers $(\mathbb{Z}, \leq)$ or $(\mathbb{Z}, \geq)$
> - booleans $(\{ \mathtt{tt}, \mathtt{ff} \}, \Rightarrow)$
> - set of Sign's $(2^\text{Sign}, \subseteq)$


### Lattices

A lattice is partially ordered sets (L,⊑), with two extra operators ⊔ (join) and ⊓ (meet).
>[!example] Sign Set lattice
>- $\sqsubseteq_{\text{Sign}} = \subseteq$
>- $\sqcup = \cap$
>- $\sqcap = \cup$
>- $\bot = \emptyset$
>- $\top = \{ +, -, 0 \}$
