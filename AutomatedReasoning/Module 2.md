
|                                                      |                   |
| ---------------------------------------------------- | ----------------- |
| $\vdash q \to p \implies \vdash q \implies \vdash p$ | MP (modus ponens) |
| $\vdash (q \to r) \to (r \to p) \to q \to p$         | Transitivity      |
| $\vdash (\neg p \to p) \to p$                        | Clavius's Law     |
| $\vdash q \to \neg q \to p$                          | Explosion         |

## MiniCalc cheatsheet

| Non-branching | Branching | Quantifiers | Special |
|---------------|-----------|-------------|---------|
| Imp_R         | Imp_L     | Exi_R       | Basic   |
| Dis_R         | Dis_L     | Exi_L       | Ext     |
| Con_L         | Con_R     | Uni_R       | NegNeg  |
|               |           | Uni_L       |         

```thy
inductive sequent_calculus :: ‹fm list ⇒ bool› (‹⊩ _› 0) where
  Basic: ‹⊩ p # z› if ‹member (Neg p) z› |
  Imp_R: ‹⊩ Imp p q # z› if ‹⊩ Neg p # q # z› |
  Imp_L: ‹⊩ Neg (Imp p q) # z› if ‹⊩ p # z› and ‹⊩ Neg q # z› |
  Dis_R: ‹⊩ Dis p q # z› if ‹⊩ p # q # z› |
  Dis_L: ‹⊩ Neg (Dis p q) # z› if ‹⊩ Neg p # z› and ‹⊩ Neg q # z› |
  Con_R: ‹⊩ Con p q # z› if ‹⊩ p # z› and ‹⊩ q # z› |
  Con_L: ‹⊩ Neg (Con p q) # z› if ‹⊩ Neg p # Neg q # z› |
  Exi_R: ‹⊩ Exi p # z› if ‹⊩ subt t p # z› |
  Exi_L: ‹⊩ Neg (Exi p) # z› if ‹⊩ Neg (inst c p) # z› and ‹news c (p # z)› |
  Uni_R: ‹⊩ Uni p # z› if ‹⊩ inst c p # z› and ‹news c (p # z)› |
  Uni_L: ‹⊩ Neg (Uni p) # z› if ‹⊩ Neg (subt t p) # z› |
  Extra: ‹⊩ z› if ‹⊩ p # z› and ‹member p z›
```
