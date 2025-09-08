```
  proof (*(rule Dis_I2)*)
    (*assume ‹p ∧ q›*)
    (*then have ‹q› ..*)
    (*from ‹p ∧ q› have ‹p› ..*)
    (*from ‹¬ (p ∧ q)› and ‹p ∧ q› have ‹⊥› ..*)
    show ‹¬ q›
    proof (rule Neg_I)
      (*assume ‹p ∧ q›*)
      assume ‹q›
      show ‹⊥› sorry
      (*proof
        case 
        show ‹⊥› sorry
      next
        assume ‹¬ p›
        show ‹⊥› sorry
      qed*)
      (*from ‹¬ (p ∧ q)› and ‹p ∧ q› have ‹⊥› ..*)
    qed
  qed
```
