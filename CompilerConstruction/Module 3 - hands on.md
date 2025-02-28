## hyggec compiler phases
![[hyggec_compiler_phases.png]]

---

- Lexing - tokenizer
`42 + x` -> `[LIT_INT 42; PLUS; IDENT "x"; EOF]`

- Parsing - turn tokens into AST
... -> 
```
Add (1:1-1:6)
┣╾lhs: IntVal 42 (1:1-1:2)
┗╾rhs: Var x (1:6-1:6)
```

