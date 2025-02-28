## hyggec compiler phases
![[hyggec_compiler_phases_interpreter.png]]

---

### Lexing - 'tokenize' (Lexer.fsl => Lexer.fs)

`42 + x` -> `[LIT_INT 42; PLUS; IDENT "x"; EOF]`

### Parsing - tokens to (untyped) AST (Parser.fsy => Parser.fs)
... -> 
```
Add (1:1-1:6)
┣╾lhs: IntVal 42 (1:1-1:2)
┗╾rhs: Var x (1:6-1:6)
```

### Type checking - untyped AST -> AST

```
Add (1:1-1:6)
┣╾Env.Vars: ∅
┣╾Env.TypeVars: ∅
┣╾Type: int
┣╾lhs: IntVal 42 (1:1-1:2)
┃      ┣╾Env.Vars: ∅
┃      ┣╾Env.TypeVars: ∅
┃      ┗╾Type: int
┗╾rhs: IntVal 1 (1:6-1:6)
       ┣╾Env.Vars: ∅
       ┣╾Env.TypeVars: ∅
       ┗╾Type: int
```

