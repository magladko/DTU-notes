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

### Type checking - untyped AST -> AST (Typechecker.fs)

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

### RISCV codegen (RISCVCodegen.fs)

using API from `RISCV.fs`

## steps to extend
1. `Lexer.fsl`

2. `Parser.fsy`
3. `Typechecker.fs`
4. `Interpreter.fs` / `RISCVCodegen.fs`
---
1. **LEXER**
	1. Add new operator in the `Lexer.fsl`
	2. Register new token in `Parser.fsy`
	3. Write tests in `tests/lexer/`
2. **PARSER**
	1. Create an expression in `Parser.fsy` (modify the closest)
	2. Add new `Expr` type to `AST.fs` (modify the closest)
	3. Create `tests/parser/` test cases
	4. Adjust `PrettyPrinter.fs`
3. **TYPE CHECKER**
	1. Add type checker record in `Typechecker.fsy` (modify the closest)
	2. Create `tests/typechecker/` test cases
4. **INTERPRETER**
	1. Adjust `Interpreter.fs` + `ASTUtil.fs`
	2. Create `tests/interpreter/` test cases
5. **CODE GENERATION**
	1. Adjust `RISCVCodegen.fs` records
	2. Create `tests/codegen/` test cases
