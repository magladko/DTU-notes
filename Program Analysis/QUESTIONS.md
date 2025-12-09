## Syntactic Analysis
1. What are the limitations of a syntactic analysis?
	- Missing complex logic (i.e. misses actual runtime meaning of code)
	- Can never be sound (cannot guarantee to accept only good programs)
2. When is syntactic analysis a good tool?
	- Detecting code syntax issues
	- Recognizing common/predefined patterns (e.g. unsafe expressions, trivial source code issues etc.)
3. Trick Question: Is Java a regular language, context free or recursive enumerable?
	- Recursive enumerable:
		- nested structure: not regular
		- scoping mechanism: not context free

## Semantics
1. Is analysing bytecode a semantic analysis?
No, if without interpretation, it is merely a syntactic analysis.
2. Name some ways can you describe the semantics of a program?
	- Operational semantics (small+big step)
	- Denotational semantics
	- Maximal trace semantics
	- Axiomatic semantics
3. What does it mean to interpret a piece of code?
It means to apply operational semantics described by code over state machine.

## Dynamic Analysis
1. Name cases where the choice of a dynamic analysis makes the most sense?
	- It is used as a simple initial analysis, often being easier than a syntactic analysis, especially since most languages have a built-in interpreter.
	- The goal is to produce a concrete trace that produces an error, which makes debugging very easy.
	- The number of relevant traces can be managed by abstracting them into a finite set of trace classes (like the path equivalent class).
	- You want to guarantee that if a warning is produced, the problem is real, because dynamic analysis underestimates the set of valid traces.
2. What are the primary limitation and challenges of dynamic analysis?
	- **Lack of Guarantee:** Dynamic analysis cannot guarantee that something _cannot_ happen (e.g., that a program will run forever). It can only prove that a program _may_ fail if a trace ends in a failure.
	- **Infinite Traces:** The number of traces in a program's semantics is often infinite, making it impossible to cover them all without using trickery like trace prediction or abstraction.
	- **Environment Setup:** Setting up the correct runtime environment can be hard or impossible without running the analysis in production.
	- **Side Effects:** Running a program to check for a warning can be problematic if the program has irreversible side effects (e.g., "deleting the database").
	- **The observer effect** --  (act monitoring can change SW behavior - Heisenbugs)
3. When is random sampling of inputs better than testing small values and visa versa?
- **Random Sampling (Fuzzing):** This is effective when the input space corresponds well to the path equivalent space. It works well when simple conditional branches (e.g., `i > 0`) give an equal chance of hitting either path.
- **Small Value Testing (Small-Scope Hypothesis):** This is better when investigating only a small section of inputs is sufficient to find most bugs. It excels at small cases (like checking empty lists) and ensures that if a bug is found, the resulting input is the smallest one that creates the error.
