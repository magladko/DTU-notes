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

