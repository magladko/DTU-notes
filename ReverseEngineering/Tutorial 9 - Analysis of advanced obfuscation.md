Obfuscation signals:
1. Jump to the middle of an instruction (jz ... loc_... + 1)
2. High/unexpected jump addresses
3. some bytes present after db (define byte)/dd (define double word)

for 1.:
- label not reachable locally: then it is not an instruction
  Press `D` - switch instruction -> data
  Press `C` - switch data -> instruction under weird jump label
  **MUST**: be sure that the byte is never executed
![[obfuscated.png]]
![[obfuscated_wip.png]]
![[deobfuscated.png]]

Then reanalyze to let IDA recognize the code snippet as function (`P`).
**IMPORTANT**: Save before - might mess up the work
Then `SPACE` for the graph form.

NOTE:
- Call gives no flag guarantees - jumps just after call should be assumed to be non-deterministic (can jump or not)
- jl + jge (the same label) -> gives ultimately an unconditional jump
