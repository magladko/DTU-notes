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

	Then reanalyze to let IDA recognize the code snippet as function (`P`) **at the starting label**.
	**IMPORTANT**: Save before - might mess up the work
	Then `SPACE` for the graph form.

- If the jmp might be used, analyze what it means, convert to data and `;` put comment that it is actually a jmp
  Or if jmp by 1 then == **nop (0x90)**, we need to convert the jmp to nop
	- Change in hex editor (permanent), in hex view look at bottom left (offset) to use as a reference in the hexd
	- In IDA: `Edit -> Patch program -> Change byte...`
	  This shows current byte row, overwrite with 90 (nop)
	  Leave comment of the original command (that it was modified), this is also visible in `Edit -> Patch program -> Patched bytes`
	  REMEMBER TO CHANGE THE FOLLOWING BYTE TO INSTRUCTION

**Nested Function case** 
Important note: it modifies the return address (add ptr \[esp+0\] ...)
Which seems to skip exactly to the code directly after the function.
IDEA:
- interpret as data with comment left
- fill with NOPs
- change call to jmp to destination
	- `Edit -> Patch program -> Assemble...` with cursor on call
	- change to `JMP [destination address]`
  
**Irrelevant code obfuscation**
A lot of commands without real impact on code.
Important notice - side effects (e.g. overflow), like:
mul 32bit 32bit register into another 32bit, not 64 (mul esi with eax)

NOTE:
- Call gives no flag guarantees - jumps just after call should be assumed to be non-deterministic (can jump or not)
- jl + jge (the same label) -> gives ultimately an unconditional jump
- `mul esi` -> actually `eax * esi`, might use EDX+EAX for 64bit result