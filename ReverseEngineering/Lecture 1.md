**ABI** - Application Binary Interface
**ESP** - stack pointer
**EBP** - stack frame

![[prologue_1_ebp.png|600]]

## **(32-bit)**
![[ollyDbg_registers(fpu).png|600]]
### Generic calculation registers (not atomic)
```
(modifies either direction)
EAX = c7818355
 AX =     8355
 AH =     83
 AL =       55
```
- **EAX**
- **ECX** 
- **EDX** 
- **EBX** 

### Stack
- **ESP** - stack pointer
- **EBP** - stack frame pointer

### -
**EIP** - instruction pointer (points to the next instruction to be executed)

### Segment Registers (mostly unused)
Filled by OS
ES/CS/SS/DS/FS/GS 

FS[0] - exception-related

\+ LastErr (not a register - like C errno)
### Flags (Part of EFL)
- C - carry (ran out of bits when arith, op)
- P - parity bit (odd/even nr of 1s in the prev op)
- A - auxiliary carry (almost unused)
- Z - ?result of the last operation is zero
- S - sign flag (last operation negative?)
- T - trace flag - internal for the debugger
- D - direction flag 
- O - overflow (ie. sum of positive resulted in negative)

