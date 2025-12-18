60h `pushad` - store all registers on stack
61h `popad` - pop back the register values from stack
Used to make the context of the packed executable faithful to the original system env.

 If pushad used, then a popad could be expected at the same function (not to mess with the stack). Then a jmp could be encountered, which might lead to a different code segment (look at memory map) and might be followed by 0-data (filler data).
If the jmp points to 0s, it is promising, since it might be filled with an unpacked app data. (to look at jmp target: "follow in disassembler")

After running to the breakpoint at this jmp, the data at target address should be filled with the unpacked entry point.

To unpack:
1. perform the jmp
2. plugins -> Scylla
3. OEP: Address should be pre-filled
4. VA: import address table address
	1. search familiar imported function names or dll names
5. Size (size of IAT) - 
6. Click `DUMP`
7. Fix `DUMP`

If pushad/popad is obfuscated:
1. pushad: monitor ESP for a decrease 20h/32bytes/8pointers (pushing all registers)
2. popad: hardware breakpoint on memory access for pushed registers