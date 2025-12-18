60h `pushad` - store all registers on stack
61h `popad` - pop back the register values from stack
Used to make the context of the packed executable faithful to the original system env.

 If pushad used, then a popad could be expected at the same function (not to mess with the stack). Then a jmp could be encountered, which might lead to a different code segment (look at memory map) and might be followed by 0-data (filler data).
If the jmp points to 0s, it is promising, since it might be filled with an unpacked app data.

After running to the breakpoint at this jmp, the data at target address should be filled with the unpacked entry point