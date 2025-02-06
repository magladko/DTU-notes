# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
value:       # Label for the memory address of the value below
    .word 3  # Allocate a word (size: 4 bytes) and initialise it to value 3
result:      # Label for the memory address of the value below
    .word 0  # Allocate a word (size: 4 bytes) and initialise it to value 0

.text        # The next items are stored in the Text memory segment
    lw t0, value    # Load word at the memory addres 'value' in register t0
    li t1, 42       # Load the immediate value 42 in register t1
    add t0, t0, t1  # Add contents of t0 and t1, store result in t0
    la t1, result   # Load the memory address of label 'result' in t3
    sw t0, 0(t1)    # Store word in t0 in memory address in t3 (offset 0)

    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
