# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
result:      # Label for the memory address of the value below
    .word 0  # Allocate a word (size: 4 bytes) and initialise it to value 0

.text        # The next items are stored in the Text memory segment

    li a7, 5
    ecall     # ReadInt
    mv t0, a0 # load the input
    
    ecall     # ReadInt
    mv t1, a0 # load the input

    add t0, t0, t1  # Add contents of t0 and t1, store result in t0
    la t1, result   # Load the memory address of label 'result' in t1
    sw t0, 0(t1)    # Store word in t0 in memory address in t1 (offset 0)

    li a7, 1
    lw a0, result # Move result to console output arg
    ecall         # PrintInt

    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
