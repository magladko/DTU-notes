# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
msg:         # Label for the mem addr of the first char of the string below
    .string "The current value is: "  # Allocate a string, in C-style: a
                                      # sequence of characters in adjacent
                                      # memory addresses, terminated with 0


.text        # The next items are stored in the Text memory segment

    li a7, 5
    ecall     # ReadInt
    mv t0, a0 # load the input
    
    ecall     # ReadInt
    mv t1, a0 # load the input

    

    li a7, 1
    lw a0, result
    ecall

    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
