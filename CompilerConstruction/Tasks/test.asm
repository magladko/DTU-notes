# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
n:
    .word 0
result:      # Label for the memory address of the value below
    .word 0  # Allocate a word (size: 4 bytes) and initialise it to value 0
message:
	.string "1234"

.text        # The next items are stored in the Text memory segment

    li a0, 1
    li a7, 64
#    li a2, 4
    la a1, message
#    mv a1, t0
    ecall
    
    
return:
    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
