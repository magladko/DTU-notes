# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
n:
    .word 0
result:      # Label for the memory address of the value below
    .word 0  # Allocate a word (size: 4 bytes) and initialise it to value 0
new_line:
	.string "\n"

.text        # The next items are stored in the Text memory segment

    li a7, 5
    ecall     # ReadInt
    mv t0, a0
    #sw a0, n, t0 # load the input
    
    li t1, 0
	ble t0, t1, return # exit if not positive

    li t2, 1 # initialize temporary result
loop_guard:
	li t1, 1
	bgt t0, t1, loop_body
    
    j loop_end
	loop_body:
	    mul t2, t2, t0
	    li t1, -1
	    add t0, t0, t1

	    j loop_guard
loop_end:

    li a7, 1
    mv a0, t2 # Move result to console output arg
    ecall         # PrintInt

return:
    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
