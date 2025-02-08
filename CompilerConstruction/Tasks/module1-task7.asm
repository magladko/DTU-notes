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

	li t1, 0
	fmv.w.x ft0, t1 # initialize result
loop_guard:
	li t1, 0
	bgt t0, t1, loop_body
    
    j loop_end
	loop_body:
	    li a7, 6 # ReadFloat
	    ecall    # ReadFloat
	    
	    fadd.s ft0, ft0, fa0
	    
	    li t1, -1
	    add t0, t0, t1 # decrement counter

	    j loop_guard
loop_end:

    li a7, 2   # PrintFloat
    fmv.s fa0, ft0 # Move result to console output arg
    ecall      # PrintFloat

return:
    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
