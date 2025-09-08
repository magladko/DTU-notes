# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
arr:
    .word 10, 9, 7, 4, 5, 6, 0, 1, 2, 8, 3
delim:
	.string " "
.text        # The next items are stored in the Text memory segment

	la t0, arr # initialize array pointer
	lw t1, (t0)  # load array size
	li t2, 4 # size of int (4 bytes)
	add t0, t0, t2 # push forward array pointer

loop_guard:
	li t2, 0
	bgt t1, t2, loop_body

    j loop_end
	loop_body:
		li a7, 1   # PrintInt
		lw a0, (t0)  # read array element
		ecall      # PrintInt
		
		li a7, 4
		la a0, delim
		ecall # Print space
	
		li t2, 4 # size of int (4 bytes)
		add t0, t0, t2 # push forward array pointer

	    li t2, -1
	    add t1, t1, t2 # decrement iterator

	    j loop_guard
loop_end:

return:
    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
