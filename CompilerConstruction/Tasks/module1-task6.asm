# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
n:
    .word 0
result:      # Label for the memory address of the value below
    .word 0  # Allocate a word (size: 4 bytes) and initialise it to value 0


.text        # The next items are stored in the Text memory segment

    li a7, 5
    ecall     # ReadInt
    mv t0, a0
    #sw a0, n, t0 # load the input

loop_fact:
	    li t1, 0
	    bgt t0, t1, case_n_positive
	    
	    j default
	case_n_positive:
	    
	    j loop_fact_fi
	default:
	    j return
	
loop_fact_fi:

    li a7, 1
    lw a0, result # Move result to console output arg
    ecall         # PrintInt

return:
    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
