# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
#value:       # Label for the memory address of the value below
#    .word 3  # Allocate a word (size: 4 bytes) and initialise it to value 3
result:      # Label for the memory address of the value below
    .float 0  # Allocate a word (size: 4 bytes) and initialise it to value 0

.text        # The next items are stored in the Text memory segment

    li a7, 6
    ecall     # ReadFloat
    fmv.s ft0, fa0 # move the input to ft1 register
    
    ecall     # ReadFloat
    fmv.s ft1, fa0 # move the input to ft1 register

    fadd.s ft0, ft0, ft1 # Add floats inplace
    #add ft0, ft0, ft1  # Add contents of ft0 and ft1, store result in ft0
    la t0, result   # Load the memory address of label 'result' in t0
    fsw ft0, 0(t0)   # Store word in ft0 in memory address in t0 (offset 0)

    li a7, 2
    fmv.s fa0, ft0
    ecall

    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
