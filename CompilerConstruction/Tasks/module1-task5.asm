# A simple program that adds two integers (one stored in memory, the other
# immediate), stores the result in memory, and exits.

.data        # The next items are stored in the Data memory segment
msg_eq:
    .string " = "
msg_gt:
    .string " > "
msg_lt:
    .string " < "

.text        # The next items are stored in the Text memory segment

    li a7, 6
    ecall          # ReadInt
    fmv.s ft0, fa0 # load the input
    
    ecall          # ReadInt
    fmv.s ft1, fa0 # load the input


    li a7, 2  # PrintFloat
    fmv.s fa0, ft0 # 
    ecall     # Print the 1st nr
if:
    li t1, 1
        
    feq.s t0, ft0, ft1
    beq t0, t1, case_eq

    fgt.s t0, ft0, ft1
    beq t0, t1, case_gt
    
    flt.s t0, ft0, ft1
    beq t0, t1, case_lt
    j fi
case_eq:
    la a0, msg_eq
    j fi
case_gt:
    la a0, msg_gt
    j fi
case_lt:
    la a0, msg_lt
    j fi
fi:
    li a7, 4 # PrintStr
    ecall

    li a7, 2       # PrintFloat
    fmv.s fa0, ft1 #
    ecall          # Print the 1st nr

    li a7, 10  # Load the immediate value 10 in register fa7
    ecall      # Perform syscall. In RARS, if fa7 is 10, this means: "Exit"
