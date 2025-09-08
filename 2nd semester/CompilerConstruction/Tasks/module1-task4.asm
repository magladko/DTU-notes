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

    li a7, 5
    ecall     # ReadInt
    mv t0, a0 # load the input
    
    ecall     # ReadInt
    mv t1, a0 # load the input


    li a7, 1  # PrintInt
    mv a0, t0 # 
    ecall     # Print the 1st nr
if:
    beq t0, t1, case_eq
    bgt t0, t1, case_gt
    blt t0, t1, case_lt
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

    li a7, 1  # PrintInt
    mv a0, t1 #
    ecall     # Print the 1st nr

    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
