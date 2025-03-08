.data:
string_val:
    .string "TEST"

.text:
    la t0, string_val
    # Before system call: save registers
    addi sp, sp, -8  # Update stack pointer to make room for saved registers
    #sw a7, 0(sp)
    #sw a1, 4(sp)
    mv a1, t0  # Copy to a1 for printing
    li a0, 2  # Set stderr
    li a7, 64  # RARS syscall: Write
    ecall
    # After system call: restore registers
    lw a7, 0(sp)
    lw a1, 4(sp)
    addi sp, sp, 8  # Restore stack pointer after register restoration
    li a7, 10  # RARS syscall: Exit
    ecall  # Successful exit with code 0

