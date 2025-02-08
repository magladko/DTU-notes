.text # The next items are stored in the Text memory segment

	# t0 - n
	# t1 - i
	# ft0 - result

	li a7, 5
	ecall
	mv t0, a0 # ReadInt
	
	li t1, 0 # iterator variable
	fmv.w.x ft0, t1 # result variable
loop_guard:
	blt t1, t0, loop_body

    j loop_end
	loop_body:

		li t3, 2
		mul t4, t1, t3 # 2*i
		li t3, 1
		add t4, t4, t3 # (2*i)+1

		andi t3, t1, 1
		li t5, 1
		beq t3, t5, odd
		j even
		odd:
		li t5, -1
		even:

		fcvt.s.w ft1, t4
		fcvt.s.w ft2, t5
		fdiv.s ft3, ft2, ft1
		fadd.s ft0, ft0, ft3
		
	    li t3, 1
	    add t1, t1, t3 # increment i

	    j loop_guard
loop_end:
	
	li t5, 4
	fcvt.s.w ft1, t5
	fmul.s ft0, ft0, ft1 # *4
	
	li a7, 2
	fmv.s fa0, ft0
	ecall # Print result

return:
    li a7, 10  # Load the immediate value 10 in register a7
    ecall      # Perform syscall. In RARS, if a7 is 10, this means: "Exit"
