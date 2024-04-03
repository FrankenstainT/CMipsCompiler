.data
_prompt: .asciiz "Please input an integer:"
_ret: .asciiz "\n"
.text
    li $t0, 3333
    sw $t0, 0($sp)
    lw $t0, 0($sp)
    sw $t0, -36($sp)
    li $t0, 6666
    sw $t0, -4($sp)
    lw $t0, -4($sp)
    sw $t0, -32($sp)
    li $t0, 9999
    sw $t0, -8($sp)
    lw $t0, -8($sp)
    sw $t0, -40($sp)
    li $t0, 1
    sw $t0, -12($sp)
    lw $t0, -12($sp)
    sw $t0, -48($sp)
label0:
    li $t0, 0
    sw $t0, -16($sp)
    lw $t1, -16($sp)
    lw $t0, -48($sp)
    sgt $t0, $t0, $t1
    sw $t0, -52($sp)
    lw $t0, -52($sp)
    beqz $t0, label1
    li $t0, 1
    sw $t0, -20($sp)
    lw $t1, -20($sp)
    lw $t0, -48($sp)
    seq $t0, $t0, $t1
    sw $t0, -56($sp)
    lw $t0, -56($sp)
    beqz $t0, label2
    lw $t0, -36($sp)
    sw $t0, -44($sp)
    j label3
label2:
label3:
    li $t0, 2
    sw $t0, -24($sp)
    lw $t1, -24($sp)
    lw $t0, -48($sp)
    seq $t0, $t0, $t1
    sw $t0, -60($sp)
    lw $t0, -60($sp)
    beqz $t0, label4
    lw $t0, -32($sp)
    sw $t0, -44($sp)
    j label5
label4:
label5:
    li $t0, 3
    sw $t0, -28($sp)
    lw $t1, -28($sp)
    lw $t0, -48($sp)
    seq $t0, $t0, $t1
    sw $t0, -64($sp)
    lw $t0, -64($sp)
    beqz $t0, label6
    lw $t0, -40($sp)
    sw $t0, -44($sp)
    j label7
label6:
label7:
    lw $a0, -44($sp)
    li $v0, 1
    syscall
    li $v0, 4
    la $a0, _ret
    syscall
    move $v0, $0
    li $v0, 4
    la $a0, _prompt
    syscall
    li $v0, 5
    syscall
    sw $v0, -48($sp)
    j label0
label1:
