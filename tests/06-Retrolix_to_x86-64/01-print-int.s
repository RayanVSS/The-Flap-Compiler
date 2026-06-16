.data
.text
	.globl main
.p2align 3, 144
main:
	/* Program entry point. */
	subq $8, %rsp
	call .I_129913994
	movq $0, %rdi
	call exit
.p2align 3, 144
.I_129913994:
	/* Initializer for . */
	movq $73, %rdi
	subq $8, %rsp
	call observe_int
	addq $8, %rsp
	movq $0, %rdi
	subq $8, %rsp
	call exit
	addq $8, %rsp
