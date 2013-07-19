section .text
global _start
_start:
	mov rax, 1
	mov rdi, 0
	syscall
