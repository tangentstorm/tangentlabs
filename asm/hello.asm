;;------------------------------------------------------
;; hello world in nasm for freebsd x64
;; found at http://forum.nasm.us/index.php?topic=1283.0
;; this incredibly detailed tutorial is also great:
;; http://farid.hajji.name/blog/2009/12/26/hello-world-in-freebsd-assembler/
;;------------------------------------------------------

;; Assemble with
;; nasm -felf64 hello.asm
;; Link with
;; ld -o hello hello.o

section .data
    message db  "Hello World!",10
    MSGLEN equ $-message

section .text
    global _start

    _start:

        ; print the string using write() system call
        mov     rdx, MSGLEN
        mov     rsi, dword message
        mov     rdi, 1
        mov     rax, 4
        syscall

        ; exit from the application here
        mov     rax, 1
        xor     edi, edi
        syscall
