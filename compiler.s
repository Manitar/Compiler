%define T_UNDEFINED 0
%define T_VOID 1
%define T_NIL 2
%define T_RATIONAL 3
%define T_FLOAT 4
%define T_BOOL 5
%define T_CHAR 6
%define T_STRING 7
%define T_SYMBOL 8
%define T_CLOSURE 9
%define T_PAIR 10
%define T_VECTOR 11

%define TYPE_SIZE 1
%define WORD_SIZE 8
	
%define KB(n) n*1024
%define MB(n) 1024*KB(n)
%define GB(n) 1024*MB(n)

%define FVAR(i) [fvar_tbl+i*WORD_SIZE]

%macro SKIP_TYPE_TAG 2
	mov %1, qword [%2+TYPE_SIZE]	
%endmacro	

%define NUMERATOR SKIP_TYPE_TAG

%macro DENOMINATOR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%macro CHAR_VAL 2
	movzx %1, byte [%2+TYPE_SIZE]
%endmacro

%define FLOAT_VAL SKIP_TYPE_TAG

%define STRING_LENGTH SKIP_TYPE_TAG
%define VECTOR_LENGTH SKIP_TYPE_TAG

%define SYMBOL_VAL SKIP_TYPE_TAG

%macro STRING_ELEMENTS 2
	lea %1, [%2+TYPE_SIZE+WORD_SIZE]
%endmacro
%define VECTOR_ELEMENTS STRING_ELEMENTS

%define CAR SKIP_TYPE_TAG

%macro CDR 2
	mov %1, qword [%2+TYPE_SIZE+WORD_SIZE]
%endmacro

%define CLOSURE_ENV CAR

%define CLOSURE_CODE CDR

%define PVAR(n) qword [rbp+(4+n)*WORD_SIZE]

%define env_ptr qword [rbp + 8 * 2]

%define num_of_params [rbp + 8 * 3]

; returns %2 allocated bytes in register %1
; Supports using with %1 = %2
%macro MALLOC 2
	add qword [malloc_pointer], %2
	push %2
	mov %1, qword [malloc_pointer]
	sub %1, [rsp]
	add rsp, 8
%endmacro
	
; Creates a short SOB with the
; value %2
; Returns the result in register %1
%macro MAKE_CHAR_VALUE 2
	MALLOC %1, 1+TYPE_SIZE
	mov byte [%1], T_CHAR
	mov byte [%1+TYPE_SIZE], %2
%endmacro

; Creates a long SOB with the
; value %2 and type %3.
; Returns the result in register %1
%macro MAKE_LONG_VALUE 3
	MALLOC %1, TYPE_SIZE+WORD_SIZE
	mov byte [%1], %3
	mov qword [%1+TYPE_SIZE], %2
%endmacro

%define MAKE_FLOAT(r,val) MAKE_LONG_VALUE r, val, T_FLOAT
%define MAKE_CHAR(r,val) MAKE_CHAR_VALUE r, val

; Create a string of length %2
; from char %3.
; Stores result in register %1
%macro MAKE_STRING 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_STRING
	mov qword [%1+TYPE_SIZE], %2
	push rcx
	add %1,WORD_SIZE+TYPE_SIZE
	mov rcx, %2
	cmp rcx, 0
%%str_loop:
	jz %%str_loop_end
	dec rcx
	mov byte [%1+rcx], %3
	jmp %%str_loop
%%str_loop_end:
	pop rcx
	sub %1, WORD_SIZE+TYPE_SIZE
%endmacro

%macro MAKE_LITERAL_STRING 2
	db T_STRING
	dq %1
	db %2
%endmacro

%macro MAKE_LITERAL_CHAR 1
	db T_CHAR
	db %1
%endmacro

; Create a vector of length %2
; from array of elements in register %3
; Store result in register %1
%macro MAKE_VECTOR 3
	lea %1, [%2+WORD_SIZE+TYPE_SIZE]
	MALLOC %1, %1
	mov byte [%1], T_VECTOR
	mov qword [%1+TYPE_SIZE], %2

    push rbx
    push rcx
    push %1
    add %1,WORD_SIZE+TYPE_SIZE
    mov rcx, %2
%%vector_loop:
    cmp rcx, 0
    js %%vector_loop_end
    mov rbx, [%3]
    mov [%1], rbx
    add %1, WORD_SIZE
    add %3, WORD_SIZE
    dec rcx
    jmp %%vector_loop
%%vector_loop_end:
    pop %1
    pop rcx
    pop rbx
%endmacro

;;; Creates a SOB with tag %2 
;;; from two pointers %3 and %4
;;; Stores result in register %1
%macro MAKE_TWO_WORDS 4 
        MALLOC %1, TYPE_SIZE+WORD_SIZE*2
        mov byte [%1], %2
        mov qword [%1+TYPE_SIZE], %3
        mov qword [%1+TYPE_SIZE+WORD_SIZE], %4
%endmacro

%macro MAKE_WORDS_LIT 3
	db %1
        dq %2
        dq %3
%endmacro

%define MAKE_RATIONAL(r, num, den) \
	MAKE_TWO_WORDS r, T_RATIONAL, num, den

%define MAKE_LITERAL_RATIONAL(num, den) \
	MAKE_WORDS_LIT T_RATIONAL, num, den
	
%define MAKE_PAIR(r, car, cdr) \
        MAKE_TWO_WORDS r, T_PAIR, car, cdr

%define MAKE_LITERAL_PAIR(car, cdr) \
        MAKE_WORDS_LIT T_PAIR, car, cdr

%define MAKE_CLOSURE(r, env, body) \
        MAKE_TWO_WORDS r, T_CLOSURE, env, body

%define MAKE_LITERAL_CLOSURE(env, body) \
		MAKE_WORDS_LIT T_CLOSURE, env, body

%macro MAKE_LITERAL_FLOAT 1 
	db T_FLOAT
	dq %1
%endmacro

%define MAKE_LITERAL_INT(num) \
		MAKE_LITERAL_RATIONAL num 1

%macro MAKE_LITERAL_SYMBOL 1
	db T_SYMBOL 
	dq %1
%endmacro

%macro BACKUP 0
	push rbx
	push rcx
	push rdx
	push r8
%endmacro

%macro RESTORE 0
	pop r8
	pop rdx
	pop rcx
	pop rbx
%endmacro

%macro SHIFT_FRAME 1
	push rax
	mov rax, num_of_params; Number of params from last
	add rax, 5
	push rbx
%assign i 1
%rep %1

	dec rax
	mov rbx, [rbp - 8 * i]
	mov [rbp + 8 * rax], rbx

%assign i i+1
%endrep
	pop rbx
	pop rax
%endmacro

%macro FIX_MORE_PARAMS 2 ; %1 number of args before fix (for shift), %2 number of args after fix
	lea rdx, [%2 + 4]
	lea rcx, [%1 + 4]
	.loopfix:
	; for stack entry move %1 up, starting from the top
	mov rbx, [rbp + 8 * (rdx -1)]
	mov [rbp + 8 * (rcx - 1)], rbx
	dec rcx
	dec rdx
	cmp rdx, 0
	jl .endloopfix
	jmp .loopfix
	.endloopfix:
	lea rbx, [(%1 - %2) * 8]
	add rsp, rbx
	add rbp, rbx
%endmacro

%macro FIX_LESS_PARAMS 0
	add qword [rbp], 8 
%endmacro

%macro SOB_LIST_SIZE 1
	mov rdx, 0    ; counter
	mov rcx, %1
	.count:
	cmp rcx, (const_tbl + 1) ; exit condition
	je .end_of_count
	inc rdx
	mov rcx, [rcx + 1 + 8]	  ; rcx -> cdr (rcx)
	jmp .count
	.end_of_count:
	push rdx				  ; save length
%endmacro

%macro LIST_TO_ARGS 1
	pop rdx				  ; args counter of list
	add rdx, num_of_params
	sub rdx, 2
	mov rax, num_of_params
	sub rax, 1 ; rax = all num_of_params - 1
	lea rdx, [rdx*8] ; Multiply rdx by 8
	sub rsp, rdx ; make place for all args
	shr rdx, 3 ; Divide rdx by 8
	sub rsp, 8
	mov [rsp], rdx		  ; num of params
	mov r8, %1 ; Put list in r8
	mov rdx, 1 ; Start from 1

	.regular_args:

	mov rcx, 1
	
	.inner_loop:
	cmp rcx, rax ; Check if we finish going over regular args
	je .list_to_args
	mov rbx, PVAR(rcx)
	mov qword [rsp + 8 * rdx], rbx
	inc rcx
	inc rdx
	jmp .inner_loop

	.list_to_args:
	mov rcx, r8 ; Move list to rcx, use it later

	.list_to_args_loop:
	cmp rcx, (const_tbl + 1) ; exit condition
	je .end_of_args
	mov rbx, qword [rcx + 1]
	mov qword [rsp + 8 * rdx], rbx      ; push the car of the pair
	mov rcx, [rcx + 1 + 8]	  ; rcx -> cdr (rcx)
	inc rdx
	jmp .list_to_args_loop
	
	
	.end_of_args:
	
%endmacro

%macro MY_SHIFT_FRAME 1
	push rdx
	push rcx
	push rbx
	push rax
	mov rax, %1

%%my_loop:
	dec rax
	mov rbx, %1
	
	sub rbx, rax
	mov rdx, rbp

	sub rdx, rbx
	sub rdx, rbx
	sub rdx, rbx
	sub rdx, rbx
	sub rdx, rbx
	sub rdx, rbx
	sub rdx, rbx
	sub rdx, rbx

	mov rcx, [rdx]
	mov [rbp + 8 * rax], rcx

	cmp rax, 0
	jne %%my_loop


	pop rax
	pop rbx
	pop rcx
	pop rdx
%endmacro

	
;;; Macros and routines for printing Scheme OBjects to STDOUT
%define CHAR_NUL 0
%define CHAR_TAB 9
%define CHAR_NEWLINE 10
%define CHAR_PAGE 12
%define CHAR_RETURN 13
%define CHAR_SPACE 32
%define CHAR_DOUBLEQUOTE 34
%define CHAR_BACKSLASH 92
	
extern printf, malloc
global write_sob, write_sob_if_not_void
	
write_sob_undefined:
	push rbp
	mov rbp, rsp

	mov rax, qword 0
	mov rdi, .undefined
	call printf

	pop rbp
	ret

section .data
.undefined:
	db "#<undefined>", 0

section .text
write_sob_rational:
	push rbp
	mov rbp, rsp

	mov rdx, rsi
	NUMERATOR rsi, rdx
	DENOMINATOR rdx, rdx
	
	cmp rdx, 1
	jne .print_fraction

	mov rdi, .int_format_string
	jmp .print

.print_fraction:
	mov rdi, .frac_format_string

.print:	
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.int_format_string:
	db "%ld", 0
.frac_format_string:
	db "%ld/%ld", 0

section .text
write_sob_float:
	push rbp
	mov rbp, rsp

	FLOAT_VAL rsi, rsi
	movq xmm0, rsi
	mov rdi, .float_format_string
	mov rax, 1

	;; printf-ing floats (among other things) requires the stack be 16-byte aligned
	;; so align the stack *downwards* (take up some extra space) if needed before
	;; calling printf for floats
	and rsp, -16 
	call printf

	;; move the stack back to the way it was, cause we messed it up in order to
	;; call printf.
	;; Note that the `leave` instruction does exactly this (reset the stack and pop
	;; rbp). The instructions are explicitly layed out here for clarity.
	mov rsp, rbp
	pop rbp
	ret
	
section .data
.float_format_string:
	db "%f", 0		

section .text
write_sob_char:
	push rbp
	mov rbp, rsp

	CHAR_VAL rsi, rsi

	cmp rsi, CHAR_NUL
	je .Lnul

	cmp rsi, CHAR_TAB
	je .Ltab

	cmp rsi, CHAR_NEWLINE
	je .Lnewline

	cmp rsi, CHAR_PAGE
	je .Lpage

	cmp rsi, CHAR_RETURN
	je .Lreturn

	cmp rsi, CHAR_SPACE
	je .Lspace
	jg .Lregular

	mov rdi, .special
	jmp .done	

.Lnul:
	mov rdi, .nul
	jmp .done

.Ltab:
	mov rdi, .tab
	jmp .done

.Lnewline:
	mov rdi, .newline
	jmp .done

.Lpage:
	mov rdi, .page
	jmp .done

.Lreturn:
	mov rdi, .return
	jmp .done

.Lspace:
	mov rdi, .space
	jmp .done

.Lregular:
	mov rdi, .regular
	jmp .done

.done:
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.space:
	db "#\space", 0
.newline:
	db "#\newline", 0
.return:
	db "#\return", 0
.tab:
	db "#\tab", 0
.page:
	db "#\page", 0
.nul:
	db "#\nul", 0
.special:
	db "#\x%02x", 0
.regular:
	db "#\%c", 0

section .text
write_sob_void:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .void
	call printf

	pop rbp
	ret

section .data
.void:
	db "#<void>", 0
	
section .text
write_sob_bool:
	push rbp
	mov rbp, rsp

	cmp word [rsi], word T_BOOL
	je .sobFalse
	
	mov rdi, .true
	jmp .continue

.sobFalse:
	mov rdi, .false

.continue:
	mov rax, 0
	call printf	

	pop rbp
	ret

section .data			
.false:
	db "#f", 0
.true:
	db "#t", 0

section .text
write_sob_nil:
	push rbp
	mov rbp, rsp

	mov rax, 0
	mov rdi, .nil
	call printf

	pop rbp
	ret

section .data
.nil:
	db "()", 0

section .text
write_sob_string:
	push rbp
	mov rbp, rsp

	push rsi

	mov rax, 0
	mov rdi, .double_quote
	call printf
	
	pop rsi

	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rbx, CHAR_TAB
	je .ch_tab
	cmp rbx, CHAR_NEWLINE
	je .ch_newline
	cmp rbx, CHAR_PAGE
	je .ch_page
	cmp rbx, CHAR_RETURN
	je .ch_return
	cmp rbx, CHAR_DOUBLEQUOTE
	je .ch_doublequote
	cmp rbx, CHAR_BACKSLASH
	je .ch_backslash
	cmp rbx, CHAR_SPACE
	jl .ch_hex
	
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx
	jmp .printf
	
.ch_tab:
	mov rdi, .fs_tab
	mov rsi, rbx
	jmp .printf
	
.ch_page:
	mov rdi, .fs_page
	mov rsi, rbx
	jmp .printf
	
.ch_return:
	mov rdi, .fs_return
	mov rsi, rbx
	jmp .printf

.ch_newline:
	mov rdi, .fs_newline
	mov rsi, rbx
	jmp .printf

.ch_doublequote:
	mov rdi, .fs_doublequote
	mov rsi, rbx
	jmp .printf

.ch_backslash:
	mov rdi, .fs_backslash
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	mov rax, 0
	mov rdi, .double_quote
	call printf

	pop rbp
	ret
section .data
.double_quote:
	db CHAR_DOUBLEQUOTE, 0
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	
.fs_tab:
	db "\t", 0
.fs_page:
	db "\f", 0
.fs_return:
	db "\r", 0
.fs_newline:
	db "\n", 0
.fs_doublequote:
	db CHAR_BACKSLASH, CHAR_DOUBLEQUOTE, 0
.fs_backslash:
	db CHAR_BACKSLASH, CHAR_BACKSLASH, 0

section .text
write_sob_pair:
	push rbp
	mov rbp, rsp

	push rsi
	
	mov rax, 0
	mov rdi, .open_paren
	call printf

	mov rsi, [rsp]

	CAR rsi, rsi
	call write_sob

	mov rsi, [rsp]
	CDR rsi, rsi
	call write_sob_pair_on_cdr
	
	add rsp, 1*8
	
	mov rdi, .close_paren
	mov rax, 0
	call printf

	pop rbp
	ret

section .data
.open_paren:
	db "(", 0
.close_paren:
	db ")", 0

section .text
write_sob_pair_on_cdr:
	push rbp
	mov rbp, rsp

	mov bl, byte [rsi]
	cmp bl, T_NIL
	je .done
	
	cmp bl, T_PAIR
	je .cdrIsPair
	
	push rsi
	
	mov rax, 0
	mov rdi, .dot
	call printf
	
	pop rsi

	call write_sob
	jmp .done

.cdrIsPair:
	CDR rbx, rsi
	push rbx
	CAR rsi, rsi
	push rsi
	
	mov rax, 0
	mov rdi, .space
	call printf
	
	pop rsi
	call write_sob

	pop rsi
	call write_sob_pair_on_cdr

.done:
	pop rbp
	ret

section .data
.space:
	db " ", 0
.dot:
	db " . ", 0

section .text
write_sob_symbol:
	push rbp
	mov rbp, rsp

	SYMBOL_VAL rsi, rsi
	
	STRING_LENGTH rcx, rsi
	STRING_ELEMENTS rax, rsi

	mov rdx, rcx

.loop:
	cmp rcx, 0
	je .done
	mov bl, byte [rax]
	and rbx, 0xff

	cmp rcx, rdx
	jne .ch_simple
	cmp rbx, '+'
	je .ch_hex
	cmp rbx, '-'
	je .ch_hex
	cmp rbx, 'A'
	jl .ch_hex

.ch_simple:
	mov rdi, .fs_simple_char
	mov rsi, rbx
	jmp .printf
	
.ch_hex:
	mov rdi, .fs_hex_char
	mov rsi, rbx

.printf:
	push rax
	push rcx
	mov rax, 0
	call printf
	pop rcx
	pop rax

	dec rcx
	inc rax
	jmp .loop

.done:
	pop rbp
	ret
	
section .data
.fs_simple_char:
	db "%c", 0
.fs_hex_char:
	db "\x%02x;", 0	

section .text
write_sob_closure:
	push rbp
	mov rbp, rsp

	CLOSURE_CODE rdx, rsi
	CLOSURE_ENV rsi, rsi

	mov rdi, .closure
	mov rax, 0
	call printf

	pop rbp
	ret
section .data
.closure:
	db "#<closure [env:%p, code:%p]>", 0

section .text
write_sob_vector:
    push rbp
    mov rbp, rsp

    push rsi

    mov rax, 0
    mov rdi, .vector_open_paren
    call printf

    mov rsi, [rsp]

    SKIP_TYPE_TAG rcx, rsi
    VECTOR_ELEMENTS rax, rsi

.loop:
    cmp rcx, 0
    je .done

    mov rsi, [rax]
    push rax
    push rcx
    call write_sob
    pop rcx
    pop rax

    dec rcx
    jz .done

    push rax
    push rcx
    mov rax, 0
    mov rdi, .vector_space
    call printf
    pop rcx
    pop rax

    add rax, WORD_SIZE
    jmp .loop

.done:
    mov rax, 0
    mov rdi, .vector_close_paren
    call printf

    pop rsi

    pop rbp
    ret

section .data
.vector_open_paren:
    db "#(", 0

.vector_space:
    db " ", 0

.vector_close_paren:
    db ")", 0

section .text
write_sob:
	mov rbx, 0
	mov bl, byte [rsi]	
	jmp qword [.jmp_table + rbx * 8]

section .data
.jmp_table:
	dq write_sob_undefined, write_sob_void, write_sob_nil
	dq write_sob_rational, write_sob_float, write_sob_bool
	dq write_sob_char, write_sob_string, write_sob_symbol
	dq write_sob_closure, write_sob_pair, write_sob_vector

section .text
write_sob_if_not_void:
	mov rsi, rax
	mov bl, byte [rsi]
	cmp bl, T_VOID
	je .continue

	call write_sob
	
	mov rax, 0
	mov rdi, .newline
	call printf
	
.continue:
	ret
section .data
.newline:
	db CHAR_NEWLINE, 0

section .text
car:
    push rbp
    mov rbp, rsp
	mov rax, PVAR(0) ; rax -> pair
	mov rax, [rax + 1] ; rax -> car
	pop rbp
	ret

cdr:
	push rbp
    mov rbp, rsp
	mov rax, PVAR(0) ; rax -> pair
	mov rax, [rax + 9] ; rax -> cdr
	pop rbp
	ret

cons:
	push rbp
    mov rbp, rsp
	mov rbx, PVAR(0) ; rax -> car
	mov rcx, PVAR(1) ; rbx -> cdr
	MAKE_PAIR (rax, rbx, rcx) ; rax -> pair (cons car cdr)
	pop rbp
	ret

set_car:
	push rbp
    mov rbp, rsp
	mov rax, PVAR(0) ; rax -> pair
	mov rbx, PVAR(1) ; rbx -> new car
	mov [rax + 1], rbx ; rax -> old car
	mov rax, (const_tbl); no return value
	pop rbp
	ret

set_cdr:
	push rbp
    mov rbp, rsp
	mov rax, PVAR(0) ; rax -> pair
	mov rbx, PVAR(1) ; rbx -> new cdr
	mov [rax + 9], rbx ; rax -> old cdr
	mov rax, (const_tbl); no return value
	pop rbp
	ret

apply:
	push rbp
    mov rbp, rsp

	;Start of Applic
	push (const_tbl + 1)     ; placeholder for lambdaOpt nil
	mov rbx, num_of_params
	sub rbx, 1

	SOB_LIST_SIZE PVAR(rbx)
	LIST_TO_ARGS PVAR(rbx)
	mov rax, PVAR(0)
	inc rax
	push qword [rax] ;Push rax->env 
	mov rax, qword [rax + 8]
	call rax ;Call rax->code 
	add rsp , 8*1 
	pop rbx 
	lea rsp , [rsp + 8*rbx] 
	add rsp , 8*1                  ; fix the push magic
	;End of applic

	mov rsp, rbp
	pop rbp
	ret
