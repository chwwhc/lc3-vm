#lang racket

#|
    Virtual Machine state
|#
(define running #t)
(define PC-START #x3000)

#|
    The LC-3 has 65536 memory locations, each of which is 16 bits wide.
|#
(define memory-size (arithmetic-shift 1 16))
(define memory (make-vector memory-size 0))

#|
    The LC-3 has 8 general-purpose registers and 2 special-purpose registers (program counter and condition flag).
    Each register is 16 bits wide.
|#
(define register-count 10) ; 8 general-purpose registers + 2 special-purpose registers
(define R-R0 0)
(define R-R1 1)
(define R-R2 2)
(define R-R3 3)
(define R-R4 4)
(define R-R5 5)
(define R-R6 6)
(define R-R7 7)
(define R-PC 8) ; program counter
(define R-COND 9) ; condition flag
(define register-storage (make-vector register-count 0))

#|
    Memory-mapped registers
|#
(define MR-KBSR #xFE00) ; keyboard status
(define MR-KBDR #xFE02) ; keyboard data

#|
    The LC-3 has 16-bit instructions.
    The first 4 bits are the opcode, and the last 12 bits are the operands.
|#
(define OP-BR #b0000) ; branch
(define OP-ADD #b0001) ; add
(define OP-LD #b0010) ; load
(define OP-ST #b0011) ; store
(define OP-JSR #b0100) ; jump register
(define OP-AND #b0101) ; bitwise and
(define OP-LDR #b0110) ; load register
(define OP-STR #b0111) ; store register
(define OP-RTI #b1000) ; unused
(define OP-NOT #b1001) ; bitwise not
(define OP-LDI #b1010) ; load indirect
(define OP-STI #b1011) ; store indirect
(define OP-JMP #b1100) ; jump
(define OP-RES #b1101) ; reserved (unused)
(define OP-LEA #b1110) ; load effective address
(define OP-TRAP #b1111) ; execute trap

#|
    The R-COND register is used to store the condition code of the last operation.
    The condition code is set to one of the following values:
    1 if the result of the last operation was positive
    0 if the result of the last operation was zero
    -1 if the result of the last operation was negative
|#
(define FL_POS (arithmetic-shift 1 0))
(define FL_ZRO (arithmetic-shift 1 1))
(define FL_NEG (arithmetic-shift 1 2))

#|
    The LC-3 has 256 trap codes.
    The first 16 trap codes are reserved for the operating system.
    The remaining 240 trap codes are available for user programs.
|#
(define TRAP_GETC #x20) ; get a character from the keyboard, not echoed onto the terminal
(define TRAP_OUT #x21) ; output a character
(define TRAP_PUTS #x22) ; output a word string
(define TRAP_IN #x23) ; get a character from the keyboard, echoed onto the terminal
(define TRAP_PUTSP #x24) ; output a byte string
(define TRAP_HALT #x25) ; halt the program

#|
    Update registers
|#
(define (reg-write idx val) (vector-set! register-storage idx (bitwise-and val #xFFFF)))
(define (reg-read idx) (vector-ref register-storage idx))
(define (update-flags reg) (cond [(zero? (reg-read reg)) (reg-write R-COND FL_ZRO)]
                                 [(positive? (reg-read reg)) (reg-write R-COND FL_POS)]
                                 [else (reg-write R-COND FL_NEG)]))

#|
    Read and write memory
|#
(define (mem-write addr val) (vector-set! memory (bitwise-and addr #xFFFF) (bitwise-and val #xFFFF)))
(define (mem-read addr)
  (let [(addr (bitwise-and addr #xFFFF))]   (if (= addr MR-KBSR)
                                                (handle-keyboard)
                                                (vector-ref memory addr))))

#|
    Sign extension is used to convert a (<=16)-bit number into a 16-bit number.
|#
(define (sign-extend x bit-count)
  (cond [(positive? (bitwise-and (arithmetic-shift x (- (sub1 bit-count))) #x1))
         (bitwise-and (bitwise-ior x (arithmetic-shift #xFFFF bit-count)) #xFFFF)]
        [else (bitwise-and x #xFFFF)]))

#|
    Instrcutrions
|#
(define (ADD instr)  ; add
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [r1 (bitwise-and (arithmetic-shift instr -6) #x7)] ; first operand (SR1)
        [imm-flag (bitwise-and (arithmetic-shift instr -5) #x1)])
    (if (zero? imm-flag) ; read from a register
        (let ([r2 (bitwise-and (arithmetic-shift instr -0) #x7)]) ; second operand (SR2)
          (reg-write r0 (+ (reg-read r1) (reg-read r2)))
          (update-flags r0))
        (let ([imm5 (sign-extend (bitwise-and (arithmetic-shift instr -0) #x1F) 5)]) ; 5-bit immediate value
          (reg-write r0 (+ (reg-read r1) imm5))
          (update-flags r0)))))
(define (LDI instr)  ; load indirect
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [pc-offset (sign-extend (bitwise-and (arithmetic-shift instr -0) #x1FF) 9)]) ; 9-bit pc-offset
    (reg-write r0 (mem-read (mem-read (+ (reg-read R-PC) pc-offset) ; add pc to pc-offset to get the final address
                                      (update-flags r0))))))
(define (AND instr)  ; bitwise and
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [r1 (bitwise-and (arithmetic-shift instr -6) #x7)] ; first operand (SR1)
        [imm-flag (bitwise-and (arithmetic-shift instr -5) #x1)])
    (if (zero? imm-flag) ; read from a register
        (let ([r2 (bitwise-and (arithmetic-shift instr -0) #x7)]) ; second operand (SR2)
          (reg-write r0 (bitwise-and (reg-read r1) (reg-read r2)))
          (update-flags r0))
        (let ([imm5 (sign-extend (bitwise-and (arithmetic-shift instr -0) #x1F) 5)]) ; 5-bit immediate value
          (reg-write r0 (bitwise-and (reg-read r1) imm5))
          (update-flags r0)))))
(define (NOT instr)  ; bitwise not
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [r1 (bitwise-and (arithmetic-shift instr -6) #x7)]) ; first operand (SR)
    (reg-write r0 (bitwise-not (reg-read r1)))
    (update-flags r0)))
(define (BR instr)  ; branch
  (let ([pc-offset (sign-extend (bitwise-and instr #x1FF) 9)] ; 9-bit pc-offset
        [cond-flag (bitwise-and (arithmetic-shift instr -9) #x7)]) ; condition flag
    (cond [(bitwise-and (reg-read R-COND) cond-flag)
           (reg-write R-PC (+ (reg-read R-PC) pc-offset))])))
(define (JMP instr)  ; jump, also handles RET
  (let ([r1 (bitwise-and (arithmetic-shift instr -6) #x7)]) ; register (R)
    (reg-write R-PC (reg-read r1))))
(define (JSR instr) ; jump subroutine, also handles JSRR
  (let ([long-flag (bitwise-and (arithmetic-shift instr -11) #x1)])
    (reg-write R-R7 (reg-read R-PC))
    (if (zero? long-flag) ; JSR, 11-bit pc-offset
        (let ([pc-offset (sign-extend (bitwise-and instr #x7FF) 11)]) ; 11-bit pc-offset
          reg-write R-PC (+ (reg-read R-PC) pc-offset))
        (let ([r1 (bitwise-and (arithmetic-shift instr -6) #x7)]) ; JSRR, register (R)
          reg-write R-PC (reg-read r1)))))
(define (LD instr) ; load
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [pc-offset (sign-extend (bitwise-and instr #x1FF) 9)]) ; 9-bit pc-offset
    (reg-write r0 (mem-read (+ (reg-read R-PC) pc-offset))) ; add pc to pc-offset to get the final address
    (update-flags r0)))
(define (LDR instr)  ; load register
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [r1 (bitwise-and (arithmetic-shift instr -6) #x7)] ; base register (BR)
        [offset6 (sign-extend (bitwise-and instr #x3F) 6)]) ; 6-bit offset
    (reg-write r0 (mem-read (+ (reg-read r1) offset6) ; add base register to offset to get the final address
                            (update-flags r0)))))
(define (LEA instr) ; load effective address
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; destination register (DR)
        [pc-offset (sign-extend (bitwise-and instr #x1FF) 9)]) ; 9-bit pc-offset
    (reg-write r0 (+ (reg-read R-PC) pc-offset)) ; add pc to pc-offset to get the final address
    (update-flags r0)))
(define (ST instr)  ; store
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; source register (SR)
        [pc-offset (sign-extend (bitwise-and instr #x1FF) 9)]) ; 9-bit pc-offset
    (mem-write (+ (reg-read R-PC) pc-offset) ; add pc to pc-offset to get the final address
               (reg-read r0))))
(define (STI instr)  ; store indirect
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; source register (SR)
        [pc-offset (sign-extend (bitwise-and instr #x1FF) 9)]) ; 9-bit pc-offset
    (mem-write (mem-read (+ (reg-read R-PC) pc-offset) ; use the memory pointed by the final address
                         (update-flags r0))
               (reg-read r0))))
(define (STR instr)  ; store register
  (let ([r0 (bitwise-and (arithmetic-shift instr -9) #x7)] ; source register (SR)
        [r1 (bitwise-and (arithmetic-shift instr -6) #x7)] ; base register (BR)
        [offset6 (sign-extend (bitwise-and instr #x3F) 6)]) ; 6-bit offset
    (mem-write (+ (reg-read r1) offset6) ; add base register to offset to get the final address
               (reg-read r0))))

#|
    Traps
|#
(define (PUTS) ; output a string terminated by a null character
  (letrec ([write-char-iter (lambda (addr)
                              (unless (zero? (mem-read addr))
                                (display (integer->char (mem-read addr)))
                                (write-char-iter (add1 addr))))])
    (write-char-iter (reg-read R-R0))
    (flush-output)))
(define (GETC) ; input a character
  (reg-write R-R0 (char->integer (read-char))))
(define (OUT)  ; output a character
  (display (integer->char (reg-read R-R0)))
  (flush-output))
(define (IN)  ; input a character
  (display "Enter a character: ")
  (reg-write R-R0 (char->integer (read-char)))
  (update-flags R-R0))
(define (PUTSP)  ; output a string of space-separated integers terminated by a null character
  (let loop ([addr (reg-read R-R0)]) ; address of the string
    (when (not (zero? (mem-read addr))) ; if the character is not null
      (display (integer->char (bitwise-and (mem-read addr) #xFF))) ; output the first character
      (display (integer->char (bitwise-and (arithmetic-shift (mem-read addr) -8) #xFF))) ; output the second character
      (loop (+ addr 1))))
  (flush-output))
(define (HALT)  ; halt
  (set! running #f)
  (flush-output))

#|
    Read the source file.
    Note that LC-3 uses big-endian, whereas most common computers use little-endian.
|#
(define (swap16 two-bytes) ; swap the two bytes in a 16-bit word
  (let [(low-byte (bytes-ref two-bytes 1)) ; get the low byte
        (high-byte (bytes-ref two-bytes 0))] ; get the high byte
    (bitwise-ior (arithmetic-shift high-byte 8) low-byte)))
(define (handle-keyboard) ; handle keyboard interrupts
  (let [(buffer (read-byte))]
    (if (not (eof-object? buffer))
        (begin
          (mem-write MR-KBSR (bitwise-ior (arithmetic-shift 1 15)))
          (mem-write MR-KBDR (integer->char buffer)))
        (mem-write MR-KBSR 0))))
(define (read-two-bytes in-port) ; read two bytes from the input port
  (let [(two-bytes (read-bytes 2 in-port))]
    (cond
      [(bytes? two-bytes) (swap16 two-bytes)]
      [else eof])))
(define (read-image-file in-port)
  (let [(origin (read-two-bytes in-port))] ; read the origin
    (let loop ([address origin]) ; read the image
      (let [(two-bytes (read-two-bytes in-port))]
        (if (eof-object? two-bytes)
            'done
            (begin
              (mem-write address two-bytes)
              (loop (+ address 1))))))))

#|
    Execute a trap
|#
(define (execute-trap trap)
  (reg-write R-R7 (reg-read R-PC)) ; save the return address
  (cond
    [(= trap TRAP_GETC)
     (begin (displayln "GETC")
            (GETC))]
    [(= trap TRAP_OUT)
     (begin (displayln "OUT")
            (OUT))]
    [(= trap TRAP_PUTS)
     (begin (displayln "PUTS")
            (PUTS))]
    [(= trap TRAP_IN)
     (begin (displayln "IN")
            (IN))]
    [(= trap TRAP_PUTSP)
     (begin (displayln "PUTSP")
            (PUTSP))]
    [(= trap TRAP_HALT)
     (begin (displayln "HALT")
            (HALT))]))

#|
    Execute an instruction
|#
(define (execute instr)
  (let ([opcode (bitwise-and (arithmetic-shift instr -12) #xF)]) ; opcode
    (cond
      [(= opcode OP-BR)
       (begin (displayln (string-append "br " (number->string instr)))
              (BR instr))]
      [(= opcode OP-ADD)
       (begin (displayln "add")
              (ADD instr))]
      [(= opcode OP-LD)
       (begin (displayln "ld")
              (LD instr))]
      [(= opcode OP-ST)
       (begin (displayln "st")
              (ST instr))]
      [(= opcode OP-JSR)
       (begin (displayln "jsr")
              (JSR instr))]
      [(= opcode OP-AND)
       (begin (displayln "and")
              (AND instr))]
      [(= opcode OP-LDR)
       (begin (displayln "ldr")
              (LDR instr))]
      [(= opcode OP-STR)
       (begin (displayln "str")
              (STR instr))]
      [(= opcode OP-NOT)
       (begin (displayln "not")
              (NOT instr))]
      [(= opcode OP-LDI)
       (begin (displayln "ldi")
              (LDI instr))]
      [(= opcode OP-STI)
       (begin (displayln "sti")
              (STI instr))]
      [(= opcode OP-JMP)
       (begin (displayln "jmp")
              (JMP instr))]
      [(= opcode OP-LEA)
       (begin (displayln "lea")
              (LEA instr))]
      [(= opcode OP-TRAP)
       (execute-trap (bitwise-and instr #xFF))]
      [else (displayln OP-LD) (displayln "Invalid or unused opcode") (set! running #F)])))

#|
    Main
|#
(define (main)
  (let ([obj-file-to-run (command-line ; get the object file to run
                          #:program "LC-3 Virtual Machine"
                          #:args (filename)
                          filename)])  (call-with-input-file obj-file-to-run #:mode 'binary read-image-file) ; read the object file
    (reg-write R-PC PC-START)
    (do ()
      ((not running)) ; continue while running is true
      (let ([instr (mem-read (reg-read R-PC))])
        (reg-write R-PC (add1 (reg-read R-PC)))
        (execute instr)))))

(main)