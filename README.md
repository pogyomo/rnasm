# rnasm - An Nes Assembler written in Rust

## Specification

### Statement

A statement have either label declaration or instruction, or both.

```asm
label:              // Valid
lda #$00            // Valid
label: lda #$00     // You can combine.
label = 10 lda #$00 // Ok
```

### Identifier

Normally, identifiers start with alphabet and then consists of alphanumeric and underline.

### Label

Label is an identifier that contain value. You can declare label simply put identifier to the beginning of statement. It contains current address.
If it start with '.', it is local label: it alive while new label (not local) is not created.
You can add colon the end of label. It is option.

```asm
Label1 // Valid
Label: // Adding colon is allowed
.local // Local label
Label2:
.local // Valid. Because new label 'Label2' has created.
```

There is another way to declare label. See below example.

```asm
label = 10          // label is equal to 10
label = 10 + 20 / 3 // You can assign expression
label = Another + 2 // You can assign another label
```

### Integer

There is two type of integer: byte and word (8bit and 16bit). Normally, all declaration of integer is word, but you can convert it to byte using prefix '<' or '>'.

```asm
 0x0123 // Word
<0x0123 // Byte. Equal to 0x23
>0x0123 // Byte. Equal to 0x01
```

Also, you can specify the base of integer usign below prefix.

```asm
'0b' or '%' => binary number
'0o' or '0' => Octadecimal
'0x' or '$' => Hexadecimal
no prefix   => Decimal
```

If you want, you can separate it with underline.

```asm
0b0000_0010 // Equal to 0b00000010
0x1_A_2___3 // Number of underlines is not important
0o23_       // End with underline is allowed
```

### Operator

All operator and its order is below.

| order | type          |
| :---: | :-----------: |
| high  | ~, -          |
| ..    | *, /, %       |
| ..    | +, -          |
| ..    | <<, >>        |
| ..    | &             |
| ..    | ^             |
| ..    | \|            |
| low   | <, > (prefix) |

The prefix operator < and > is "Last one win" types operator.

```asm
<1 + 2 // ><(1 + 2) -> >(1 + 2). Winner is >
```

If you add byte and word, the result will be word.

```asm
(<0x00ff) + 0x2300 // Equal to 0x23ff
```

You can use parenthesis to change the order.

```asm
(1 + 2) * 3 // Equal to 1 * 3 + 2 * 3
```

### Comment

You can use both c-style comment and assembler-style comment. Nested comment is valid.

```asm
// A c-style one line comment
/* another c-style comment */
/* /* nested comment is ok */ */
/*
    multi line is ok
*/
; Assembler-style comment
```

### Addressing Mode

Below is syntax of addressing mode.

| Name        | Syntax    |
| ----------- | --------- |
| Accumulator | a         |
| Absolute    | IM16      |
| AbsoluteX   | IM16, x   |
| AbsoluteY   | IM16, y   |
| Immediate   | #IM8      |
| Implied     | Empty     |
| Indirect    | [IM16]    |
| IndirectX   | [IM16, x] |
| IndirectY   | [IM16], y |
| Relative    | @IM16     |
| ZeroPage    | IM8       |
| ZeroPageX   | IM8, x    |
| ZeroPageY   | IM8, y    |
