## Syntax of instruction
The common style is below.
```
<mnemonic> <operand>
```
To represent several addressing mode, this assembler use special prefix (it is different to the prefix 
that is used in expression).

## Identifier
You can assign integer values to identifiers in two ways.
1. Put a identifier to the beginning of line. The identifier will get the current address.
Also, you can add colon the end of identifier, but it is optional.
```
label     // valid
newlabel: // you can use colon
```
2. Using equal sign. You can assign integer, identifier and expression.
```
label    = 20 // good.
newlabel = (label + 0b11) / $F // you can assign expression
```
