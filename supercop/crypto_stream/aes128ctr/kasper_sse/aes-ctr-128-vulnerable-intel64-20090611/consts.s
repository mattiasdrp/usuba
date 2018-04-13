# Author: Emilia Käsper and Peter Schwabe
# Date: 2009-03-19
# Public domain

.data

.globl BM31
.globl BM30
.globl BM29
.globl BM28

.globl BM27
.globl BM26
.globl BM25
.globl BM24

.globl BM23
.globl BM22
.globl BM21
.globl BM20

.globl BM19
.globl BM18
.globl BM17
.globl BM16

.globl BM15
.globl BM14
.globl BM13
.globl BM12

.globl BM11
.globl BM10
.globl BM09
.globl BM08

.globl BM07
.globl BM06
.globl BM05
.globl BM04

.globl BM03
.globl BM02
.globl BM01
.globl BM00

.globl REVERS

.globl BIT063
.globl BIT064
.globl BIT127
.globl GCMPOL

.globl SWAP32
.globl M0SWAP
.globl RCON
.globl ROTB
.globl EXPB0
.globl ONE
.globl BS0
.globl BS1
.globl BS2
.globl CTRINC1
.globl CTRINC2
.globl CTRINC3
.globl CTRINC4
.globl CTRINC5
.globl CTRINC6
.globl CTRINC7
.globl RCTRINC1
.globl RCTRINC2
.globl RCTRINC3
.globl RCTRINC4
.globl RCTRINC5
.globl RCTRINC6
.globl RCTRINC7
.globl M0
.globl M0SR
.globl SRM0
.globl SR
.globl PTRMSK

.p2align 6
#.align 16

#.section .rodata

RCON: .int 0x00000000, 0x00000000, 0x00000000, 0xffffffff
ROTB: .int 0x0c000000, 0x00000000, 0x04000000, 0x08000000
EXPB0: .int 0x03030303, 0x07070707, 0x0b0b0b0b, 0x0f0f0f0f
CTRINC1: .int 0x00000001, 0x00000000, 0x00000000, 0x00000000
CTRINC2: .int 0x00000002, 0x00000000, 0x00000000, 0x00000000
CTRINC3: .int 0x00000003, 0x00000000, 0x00000000, 0x00000000
CTRINC4: .int 0x00000004, 0x00000000, 0x00000000, 0x00000000
CTRINC5: .int 0x00000005, 0x00000000, 0x00000000, 0x00000000
CTRINC6: .int 0x00000006, 0x00000000, 0x00000000, 0x00000000
CTRINC7: .int 0x00000007, 0x00000000, 0x00000000, 0x00000000

SWAP32: .int 0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f
RCTRINC1: .int 0x00000000, 0x00000000, 0x00000000, 0x00000001
RCTRINC2: .int 0x00000000, 0x00000000, 0x00000000, 0x00000002
RCTRINC3: .int 0x00000000, 0x00000000, 0x00000000, 0x00000003
RCTRINC4: .int 0x00000000, 0x00000000, 0x00000000, 0x00000004
RCTRINC5: .int 0x00000000, 0x00000000, 0x00000000, 0x00000005
RCTRINC6: .int 0x00000000, 0x00000000, 0x00000000, 0x00000006
RCTRINC7: .int 0x00000000, 0x00000000, 0x00000000, 0x00000007

REVERS: .quad 0x08090A0B0C0D0E0F, 0x0001020304050607

BIT063: .quad 0x0000000000000000, 0x0000000000000001
BIT064: .quad 0x8000000000000000, 0x0000000000000000
BIT127: .quad 0x0000000000000001, 0x0000000000000000
GCMPOL: .quad 0x0000000000000000, 0xE100000000000000

BM31: .quad 0x0000000100000001, 0x0000000100000001
BM30: .quad 0x0000000200000002, 0x0000000200000002
BM29: .quad 0x0000000400000004, 0x0000000400000004
BM28: .quad 0x0000000800000008, 0x0000000800000008

BM27: .quad 0x0000001000000010, 0x0000001000000010
BM26: .quad 0x0000002000000020, 0x0000002000000020
BM25: .quad 0x0000004000000040, 0x0000004000000040
BM24: .quad 0x0000008000000080, 0x0000008000000080

BM23: .quad 0x0000010000000100, 0x0000010000000100
BM22: .quad 0x0000020000000200, 0x0000020000000200
BM21: .quad 0x0000040000000400, 0x0000040000000400
BM20: .quad 0x0000080000000800, 0x0000080000000800

BM19: .quad 0x0000100000001000, 0x0000100000001000
BM18: .quad 0x0000200000002000, 0x0000200000002000
BM17: .quad 0x0000400000004000, 0x0000400000004000
BM16: .quad 0x0000800000008000, 0x0000800000008000

BM15: .quad 0x0001000000010000, 0x0001000000010000
BM14: .quad 0x0002000000020000, 0x0002000000020000
BM13: .quad 0x0004000000040000, 0x0004000000040000
BM12: .quad 0x0008000000080000, 0x0008000000080000

BM11: .quad 0x0010000000100000, 0x0010000000100000
BM10: .quad 0x0020000000200000, 0x0020000000200000
BM09: .quad 0x0040000000400000, 0x0040000000400000
BM08: .quad 0x0080000000800000, 0x0080000000800000

BM07: .quad 0x0100000001000000, 0x0100000001000000
BM06: .quad 0x0200000002000000, 0x0200000002000000
BM05: .quad 0x0400000004000000, 0x0400000004000000
BM04: .quad 0x0800000008000000, 0x0800000008000000

BM03: .quad 0x1000000010000000, 0x1000000010000000
BM02: .quad 0x2000000020000000, 0x2000000020000000
BM01: .quad 0x4000000040000000, 0x4000000040000000
BM00: .quad 0x8000000080000000, 0x8000000080000000

BS0: .quad 0x5555555555555555, 0x5555555555555555
BS1: .quad 0x3333333333333333, 0x3333333333333333
BS2: .quad 0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f
ONE: .quad 0xffffffffffffffff, 0xffffffffffffffff
M0SWAP: .quad 0x0105090d0004080c , 0x03070b0f02060a0e
M0:  .quad 0x02060a0e03070b0f, 0x0004080c0105090d
M0SR:	.quad 0x0a0e02060f03070b, 0x0004080c05090d01
SRM0:	.quad 0x0304090e00050a0f, 0x01060b0c0207080d
SR: .quad 0x0504070600030201, 0x0f0e0d0c0a09080b
PTRMSK: .int 0xfffffff0, 0xffffffff


