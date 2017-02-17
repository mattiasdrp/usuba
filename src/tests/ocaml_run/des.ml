open Ocaml_runtime
let sbox_1 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a4) in 
    let x2 = lnot (a1) in 
    let x3 = (a3) lxor (a4) in 
    let x4 = (x2) lxor (x3) in 
    let x5 = (x2) lor (a3) in 
    let x6 = (x1) land (x5) in 
    let x7 = (x6) lor (a6) in 
    let x8 = (x7) lxor (x4) in 
    let x9 = (x2) lor (x1) in 
    let x10 = (x9) land (a6) in 
    let x11 = (x10) lxor (x7) in 
    let x12 = (x11) lor (a2) in 
    let x13 = (x12) lxor (x8) in 
    let x14 = (x13) lxor (x9) in 
    let x15 = (x14) lor (a6) in 
    let x16 = (x15) lxor (x1) in 
    let x17 = lnot (x14) in 
    let x18 = (x3) land (x17) in 
    let x19 = (x18) lor (a2) in 
    let x20 = (x19) lxor (x16) in 
    let x21 = (x20) lor (a5) in 
    let x22 = (x21) lxor (x13) in 
    let out4 = x22 in 
    let x23 = (x4) lor (a3) in 
    let x24 = lnot (x23) in 
    let x25 = (x24) lor (a6) in 
    let x26 = (x25) lxor (x6) in 
    let x27 = (x8) land (x1) in 
    let x28 = (x27) lor (a2) in 
    let x29 = (x28) lxor (x26) in 
    let x30 = (x8) lor (x1) in 
    let x31 = (x6) lxor (x30) in 
    let x32 = (x14) land (x5) in 
    let x33 = (x8) lxor (x32) in 
    let x34 = (x33) land (a2) in 
    let x35 = (x34) lxor (x31) in 
    let x36 = (x35) lor (a5) in 
    let x37 = (x36) lxor (x29) in 
    let out1 = x37 in 
    let x38 = (x10) land (a3) in 
    let x39 = (x4) lor (x38) in 
    let x40 = (x33) land (a3) in 
    let x41 = (x25) lxor (x40) in 
    let x42 = (x41) lor (a2) in 
    let x43 = (x42) lxor (x39) in 
    let x44 = (x26) lor (a3) in 
    let x45 = (x14) lxor (x44) in 
    let x46 = (x8) lor (a1) in 
    let x47 = (x20) lxor (x46) in 
    let x48 = (x47) lor (a2) in 
    let x49 = (x48) lxor (x45) in 
    let x50 = (x49) land (a5) in 
    let x51 = (x50) lxor (x43) in 
    let out2 = x51 in 
    let x52 = (x40) lxor (x8) in 
    let x53 = (x11) lxor (a3) in 
    let x54 = (x5) land (x53) in 
    let x55 = (x54) lor (a2) in 
    let x56 = (x55) lxor (x52) in 
    let x57 = (x4) lor (a6) in 
    let x58 = (x38) lxor (x57) in 
    let x59 = (x56) land (x13) in 
    let x60 = (x59) land (a2) in 
    let x61 = (x60) lxor (x58) in 
    let x62 = (x61) land (a5) in 
    let x63 = (x62) lxor (x56) in 
    let out3 = x63 in 
    (out1,out2,out3,out4)


let sbox_2 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a5) in 
    let x2 = lnot (a1) in 
    let x3 = (a6) lxor (a5) in 
    let x4 = (x2) lxor (x3) in 
    let x5 = (a2) lxor (x4) in 
    let x6 = (x1) lor (a6) in 
    let x7 = (x2) lor (x6) in 
    let x8 = (x7) land (a2) in 
    let x9 = (x8) lxor (a6) in 
    let x10 = (x9) land (a3) in 
    let x11 = (x10) lxor (x5) in 
    let x12 = (x9) land (a2) in 
    let x13 = (x6) lxor (a5) in 
    let x14 = (x13) lor (a3) in 
    let x15 = (x14) lxor (x12) in 
    let x16 = (x15) land (a4) in 
    let x17 = (x16) lxor (x11) in 
    let out2 = x17 in 
    let x18 = (a1) lor (a5) in 
    let x19 = (x18) lor (a6) in 
    let x20 = (x19) lxor (x13) in 
    let x21 = (a2) lxor (x20) in 
    let x22 = (x4) lor (a6) in 
    let x23 = (x17) land (x22) in 
    let x24 = (x23) lor (a3) in 
    let x25 = (x24) lxor (x21) in 
    let x26 = (x2) lor (a6) in 
    let x27 = (x2) land (a5) in 
    let x28 = (x27) lor (a2) in 
    let x29 = (x28) lxor (x26) in 
    let x30 = (x27) lxor (x3) in 
    let x31 = (x19) lxor (x2) in 
    let x32 = (x31) land (a2) in 
    let x33 = (x32) lxor (x30) in 
    let x34 = (x33) land (a3) in 
    let x35 = (x34) lxor (x29) in 
    let x36 = (x35) lor (a4) in 
    let x37 = (x36) lxor (x25) in 
    let out3 = x37 in 
    let x38 = (x32) land (x21) in 
    let x39 = (x5) lxor (x38) in 
    let x40 = (x15) lor (a1) in 
    let x41 = (x13) lxor (x40) in 
    let x42 = (x41) lor (a3) in 
    let x43 = (x42) lxor (x39) in 
    let x44 = (x41) lor (x28) in 
    let x45 = (x44) land (a4) in 
    let x46 = (x45) lxor (x43) in 
    let out1 = x46 in 
    let x47 = (x21) land (x19) in 
    let x48 = (x26) lxor (x47) in 
    let x49 = (x33) land (a2) in 
    let x50 = (x21) lxor (x49) in 
    let x51 = (x50) land (a3) in 
    let x52 = (x51) lxor (x48) in 
    let x53 = (x28) land (x18) in 
    let x54 = (x50) land (x53) in 
    let x55 = (x54) lor (a4) in 
    let x56 = (x55) lxor (x52) in 
    let out4 = x56 in 
    (out1,out2,out3,out4)


let sbox_3 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a5) in 
    let x2 = lnot (a6) in 
    let x3 = (a3) land (a5) in 
    let x4 = (a6) lxor (x3) in 
    let x5 = (x1) land (a4) in 
    let x6 = (x5) lxor (x4) in 
    let x7 = (a2) lxor (x6) in 
    let x8 = (x1) land (a3) in 
    let x9 = (x2) lxor (a5) in 
    let x10 = (x9) lor (a4) in 
    let x11 = (x10) lxor (x8) in 
    let x12 = (x11) land (x7) in 
    let x13 = (x11) lxor (a5) in 
    let x14 = (x7) lor (x13) in 
    let x15 = (x14) land (a4) in 
    let x16 = (x15) lxor (x12) in 
    let x17 = (x16) land (a2) in 
    let x18 = (x17) lxor (x11) in 
    let x19 = (x18) land (a1) in 
    let x20 = (x19) lxor (x7) in 
    let out4 = x20 in 
    let x21 = (a4) lxor (a3) in 
    let x22 = (x9) lxor (x21) in 
    let x23 = (x4) lor (x2) in 
    let x24 = (x8) lxor (x23) in 
    let x25 = (x24) lor (a2) in 
    let x26 = (x25) lxor (x22) in 
    let x27 = (x23) lxor (a6) in 
    let x28 = (a4) lor (x27) in 
    let x29 = (x15) lxor (a3) in 
    let x30 = (x5) lor (x29) in 
    let x31 = (x30) lor (a2) in 
    let x32 = (x31) lxor (x28) in 
    let x33 = (x32) lor (a1) in 
    let x34 = (x33) lxor (x26) in 
    let out1 = x34 in 
    let x35 = (x9) lxor (a3) in 
    let x36 = (x5) lor (x35) in 
    let x37 = (x29) lor (x4) in 
    let x38 = (a4) lxor (x37) in 
    let x39 = (x38) lor (a2) in 
    let x40 = (x39) lxor (x36) in 
    let x41 = (x11) land (a6) in 
    let x42 = (x6) lor (x41) in 
    let x43 = (x38) lxor (x34) in 
    let x44 = (x41) lxor (x43) in 
    let x45 = (x44) land (a2) in 
    let x46 = (x45) lxor (x42) in 
    let x47 = (x46) lor (a1) in 
    let x48 = (x47) lxor (x40) in 
    let out3 = x48 in 
    let x49 = (x38) lor (x2) in 
    let x50 = (x13) lxor (x49) in 
    let x51 = (x28) lxor (x27) in 
    let x52 = (x51) lor (a2) in 
    let x53 = (x52) lxor (x50) in 
    let x54 = (x23) land (x12) in 
    let x55 = (x52) land (x54) in 
    let x56 = (x55) lor (a1) in 
    let x57 = (x56) lxor (x53) in 
    let out2 = x57 in 
    (out1,out2,out3,out4)


let sbox_4 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a1) in 
    let x2 = lnot (a3) in 
    let x3 = (a3) lor (a1) in 
    let x4 = (x3) land (a5) in 
    let x5 = (x4) lxor (x1) in 
    let x6 = (a3) lor (a2) in 
    let x7 = (x6) lxor (x5) in 
    let x8 = (a5) land (a1) in 
    let x9 = (x3) lxor (x8) in 
    let x10 = (x9) land (a2) in 
    let x11 = (x10) lxor (a5) in 
    let x12 = (x11) land (a4) in 
    let x13 = (x12) lxor (x7) in 
    let x14 = (x4) lxor (x2) in 
    let x15 = (x14) land (a2) in 
    let x16 = (x15) lxor (x9) in 
    let x17 = (x14) land (x5) in 
    let x18 = (x2) lxor (a5) in 
    let x19 = (x18) lor (a2) in 
    let x20 = (x19) lxor (x17) in 
    let x21 = (x20) lor (a4) in 
    let x22 = (x21) lxor (x16) in 
    let x23 = (x22) land (a6) in 
    let x24 = (x23) lxor (x13) in 
    let out2 = x24 in 
    let x25 = lnot (x13) in 
    let x26 = (x22) lor (a6) in 
    let x27 = (x26) lxor (x25) in 
    let out1 = x27 in 
    let x28 = (x11) land (a2) in 
    let x29 = (x17) lxor (x28) in 
    let x30 = (x10) lxor (a3) in 
    let x31 = (x19) lxor (x30) in 
    let x32 = (x31) land (a4) in 
    let x33 = (x32) lxor (x29) in 
    let x34 = (x33) lxor (x25) in 
    let x35 = (x34) land (a2) in 
    let x36 = (x35) lxor (x24) in 
    let x37 = (x34) lor (a4) in 
    let x38 = (x37) lxor (x36) in 
    let x39 = (x38) land (a6) in 
    let x40 = (x39) lxor (x33) in 
    let out4 = x40 in 
    let x41 = (x38) lxor (x26) in 
    let x42 = (x40) lxor (x41) in 
    let out3 = x42 in 
    (out1,out2,out3,out4)


let sbox_5 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a6) in 
    let x2 = lnot (a3) in 
    let x3 = (x2) lor (x1) in 
    let x4 = (a4) lxor (x3) in 
    let x5 = (x3) land (a1) in 
    let x6 = (x5) lxor (x4) in 
    let x7 = (a4) lor (a6) in 
    let x8 = (a3) lxor (x7) in 
    let x9 = (x7) lor (a3) in 
    let x10 = (x9) lor (a1) in 
    let x11 = (x10) lxor (x8) in 
    let x12 = (x11) land (a5) in 
    let x13 = (x12) lxor (x6) in 
    let x14 = lnot (x4) in 
    let x15 = (a6) land (x14) in 
    let x16 = (x15) lor (a1) in 
    let x17 = (x16) lxor (x8) in 
    let x18 = (x17) lor (a5) in 
    let x19 = (x18) lxor (x10) in 
    let x20 = (x19) lor (a2) in 
    let x21 = (x20) lxor (x13) in 
    let out3 = x21 in 
    let x22 = (x15) lor (x2) in 
    let x23 = (a6) lxor (x22) in 
    let x24 = (x22) lxor (a4) in 
    let x25 = (x24) land (a1) in 
    let x26 = (x25) lxor (x23) in 
    let x27 = (x11) lxor (a1) in 
    let x28 = (x22) land (x27) in 
    let x29 = (x28) lor (a5) in 
    let x30 = (x29) lxor (x26) in 
    let x31 = (x27) lor (a4) in 
    let x32 = lnot (x31) in 
    let x33 = (x32) lor (a2) in 
    let x34 = (x33) lxor (x30) in 
    let out2 = x34 in 
    let x35 = (x15) lxor (x2) in 
    let x36 = (x35) land (a1) in 
    let x37 = (x36) lxor (x14) in 
    let x38 = (x7) lxor (x5) in 
    let x39 = (x34) land (x38) in 
    let x40 = (x39) lor (a5) in 
    let x41 = (x40) lxor (x37) in 
    let x42 = (x5) lxor (x2) in 
    let x43 = (x16) land (x42) in 
    let x44 = (x27) land (x4) in 
    let x45 = (x44) land (a5) in 
    let x46 = (x45) lxor (x43) in 
    let x47 = (x46) lor (a2) in 
    let x48 = (x47) lxor (x41) in 
    let out1 = x48 in 
    let x49 = (x48) land (x24) in 
    let x50 = (x5) lxor (x49) in 
    let x51 = (x30) lxor (x11) in 
    let x52 = (x50) lor (x51) in 
    let x53 = (x52) land (a5) in 
    let x54 = (x53) lxor (x50) in 
    let x55 = (x19) lxor (x14) in 
    let x56 = (x34) lxor (x55) in 
    let x57 = (x16) lxor (x4) in 
    let x58 = (x30) land (x57) in 
    let x59 = (x58) land (a5) in 
    let x60 = (x59) lxor (x56) in 
    let x61 = (x60) lor (a2) in 
    let x62 = (x61) lxor (x54) in 
    let out4 = x62 in 
    (out1,out2,out3,out4)


let sbox_6 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a2) in 
    let x2 = lnot (a5) in 
    let x3 = (a6) lxor (a2) in 
    let x4 = (x2) lxor (x3) in 
    let x5 = (a1) lxor (x4) in 
    let x6 = (a6) land (a5) in 
    let x7 = (x1) lor (x6) in 
    let x8 = (x5) land (a5) in 
    let x9 = (x8) land (a1) in 
    let x10 = (x9) lxor (x7) in 
    let x11 = (x10) land (a4) in 
    let x12 = (x11) lxor (x5) in 
    let x13 = (x10) lxor (a6) in 
    let x14 = (a1) land (x13) in 
    let x15 = (a6) land (a2) in 
    let x16 = (a5) lxor (x15) in 
    let x17 = (x16) land (a1) in 
    let x18 = (x17) lxor (x2) in 
    let x19 = (x18) lor (a4) in 
    let x20 = (x19) lxor (x14) in 
    let x21 = (x20) land (a3) in 
    let x22 = (x21) lxor (x12) in 
    let out2 = x22 in 
    let x23 = (x18) lxor (a6) in 
    let x24 = (x23) land (a1) in 
    let x25 = (x24) lxor (a5) in 
    let x26 = (x17) lxor (a2) in 
    let x27 = (x6) lor (x26) in 
    let x28 = (x27) land (a4) in 
    let x29 = (x28) lxor (x25) in 
    let x30 = lnot (x26) in 
    let x31 = (x29) lor (a6) in 
    let x32 = lnot (x31) in 
    let x33 = (x32) land (a4) in 
    let x34 = (x33) lxor (x30) in 
    let x35 = (x34) land (a3) in 
    let x36 = (x35) lxor (x29) in 
    let out4 = x36 in 
    let x37 = (x34) lxor (x6) in 
    let x38 = (x23) land (a5) in 
    let x39 = (x5) lxor (x38) in 
    let x40 = (x39) lor (a4) in 
    let x41 = (x40) lxor (x37) in 
    let x42 = (x24) lor (x16) in 
    let x43 = (x1) lxor (x42) in 
    let x44 = (x24) lxor (x15) in 
    let x45 = (x31) lxor (x44) in 
    let x46 = (x45) lor (a4) in 
    let x47 = (x46) lxor (x43) in 
    let x48 = (x47) lor (a3) in 
    let x49 = (x48) lxor (x41) in 
    let out1 = x49 in 
    let x50 = (x38) lor (x5) in 
    let x51 = (x6) lxor (x50) in 
    let x52 = (x31) land (x8) in 
    let x53 = (x52) lor (a4) in 
    let x54 = (x53) lxor (x51) in 
    let x55 = (x43) land (x30) in 
    let x56 = (x55) lor (a3) in 
    let x57 = (x56) lxor (x54) in 
    let out3 = x57 in 
    (out1,out2,out3,out4)


let sbox_7 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a2) in 
    let x2 = lnot (a5) in 
    let x3 = (a4) land (a2) in 
    let x4 = (a5) lxor (x3) in 
    let x5 = (a3) lxor (x4) in 
    let x6 = (x4) land (a4) in 
    let x7 = (a2) lxor (x6) in 
    let x8 = (x7) land (a3) in 
    let x9 = (x8) lxor (a1) in 
    let x10 = (x9) lor (a6) in 
    let x11 = (x10) lxor (x5) in 
    let x12 = (x2) land (a4) in 
    let x13 = (a2) lor (x12) in 
    let x14 = (x2) lor (a2) in 
    let x15 = (x14) land (a3) in 
    let x16 = (x15) lxor (x13) in 
    let x17 = (x11) lxor (x6) in 
    let x18 = (x17) lor (a6) in 
    let x19 = (x18) lxor (x16) in 
    let x20 = (x19) land (a1) in 
    let x21 = (x20) lxor (x11) in 
    let out1 = x21 in 
    let x22 = (x21) lor (a2) in 
    let x23 = (x6) lxor (x22) in 
    let x24 = (x15) lxor (x23) in 
    let x25 = (x6) lxor (x5) in 
    let x26 = (x12) lor (x25) in 
    let x27 = (x26) lor (a6) in 
    let x28 = (x27) lxor (x24) in 
    let x29 = (x19) land (x1) in 
    let x30 = (x26) land (x23) in 
    let x31 = (x30) land (a6) in 
    let x32 = (x31) lxor (x29) in 
    let x33 = (x32) lor (a1) in 
    let x34 = (x33) lxor (x28) in 
    let out4 = x34 in 
    let x35 = (x16) land (a4) in 
    let x36 = (x1) lor (x35) in 
    let x37 = (x36) land (a6) in 
    let x38 = (x37) lxor (x11) in 
    let x39 = (x13) land (a4) in 
    let x40 = (x7) lor (a3) in 
    let x41 = (x40) lxor (x39) in 
    let x42 = (x24) lor (x1) in 
    let x43 = (x42) lor (a6) in 
    let x44 = (x43) lxor (x41) in 
    let x45 = (x44) lor (a1) in 
    let x46 = (x45) lxor (x38) in 
    let out2 = x46 in 
    let x47 = (x44) lxor (x8) in 
    let x48 = (x15) lxor (x6) in 
    let x49 = (x48) lor (a6) in 
    let x50 = (x49) lxor (x47) in 
    let x51 = (x44) lxor (x19) in 
    let x52 = (x25) lxor (a4) in 
    let x53 = (x46) land (x52) in 
    let x54 = (x53) land (a6) in 
    let x55 = (x54) lxor (x51) in 
    let x56 = (x55) lor (a1) in 
    let x57 = (x56) lxor (x50) in 
    let out3 = x57 in 
    (out1,out2,out3,out4)


let sbox_8 a1 a2 a3 a4 a5 a6 = 
    let x1 = lnot (a1) in 
    let x2 = lnot (a4) in 
    let x3 = (x1) lxor (a3) in 
    let x4 = (x1) lor (a3) in 
    let x5 = (x2) lxor (x4) in 
    let x6 = (x5) lor (a5) in 
    let x7 = (x6) lxor (x3) in 
    let x8 = (x5) lor (x1) in 
    let x9 = (x8) lxor (x2) in 
    let x10 = (x9) land (a5) in 
    let x11 = (x10) lxor (x8) in 
    let x12 = (x11) land (a2) in 
    let x13 = (x12) lxor (x7) in 
    let x14 = (x9) lxor (x6) in 
    let x15 = (x9) land (x3) in 
    let x16 = (x8) land (a5) in 
    let x17 = (x16) lxor (x15) in 
    let x18 = (x17) lor (a2) in 
    let x19 = (x18) lxor (x14) in 
    let x20 = (x19) lor (a6) in 
    let x21 = (x20) lxor (x13) in 
    let out1 = x21 in 
    let x22 = (x3) lor (a5) in 
    let x23 = (x2) land (x22) in 
    let x24 = lnot (a3) in 
    let x25 = (x8) land (x24) in 
    let x26 = (x4) land (a5) in 
    let x27 = (x26) lxor (x25) in 
    let x28 = (x27) lor (a2) in 
    let x29 = (x28) lxor (x23) in 
    let x30 = (x29) land (a6) in 
    let x31 = (x30) lxor (x13) in 
    let out4 = x31 in 
    let x32 = (x6) lxor (x5) in 
    let x33 = (x22) lxor (x32) in 
    let x34 = (x13) lor (a4) in 
    let x35 = (x34) land (a2) in 
    let x36 = (x35) lxor (x33) in 
    let x37 = (x33) land (a1) in 
    let x38 = (x8) lxor (x37) in 
    let x39 = (x23) lxor (a1) in 
    let x40 = (x7) land (x39) in 
    let x41 = (x40) land (a2) in 
    let x42 = (x41) lxor (x38) in 
    let x43 = (x42) lor (a6) in 
    let x44 = (x43) lxor (x36) in 
    let out3 = x44 in 
    let x45 = (x10) lxor (a1) in 
    let x46 = (x22) lxor (x45) in 
    let x47 = lnot (x7) in 
    let x48 = (x8) land (x47) in 
    let x49 = (x48) lor (a2) in 
    let x50 = (x49) lxor (x46) in 
    let x51 = (x29) lxor (x19) in 
    let x52 = (x38) lor (x51) in 
    let x53 = (x52) land (a6) in 
    let x54 = (x53) lxor (x50) in 
    let out2 = x54 in 
    (out1,out2,out3,out4)


let expand a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 = 
    let out1 = a32 in 
    let out2 = a1 in 
    let out3 = a2 in 
    let out4 = a3 in 
    let out5 = a4 in 
    let out6 = a5 in 
    let out7 = a4 in 
    let out8 = a5 in 
    let out9 = a6 in 
    let out10 = a7 in 
    let out11 = a8 in 
    let out12 = a9 in 
    let out13 = a8 in 
    let out14 = a9 in 
    let out15 = a10 in 
    let out16 = a11 in 
    let out17 = a12 in 
    let out18 = a13 in 
    let out19 = a12 in 
    let out20 = a13 in 
    let out21 = a14 in 
    let out22 = a15 in 
    let out23 = a16 in 
    let out24 = a17 in 
    let out25 = a16 in 
    let out26 = a17 in 
    let out27 = a18 in 
    let out28 = a19 in 
    let out29 = a20 in 
    let out30 = a21 in 
    let out31 = a20 in 
    let out32 = a21 in 
    let out33 = a22 in 
    let out34 = a23 in 
    let out35 = a24 in 
    let out36 = a25 in 
    let out37 = a24 in 
    let out38 = a25 in 
    let out39 = a26 in 
    let out40 = a27 in 
    let out41 = a28 in 
    let out42 = a29 in 
    let out43 = a28 in 
    let out44 = a29 in 
    let out45 = a30 in 
    let out46 = a31 in 
    let out47 = a32 in 
    let out48 = a1 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48)


let init_p a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 = 
    let out1 = a58 in 
    let out2 = a50 in 
    let out3 = a42 in 
    let out4 = a34 in 
    let out5 = a26 in 
    let out6 = a18 in 
    let out7 = a10 in 
    let out8 = a2 in 
    let out9 = a60 in 
    let out10 = a52 in 
    let out11 = a44 in 
    let out12 = a36 in 
    let out13 = a28 in 
    let out14 = a20 in 
    let out15 = a12 in 
    let out16 = a4 in 
    let out17 = a62 in 
    let out18 = a54 in 
    let out19 = a46 in 
    let out20 = a38 in 
    let out21 = a30 in 
    let out22 = a22 in 
    let out23 = a14 in 
    let out24 = a6 in 
    let out25 = a64 in 
    let out26 = a56 in 
    let out27 = a48 in 
    let out28 = a40 in 
    let out29 = a32 in 
    let out30 = a24 in 
    let out31 = a16 in 
    let out32 = a8 in 
    let out33 = a57 in 
    let out34 = a49 in 
    let out35 = a41 in 
    let out36 = a33 in 
    let out37 = a25 in 
    let out38 = a17 in 
    let out39 = a9 in 
    let out40 = a1 in 
    let out41 = a59 in 
    let out42 = a51 in 
    let out43 = a43 in 
    let out44 = a35 in 
    let out45 = a27 in 
    let out46 = a19 in 
    let out47 = a11 in 
    let out48 = a3 in 
    let out49 = a61 in 
    let out50 = a53 in 
    let out51 = a45 in 
    let out52 = a37 in 
    let out53 = a29 in 
    let out54 = a21 in 
    let out55 = a13 in 
    let out56 = a5 in 
    let out57 = a63 in 
    let out58 = a55 in 
    let out59 = a47 in 
    let out60 = a39 in 
    let out61 = a31 in 
    let out62 = a23 in 
    let out63 = a15 in 
    let out64 = a7 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48,out49,out50,out51,out52,out53,out54,out55,out56,out57,out58,out59,out60,out61,out62,out63,out64)


let final_p a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 = 
    let out1 = a40 in 
    let out2 = a8 in 
    let out3 = a48 in 
    let out4 = a16 in 
    let out5 = a56 in 
    let out6 = a24 in 
    let out7 = a64 in 
    let out8 = a32 in 
    let out9 = a39 in 
    let out10 = a7 in 
    let out11 = a47 in 
    let out12 = a15 in 
    let out13 = a55 in 
    let out14 = a23 in 
    let out15 = a63 in 
    let out16 = a31 in 
    let out17 = a38 in 
    let out18 = a6 in 
    let out19 = a46 in 
    let out20 = a14 in 
    let out21 = a54 in 
    let out22 = a22 in 
    let out23 = a62 in 
    let out24 = a30 in 
    let out25 = a37 in 
    let out26 = a5 in 
    let out27 = a45 in 
    let out28 = a13 in 
    let out29 = a53 in 
    let out30 = a21 in 
    let out31 = a61 in 
    let out32 = a29 in 
    let out33 = a36 in 
    let out34 = a4 in 
    let out35 = a44 in 
    let out36 = a12 in 
    let out37 = a52 in 
    let out38 = a20 in 
    let out39 = a60 in 
    let out40 = a28 in 
    let out41 = a35 in 
    let out42 = a3 in 
    let out43 = a43 in 
    let out44 = a11 in 
    let out45 = a51 in 
    let out46 = a19 in 
    let out47 = a59 in 
    let out48 = a27 in 
    let out49 = a34 in 
    let out50 = a2 in 
    let out51 = a42 in 
    let out52 = a10 in 
    let out53 = a50 in 
    let out54 = a18 in 
    let out55 = a58 in 
    let out56 = a26 in 
    let out57 = a33 in 
    let out58 = a1 in 
    let out59 = a41 in 
    let out60 = a9 in 
    let out61 = a49 in 
    let out62 = a17 in 
    let out63 = a57 in 
    let out64 = a25 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48,out49,out50,out51,out52,out53,out54,out55,out56,out57,out58,out59,out60,out61,out62,out63,out64)


let permut a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 = 
    let out1 = a16 in 
    let out2 = a7 in 
    let out3 = a20 in 
    let out4 = a21 in 
    let out5 = a29 in 
    let out6 = a12 in 
    let out7 = a28 in 
    let out8 = a17 in 
    let out9 = a1 in 
    let out10 = a15 in 
    let out11 = a23 in 
    let out12 = a26 in 
    let out13 = a5 in 
    let out14 = a18 in 
    let out15 = a31 in 
    let out16 = a10 in 
    let out17 = a2 in 
    let out18 = a8 in 
    let out19 = a24 in 
    let out20 = a14 in 
    let out21 = a32 in 
    let out22 = a27 in 
    let out23 = a3 in 
    let out24 = a9 in 
    let out25 = a19 in 
    let out26 = a13 in 
    let out27 = a30 in 
    let out28 = a6 in 
    let out29 = a22 in 
    let out30 = a1 in 
    let out31 = a4 in 
    let out32 = a25 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32)


let pc_1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 = 
    let out1 = a57 in 
    let out2 = a49 in 
    let out3 = a41 in 
    let out4 = a33 in 
    let out5 = a25 in 
    let out6 = a17 in 
    let out7 = a9 in 
    let out8 = a1 in 
    let out9 = a58 in 
    let out10 = a50 in 
    let out11 = a42 in 
    let out12 = a34 in 
    let out13 = a26 in 
    let out14 = a18 in 
    let out15 = a10 in 
    let out16 = a2 in 
    let out17 = a59 in 
    let out18 = a51 in 
    let out19 = a43 in 
    let out20 = a35 in 
    let out21 = a27 in 
    let out22 = a19 in 
    let out23 = a11 in 
    let out24 = a3 in 
    let out25 = a60 in 
    let out26 = a52 in 
    let out27 = a44 in 
    let out28 = a36 in 
    let out29 = a63 in 
    let out30 = a55 in 
    let out31 = a47 in 
    let out32 = a39 in 
    let out33 = a31 in 
    let out34 = a23 in 
    let out35 = a15 in 
    let out36 = a7 in 
    let out37 = a62 in 
    let out38 = a54 in 
    let out39 = a46 in 
    let out40 = a38 in 
    let out41 = a30 in 
    let out42 = a22 in 
    let out43 = a14 in 
    let out44 = a6 in 
    let out45 = a61 in 
    let out46 = a53 in 
    let out47 = a45 in 
    let out48 = a37 in 
    let out49 = a29 in 
    let out50 = a21 in 
    let out51 = a13 in 
    let out52 = a5 in 
    let out53 = a28 in 
    let out54 = a20 in 
    let out55 = a12 in 
    let out56 = a4 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48,out49,out50,out51,out52,out53,out54,out55,out56)


let pc_2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 = 
    let out1 = a14 in 
    let out2 = a17 in 
    let out3 = a11 in 
    let out4 = a24 in 
    let out5 = a1 in 
    let out6 = a5 in 
    let out7 = a3 in 
    let out8 = a28 in 
    let out9 = a15 in 
    let out10 = a6 in 
    let out11 = a21 in 
    let out12 = a10 in 
    let out13 = a23 in 
    let out14 = a19 in 
    let out15 = a12 in 
    let out16 = a4 in 
    let out17 = a26 in 
    let out18 = a8 in 
    let out19 = a16 in 
    let out20 = a7 in 
    let out21 = a27 in 
    let out22 = a20 in 
    let out23 = a13 in 
    let out24 = a2 in 
    let out25 = a41 in 
    let out26 = a52 in 
    let out27 = a31 in 
    let out28 = a37 in 
    let out29 = a47 in 
    let out30 = a55 in 
    let out31 = a30 in 
    let out32 = a40 in 
    let out33 = a51 in 
    let out34 = a45 in 
    let out35 = a33 in 
    let out36 = a48 in 
    let out37 = a44 in 
    let out38 = a49 in 
    let out39 = a39 in 
    let out40 = a56 in 
    let out41 = a34 in 
    let out42 = a53 in 
    let out43 = a46 in 
    let out44 = a42 in 
    let out45 = a50 in 
    let out46 = a36 in 
    let out47 = a29 in 
    let out48 = a32 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48)


let rol_1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 = 
    let out1 = a28 in 
    let out2 = a1 in 
    let out3 = a2 in 
    let out4 = a3 in 
    let out5 = a4 in 
    let out6 = a5 in 
    let out7 = a6 in 
    let out8 = a7 in 
    let out9 = a8 in 
    let out10 = a9 in 
    let out11 = a10 in 
    let out12 = a11 in 
    let out13 = a12 in 
    let out14 = a13 in 
    let out15 = a14 in 
    let out16 = a15 in 
    let out17 = a16 in 
    let out18 = a17 in 
    let out19 = a18 in 
    let out20 = a19 in 
    let out21 = a20 in 
    let out22 = a21 in 
    let out23 = a22 in 
    let out24 = a23 in 
    let out25 = a24 in 
    let out26 = a25 in 
    let out27 = a26 in 
    let out28 = a27 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28)


let rol_2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 = 
    let out1 = a27 in 
    let out2 = a28 in 
    let out3 = a1 in 
    let out4 = a2 in 
    let out5 = a3 in 
    let out6 = a4 in 
    let out7 = a5 in 
    let out8 = a6 in 
    let out9 = a7 in 
    let out10 = a8 in 
    let out11 = a9 in 
    let out12 = a10 in 
    let out13 = a11 in 
    let out14 = a12 in 
    let out15 = a13 in 
    let out16 = a14 in 
    let out17 = a15 in 
    let out18 = a16 in 
    let out19 = a17 in 
    let out20 = a18 in 
    let out21 = a19 in 
    let out22 = a20 in 
    let out23 = a21 in 
    let out24 = a22 in 
    let out25 = a23 in 
    let out26 = a24 in 
    let out27 = a25 in 
    let out28 = a26 in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28)


let xor48 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 = 
    let out1 = (b1) lxor (a1) in 
    let out2 = (b2) lxor (a2) in 
    let out3 = (b3) lxor (a3) in 
    let out4 = (b4) lxor (a4) in 
    let out5 = (b5) lxor (a5) in 
    let out6 = (b6) lxor (a6) in 
    let out7 = (b7) lxor (a7) in 
    let out8 = (b8) lxor (a8) in 
    let out9 = (b9) lxor (a9) in 
    let out10 = (b10) lxor (a10) in 
    let out11 = (b11) lxor (a11) in 
    let out12 = (b12) lxor (a12) in 
    let out13 = (b13) lxor (a13) in 
    let out14 = (b14) lxor (a14) in 
    let out15 = (b15) lxor (a15) in 
    let out16 = (b16) lxor (a16) in 
    let out17 = (b17) lxor (a17) in 
    let out18 = (b18) lxor (a18) in 
    let out19 = (b19) lxor (a19) in 
    let out20 = (b20) lxor (a20) in 
    let out21 = (b21) lxor (a21) in 
    let out22 = (b22) lxor (a22) in 
    let out23 = (b23) lxor (a23) in 
    let out24 = (b24) lxor (a24) in 
    let out25 = (b25) lxor (a25) in 
    let out26 = (b26) lxor (a26) in 
    let out27 = (b27) lxor (a27) in 
    let out28 = (b28) lxor (a28) in 
    let out29 = (b29) lxor (a29) in 
    let out30 = (b30) lxor (a30) in 
    let out31 = (b31) lxor (a31) in 
    let out32 = (b32) lxor (a32) in 
    let out33 = (b33) lxor (a33) in 
    let out34 = (b34) lxor (a34) in 
    let out35 = (b35) lxor (a35) in 
    let out36 = (b36) lxor (a36) in 
    let out37 = (b37) lxor (a37) in 
    let out38 = (b38) lxor (a38) in 
    let out39 = (b39) lxor (a39) in 
    let out40 = (b40) lxor (a40) in 
    let out41 = (b41) lxor (a41) in 
    let out42 = (b42) lxor (a42) in 
    let out43 = (b43) lxor (a43) in 
    let out44 = (b44) lxor (a44) in 
    let out45 = (b45) lxor (a45) in 
    let out46 = (b46) lxor (a46) in 
    let out47 = (b47) lxor (a47) in 
    let out48 = (b48) lxor (a48) in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48)


let xor32 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 = 
    let out1 = (b1) lxor (a1) in 
    let out2 = (b2) lxor (a2) in 
    let out3 = (b3) lxor (a3) in 
    let out4 = (b4) lxor (a4) in 
    let out5 = (b5) lxor (a5) in 
    let out6 = (b6) lxor (a6) in 
    let out7 = (b7) lxor (a7) in 
    let out8 = (b8) lxor (a8) in 
    let out9 = (b9) lxor (a9) in 
    let out10 = (b10) lxor (a10) in 
    let out11 = (b11) lxor (a11) in 
    let out12 = (b12) lxor (a12) in 
    let out13 = (b13) lxor (a13) in 
    let out14 = (b14) lxor (a14) in 
    let out15 = (b15) lxor (a15) in 
    let out16 = (b16) lxor (a16) in 
    let out17 = (b17) lxor (a17) in 
    let out18 = (b18) lxor (a18) in 
    let out19 = (b19) lxor (a19) in 
    let out20 = (b20) lxor (a20) in 
    let out21 = (b21) lxor (a21) in 
    let out22 = (b22) lxor (a22) in 
    let out23 = (b23) lxor (a23) in 
    let out24 = (b24) lxor (a24) in 
    let out25 = (b25) lxor (a25) in 
    let out26 = (b26) lxor (a26) in 
    let out27 = (b27) lxor (a27) in 
    let out28 = (b28) lxor (a28) in 
    let out29 = (b29) lxor (a29) in 
    let out30 = (b30) lxor (a30) in 
    let out31 = (b31) lxor (a31) in 
    let out32 = (b32) lxor (a32) in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32)


let des a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15 k16 k17 k18 k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 k30 k31 k32 k33 k34 k35 k36 k37 k38 k39 k40 k41 k42 k43 k44 k45 k46 k47 k48 k49 k50 k51 k52 k53 k54 k55 k56 k57 k58 k59 k60 k61 k62 k63 k64 = 
    let (l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16,l17,l18,l19,l20,l21,l22,l23,l24,l25,l26,l27,l28,l29,l30,l31,l32,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32) = init_p (a1) (a2) (a3) (a4) (a5) (a6) (a7) (a8) (a9) (a10) (a11) (a12) (a13) (a14) (a15) (a16) (a17) (a18) (a19) (a20) (a21) (a22) (a23) (a24) (a25) (a26) (a27) (a28) (a29) (a30) (a31) (a32) (a33) (a34) (a35) (a36) (a37) (a38) (a39) (a40) (a41) (a42) (a43) (a44) (a45) (a46) (a47) (a48) (a49) (a50) (a51) (a52) (a53) (a54) (a55) (a56) (a57) (a58) (a59) (a60) (a61) (a62) (a63) (a64) in 
    let (kl1,kl2,kl3,kl4,kl5,kl6,kl7,kl8,kl9,kl10,kl11,kl12,kl13,kl14,kl15,kl16,kl17,kl18,kl19,kl20,kl21,kl22,kl23,kl24,kl25,kl26,kl27,kl28,kr1,kr2,kr3,kr4,kr5,kr6,kr7,kr8,kr9,kr10,kr11,kr12,kr13,kr14,kr15,kr16,kr17,kr18,kr19,kr20,kr21,kr22,kr23,kr24,kr25,kr26,kr27,kr28) = pc_1 (k1) (k2) (k3) (k4) (k5) (k6) (k7) (k8) (k9) (k10) (k11) (k12) (k13) (k14) (k15) (k16) (k17) (k18) (k19) (k20) (k21) (k22) (k23) (k24) (k25) (k26) (k27) (k28) (k29) (k30) (k31) (k32) (k33) (k34) (k35) (k36) (k37) (k38) (k39) (k40) (k41) (k42) (k43) (k44) (k45) (k46) (k47) (k48) (k49) (k50) (k51) (k52) (k53) (k54) (k55) (k56) (k57) (k58) (k59) (k60) (k61) (k62) (k63) (k64) in 
    let (a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,a31,a32,a33,a34,a35,a36,a37,a38,a39,a40,a41,a42,a43,a44,a45,a46,a47,a48) = expand (r1) (r2) (r3) (r4) (r5) (r6) (r7) (r8) (r9) (r10) (r11) (r12) (r13) (r14) (r15) (r16) (r17) (r18) (r19) (r20) (r21) (r22) (r23) (r24) (r25) (r26) (r27) (r28) (r29) (r30) (r31) (r32) in 
    let (kl1,kl2,kl3,kl4,kl5,kl6,kl7,kl8,kl9,kl10,kl11,kl12,kl13,kl14,kl15,kl16,kl17,kl18,kl19,kl20,kl21,kl22,kl23,kl24,kl25,kl26,kl27,kl28) = rol_1 (kl1) (kl2) (kl3) (kl4) (kl5) (kl6) (kl7) (kl8) (kl9) (kl10) (kl11) (kl12) (kl13) (kl14) (kl15) (kl16) (kl17) (kl18) (kl19) (kl20) (kl21) (kl22) (kl23) (kl24) (kl25) (kl26) (kl27) (kl28) in 
    let (kr1,kr2,kr3,kr4,kr5,kr6,kr7,kr8,kr9,kr10,kr11,kr12,kr13,kr14,kr15,kr16,kr17,kr18,kr19,kr20,kr21,kr22,kr23,kr24,kr25,kr26,kr27,kr28) = rol_1 (kr1) (kr2) (kr3) (kr4) (kr5) (kr6) (kr7) (kr8) (kr9) (kr10) (kr11) (kr12) (kr13) (kr14) (kr15) (kr16) (kr17) (kr18) (kr19) (kr20) (kr21) (kr22) (kr23) (kr24) (kr25) (kr26) (kr27) (kr28) in 
    let (k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11,k12,k13,k14,k15,k16,k17,k18,k19,k20,k21,k22,k23,k24,k25,k26,k27,k28,k29,k30,k31,k32,k33,k34,k35,k36,k37,k38,k39,k40,k41,k42,k43,k44,k45,k46,k47,k48) = pc_2 (kl1) (kl2) (kl3) (kl4) (kl5) (kl6) (kl7) (kl8) (kl9) (kl10) (kl11) (kl12) (kl13) (kl14) (kl15) (kl16) (kl17) (kl18) (kl19) (kl20) (kl21) (kl22) (kl23) (kl24) (kl25) (kl26) (kl27) (kl28) (kr1) (kr2) (kr3) (kr4) (kr5) (kr6) (kr7) (kr8) (kr9) (kr10) (kr11) (kr12) (kr13) (kr14) (kr15) (kr16) (kr17) (kr18) (kr19) (kr20) (kr21) (kr22) (kr23) (kr24) (kr25) (kr26) (kr27) (kr28) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = xor48 (a1) (a2) (a3) (a4) (a5) (a6) (a7) (a8) (a9) (a10) (a11) (a12) (a13) (a14) (a15) (a16) (a17) (a18) (a19) (a20) (a21) (a22) (a23) (a24) (a25) (a26) (a27) (a28) (a29) (a30) (a31) (a32) (a33) (a34) (a35) (a36) (a37) (a38) (a39) (a40) (a41) (a42) (a43) (a44) (a45) (a46) (a47) (a48) (k1) (k2) (k3) (k4) (k5) (k6) (k7) (k8) (k9) (k10) (k11) (k12) (k13) (k14) (k15) (k16) (k17) (k18) (k19) (k20) (k21) (k22) (k23) (k24) (k25) (k26) (k27) (k28) (k29) (k30) (k31) (k32) (k33) (k34) (k35) (k36) (k37) (k38) (k39) (k40) (k41) (k42) (k43) (k44) (k45) (k46) (k47) (k48) in 
    let (c1,c2,c3,c4) = sbox_1 (s1_1) (s1_2) (s1_3) (s1_4) (s1_5) (s1_6) in 
    let (c5,c6,c7,c8) = sbox_2 (s2_1) (s2_2) (s2_3) (s2_4) (s2_5) (s2_6) in 
    let (c9,c10,c11,c12) = sbox_3 (s3_1) (s3_2) (s3_3) (s3_4) (s3_5) (s3_6) in 
    let (c13,c14,c15,c16) = sbox_4 (s4_1) (s4_2) (s4_3) (s4_4) (s4_5) (s4_6) in 
    let (c17,c18,c19,c20) = sbox_5 (s5_1) (s5_2) (s5_3) (s5_4) (s5_5) (s5_6) in 
    let (c21,c22,c23,c24) = sbox_6 (s6_1) (s6_2) (s6_3) (s6_4) (s6_5) (s6_6) in 
    let (c25,c26,c27,c28) = sbox_7 (s7_1) (s7_2) (s7_3) (s7_4) (s7_5) (s7_6) in 
    let (c29,c30,c31,c32) = sbox_8 (s8_1) (s8_2) (s8_3) (s8_4) (s8_5) (s8_6) in 
    let (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32) = permut (c1) (c2) (c3) (c4) (c5) (c6) (c7) (c8) (c9) (c10) (c11) (c12) (c13) (c14) (c15) (c16) (c17) (c18) (c19) (c20) (c21) (c22) (c23) (c24) (c25) (c26) (c27) (c28) (c29) (c30) (c31) (c32) in 
    let (t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28,t29,t30,t31,t32) = (r32,r31,r30,r29,r28,r27,r26,r25,r24,r23,r22,r21,r20,r19,r18,r17,r16,r15,r14,r13,r12,r11,r10,r9,r8,r7,r6,r5,r4,r3,r2,r1) in 
    let (r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32) = xor32 (c1) (c2) (c3) (c4) (c5) (c6) (c7) (c8) (c9) (c10) (c11) (c12) (c13) (c14) (c15) (c16) (c17) (c18) (c19) (c20) (c21) (c22) (c23) (c24) (c25) (c26) (c27) (c28) (c29) (c30) (c31) (c32) (l1) (l2) (l3) (l4) (l5) (l6) (l7) (l8) (l9) (l10) (l11) (l12) (l13) (l14) (l15) (l16) (l17) (l18) (l19) (l20) (l21) (l22) (l23) (l24) (l25) (l26) (l27) (l28) (l29) (l30) (l31) (l32) in 
    let (l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16,l17,l18,l19,l20,l21,l22,l23,l24,l25,l26,l27,l28,l29,l30,l31,l32) = (t32,t31,t30,t29,t28,t27,t26,t25,t24,t23,t22,t21,t20,t19,t18,t17,t16,t15,t14,t13,t12,t11,t10,t9,t8,t7,t6,t5,t4,t3,t2,t1) in 
    let (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48,out49,out50,out51,out52,out53,out54,out55,out56,out57,out58,out59,out60,out61,out62,out63,out64) = final_p (l1) (l2) (l3) (l4) (l5) (l6) (l7) (l8) (l9) (l10) (l11) (l12) (l13) (l14) (l15) (l16) (l17) (l18) (l19) (l20) (l21) (l22) (l23) (l24) (l25) (l26) (l27) (l28) (l29) (l30) (l31) (l32) (r1) (r2) (r3) (r4) (r5) (r6) (r7) (r8) (r9) (r10) (r11) (r12) (r13) (r14) (r15) (r16) (r17) (r18) (r19) (r20) (r21) (r22) (r23) (r24) (r25) (r26) (r27) (r28) (r29) (r30) (r31) (r32) in 
    (out1,out2,out3,out4,out5,out6,out7,out8,out9,out10,out11,out12,out13,out14,out15,out16,out17,out18,out19,out20,out21,out22,out23,out24,out25,out26,out27,out28,out29,out30,out31,out32,out33,out34,out35,out36,out37,out38,out39,out40,out41,out42,out43,out44,out45,out46,out47,out48,out49,out50,out51,out52,out53,out54,out55,out56,out57,out58,out59,out60,out61,out62,out63,out64)



      
