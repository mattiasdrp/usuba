

let id x = x

let convert_ortho (size: int) (input: int64 array) : int array =
  let out = Array.make size 0 in
  for i = 0 to Array.length input - 1 do
    for j = 0 to size-1 do
      let b = Int64.to_int (Int64.logand (Int64.shift_right input.(i) j) Int64.one) in
      out.(j) <- out.(j) lor (b lsl i)
    done
  done;
  out
 

let convert_unortho (input: int array) : int64 array =
  let out = Array.make 63 Int64.zero in
  for i = 0 to Array.length input - 1 do
    for j = 0 to 62 do
      let b = Int64.of_int (input.(i) lsr j land 1) in
      out.(j) <- Int64.logor out.(j) (Int64.shift_left b i)
    done
  done;
  out


let convert5 ((in1_1,in1_2,in1_3,in1_4,in1_5,in1_6)) = 
    let out1_1 = in1_1 in 
    let out2_1 = in1_2 in 
    let out3_1 = in1_3 in 
    let out4_1 = in1_4 in 
    let out5_1 = in1_5 in 
    let out6_1 = in1_6 in 
    ((out1_1),(out2_1),(out3_1),(out4_1),(out5_1),(out6_1))



let convert6 ((in1_1,in1_2,in1_3,in1_4),(in2_1,in2_2,in2_3,in2_4),(in3_1,in3_2,in3_3,in3_4),(in4_1,in4_2,in4_3,in4_4),(in5_1,in5_2,in5_3,in5_4),(in6_1,in6_2,in6_3,in6_4),(in7_1,in7_2,in7_3,in7_4),(in8_1,in8_2,in8_3,in8_4)) = 
    let out1_1 = in1_1 in 
    let out1_2 = in1_2 in 
    let out1_3 = in1_3 in 
    let out1_4 = in1_4 in 
    let out1_5 = in2_1 in 
    let out1_6 = in2_2 in 
    let out1_7 = in2_3 in 
    let out1_8 = in2_4 in 
    let out1_9 = in3_1 in 
    let out1_10 = in3_2 in 
    let out1_11 = in3_3 in 
    let out1_12 = in3_4 in 
    let out1_13 = in4_1 in 
    let out1_14 = in4_2 in 
    let out1_15 = in4_3 in 
    let out1_16 = in4_4 in 
    let out1_17 = in5_1 in 
    let out1_18 = in5_2 in 
    let out1_19 = in5_3 in 
    let out1_20 = in5_4 in 
    let out1_21 = in6_1 in 
    let out1_22 = in6_2 in 
    let out1_23 = in6_3 in 
    let out1_24 = in6_4 in 
    let out1_25 = in7_1 in 
    let out1_26 = in7_2 in 
    let out1_27 = in7_3 in 
    let out1_28 = in7_4 in 
    let out1_29 = in8_1 in 
    let out1_30 = in8_2 in 
    let out1_31 = in8_3 in 
    let out1_32 = in8_4 in 
    ((out1_1,out1_2,out1_3,out1_4,out1_5,out1_6,out1_7,out1_8,out1_9,out1_10,out1_11,out1_12,out1_13,out1_14,out1_15,out1_16,out1_17,out1_18,out1_19,out1_20,out1_21,out1_22,out1_23,out1_24,out1_25,out1_26,out1_27,out1_28,out1_29,out1_30,out1_31,out1_32))



let convert7 ((in1_1,in1_2,in1_3,in1_4,in1_5,in1_6,in1_7,in1_8,in1_9,in1_10,in1_11,in1_12,in1_13,in1_14,in1_15,in1_16,in1_17,in1_18,in1_19,in1_20,in1_21,in1_22,in1_23,in1_24,in1_25,in1_26,in1_27,in1_28,in1_29,in1_30,in1_31,in1_32),(in2_1,in2_2,in2_3,in2_4,in2_5,in2_6,in2_7,in2_8,in2_9,in2_10,in2_11,in2_12,in2_13,in2_14,in2_15,in2_16,in2_17,in2_18,in2_19,in2_20,in2_21,in2_22,in2_23,in2_24,in2_25,in2_26,in2_27,in2_28,in2_29,in2_30,in2_31,in2_32)) = 
    let out1_1 = in1_1 in 
    let out1_2 = in1_2 in 
    let out1_3 = in1_3 in 
    let out1_4 = in1_4 in 
    let out1_5 = in1_5 in 
    let out1_6 = in1_6 in 
    let out1_7 = in1_7 in 
    let out1_8 = in1_8 in 
    let out1_9 = in1_9 in 
    let out1_10 = in1_10 in 
    let out1_11 = in1_11 in 
    let out1_12 = in1_12 in 
    let out1_13 = in1_13 in 
    let out1_14 = in1_14 in 
    let out1_15 = in1_15 in 
    let out1_16 = in1_16 in 
    let out1_17 = in1_17 in 
    let out1_18 = in1_18 in 
    let out1_19 = in1_19 in 
    let out1_20 = in1_20 in 
    let out1_21 = in1_21 in 
    let out1_22 = in1_22 in 
    let out1_23 = in1_23 in 
    let out1_24 = in1_24 in 
    let out1_25 = in1_25 in 
    let out1_26 = in1_26 in 
    let out1_27 = in1_27 in 
    let out1_28 = in1_28 in 
    let out1_29 = in1_29 in 
    let out1_30 = in1_30 in 
    let out1_31 = in1_31 in 
    let out1_32 = in1_32 in 
    let out1_33 = in2_1 in 
    let out1_34 = in2_2 in 
    let out1_35 = in2_3 in 
    let out1_36 = in2_4 in 
    let out1_37 = in2_5 in 
    let out1_38 = in2_6 in 
    let out1_39 = in2_7 in 
    let out1_40 = in2_8 in 
    let out1_41 = in2_9 in 
    let out1_42 = in2_10 in 
    let out1_43 = in2_11 in 
    let out1_44 = in2_12 in 
    let out1_45 = in2_13 in 
    let out1_46 = in2_14 in 
    let out1_47 = in2_15 in 
    let out1_48 = in2_16 in 
    let out1_49 = in2_17 in 
    let out1_50 = in2_18 in 
    let out1_51 = in2_19 in 
    let out1_52 = in2_20 in 
    let out1_53 = in2_21 in 
    let out1_54 = in2_22 in 
    let out1_55 = in2_23 in 
    let out1_56 = in2_24 in 
    let out1_57 = in2_25 in 
    let out1_58 = in2_26 in 
    let out1_59 = in2_27 in 
    let out1_60 = in2_28 in 
    let out1_61 = in2_29 in 
    let out1_62 = in2_30 in 
    let out1_63 = in2_31 in 
    let out1_64 = in2_32 in 
    ((out1_1,out1_2,out1_3,out1_4,out1_5,out1_6,out1_7,out1_8,out1_9,out1_10,out1_11,out1_12,out1_13,out1_14,out1_15,out1_16,out1_17,out1_18,out1_19,out1_20,out1_21,out1_22,out1_23,out1_24,out1_25,out1_26,out1_27,out1_28,out1_29,out1_30,out1_31,out1_32,out1_33,out1_34,out1_35,out1_36,out1_37,out1_38,out1_39,out1_40,out1_41,out1_42,out1_43,out1_44,out1_45,out1_46,out1_47,out1_48,out1_49,out1_50,out1_51,out1_52,out1_53,out1_54,out1_55,out1_56,out1_57,out1_58,out1_59,out1_60,out1_61,out1_62,out1_63,out1_64))



let convert8 ((in1_1,in1_2,in1_3,in1_4,in1_5,in1_6,in1_7,in1_8,in1_9,in1_10,in1_11,in1_12,in1_13,in1_14,in1_15,in1_16,in1_17,in1_18,in1_19,in1_20,in1_21,in1_22,in1_23,in1_24,in1_25,in1_26,in1_27,in1_28,in1_29,in1_30,in1_31,in1_32,in1_33,in1_34,in1_35,in1_36,in1_37,in1_38,in1_39,in1_40,in1_41,in1_42,in1_43,in1_44,in1_45,in1_46,in1_47,in1_48,in1_49,in1_50,in1_51,in1_52,in1_53,in1_54,in1_55,in1_56,in1_57,in1_58,in1_59,in1_60,in1_61,in1_62,in1_63,in1_64),(in2_1),(in3_1),(in4_1),(in5_1),(in6_1),(in7_1),(in8_1),(in9_1),(in10_1),(in11_1),(in12_1),(in13_1),(in14_1),(in15_1),(in16_1),(in17_1),(in18_1),(in19_1),(in20_1),(in21_1),(in22_1),(in23_1),(in24_1),(in25_1),(in26_1),(in27_1),(in28_1),(in29_1),(in30_1),(in31_1),(in32_1),(in33_1),(in34_1),(in35_1),(in36_1),(in37_1),(in38_1),(in39_1),(in40_1),(in41_1),(in42_1),(in43_1),(in44_1),(in45_1),(in46_1),(in47_1),(in48_1),(in49_1),(in50_1),(in51_1),(in52_1),(in53_1),(in54_1),(in55_1),(in56_1),(in57_1),(in58_1),(in59_1),(in60_1),(in61_1),(in62_1),(in63_1),(in64_1),(in65_1)) = 
    let out1_1 = in1_1 in 
    let out1_2 = in1_2 in 
    let out1_3 = in1_3 in 
    let out1_4 = in1_4 in 
    let out1_5 = in1_5 in 
    let out1_6 = in1_6 in 
    let out1_7 = in1_7 in 
    let out1_8 = in1_8 in 
    let out1_9 = in1_9 in 
    let out1_10 = in1_10 in 
    let out1_11 = in1_11 in 
    let out1_12 = in1_12 in 
    let out1_13 = in1_13 in 
    let out1_14 = in1_14 in 
    let out1_15 = in1_15 in 
    let out1_16 = in1_16 in 
    let out1_17 = in1_17 in 
    let out1_18 = in1_18 in 
    let out1_19 = in1_19 in 
    let out1_20 = in1_20 in 
    let out1_21 = in1_21 in 
    let out1_22 = in1_22 in 
    let out1_23 = in1_23 in 
    let out1_24 = in1_24 in 
    let out1_25 = in1_25 in 
    let out1_26 = in1_26 in 
    let out1_27 = in1_27 in 
    let out1_28 = in1_28 in 
    let out1_29 = in1_29 in 
    let out1_30 = in1_30 in 
    let out1_31 = in1_31 in 
    let out1_32 = in1_32 in 
    let out1_33 = in1_33 in 
    let out1_34 = in1_34 in 
    let out1_35 = in1_35 in 
    let out1_36 = in1_36 in 
    let out1_37 = in1_37 in 
    let out1_38 = in1_38 in 
    let out1_39 = in1_39 in 
    let out1_40 = in1_40 in 
    let out1_41 = in1_41 in 
    let out1_42 = in1_42 in 
    let out1_43 = in1_43 in 
    let out1_44 = in1_44 in 
    let out1_45 = in1_45 in 
    let out1_46 = in1_46 in 
    let out1_47 = in1_47 in 
    let out1_48 = in1_48 in 
    let out1_49 = in1_49 in 
    let out1_50 = in1_50 in 
    let out1_51 = in1_51 in 
    let out1_52 = in1_52 in 
    let out1_53 = in1_53 in 
    let out1_54 = in1_54 in 
    let out1_55 = in1_55 in 
    let out1_56 = in1_56 in 
    let out1_57 = in1_57 in 
    let out1_58 = in1_58 in 
    let out1_59 = in1_59 in 
    let out1_60 = in1_60 in 
    let out1_61 = in1_61 in 
    let out1_62 = in1_62 in 
    let out1_63 = in1_63 in 
    let out1_64 = in1_64 in 
    let out1_65 = in2_1 in 
    let out1_66 = in3_1 in 
    let out1_67 = in4_1 in 
    let out1_68 = in5_1 in 
    let out1_69 = in6_1 in 
    let out1_70 = in7_1 in 
    let out1_71 = in8_1 in 
    let out1_72 = in9_1 in 
    let out1_73 = in10_1 in 
    let out1_74 = in11_1 in 
    let out1_75 = in12_1 in 
    let out1_76 = in13_1 in 
    let out1_77 = in14_1 in 
    let out1_78 = in15_1 in 
    let out1_79 = in16_1 in 
    let out1_80 = in17_1 in 
    let out1_81 = in18_1 in 
    let out1_82 = in19_1 in 
    let out1_83 = in20_1 in 
    let out1_84 = in21_1 in 
    let out1_85 = in22_1 in 
    let out1_86 = in23_1 in 
    let out1_87 = in24_1 in 
    let out1_88 = in25_1 in 
    let out1_89 = in26_1 in 
    let out1_90 = in27_1 in 
    let out1_91 = in28_1 in 
    let out1_92 = in29_1 in 
    let out1_93 = in30_1 in 
    let out1_94 = in31_1 in 
    let out1_95 = in32_1 in 
    let out1_96 = in33_1 in 
    let out1_97 = in34_1 in 
    let out1_98 = in35_1 in 
    let out1_99 = in36_1 in 
    let out1_100 = in37_1 in 
    let out1_101 = in38_1 in 
    let out1_102 = in39_1 in 
    let out1_103 = in40_1 in 
    let out1_104 = in41_1 in 
    let out1_105 = in42_1 in 
    let out1_106 = in43_1 in 
    let out1_107 = in44_1 in 
    let out1_108 = in45_1 in 
    let out1_109 = in46_1 in 
    let out1_110 = in47_1 in 
    let out1_111 = in48_1 in 
    let out1_112 = in49_1 in 
    let out1_113 = in50_1 in 
    let out1_114 = in51_1 in 
    let out1_115 = in52_1 in 
    let out1_116 = in53_1 in 
    let out1_117 = in54_1 in 
    let out1_118 = in55_1 in 
    let out1_119 = in56_1 in 
    let out1_120 = in57_1 in 
    let out1_121 = in58_1 in 
    let out1_122 = in59_1 in 
    let out1_123 = in60_1 in 
    let out1_124 = in61_1 in 
    let out1_125 = in62_1 in 
    let out1_126 = in63_1 in 
    let out1_127 = in64_1 in 
    let out1_128 = in65_1 in 
    ((out1_1,out1_2,out1_3,out1_4,out1_5,out1_6,out1_7,out1_8,out1_9,out1_10,out1_11,out1_12,out1_13,out1_14,out1_15,out1_16,out1_17,out1_18,out1_19,out1_20,out1_21,out1_22,out1_23,out1_24,out1_25,out1_26,out1_27,out1_28,out1_29,out1_30,out1_31,out1_32,out1_33,out1_34,out1_35,out1_36,out1_37,out1_38,out1_39,out1_40,out1_41,out1_42,out1_43,out1_44,out1_45,out1_46,out1_47,out1_48,out1_49,out1_50,out1_51,out1_52,out1_53,out1_54,out1_55,out1_56,out1_57,out1_58,out1_59,out1_60,out1_61,out1_62,out1_63,out1_64,out1_65,out1_66,out1_67,out1_68,out1_69,out1_70,out1_71,out1_72,out1_73,out1_74,out1_75,out1_76,out1_77,out1_78,out1_79,out1_80,out1_81,out1_82,out1_83,out1_84,out1_85,out1_86,out1_87,out1_88,out1_89,out1_90,out1_91,out1_92,out1_93,out1_94,out1_95,out1_96,out1_97,out1_98,out1_99,out1_100,out1_101,out1_102,out1_103,out1_104,out1_105,out1_106,out1_107,out1_108,out1_109,out1_110,out1_111,out1_112,out1_113,out1_114,out1_115,out1_116,out1_117,out1_118,out1_119,out1_120,out1_121,out1_122,out1_123,out1_124,out1_125,out1_126,out1_127,out1_128))



let sbox_1_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a4_)) in 
    let x2_ = (lnot (a1_)) in 
    let x3_ = ((a4_) land ((lnot (a3_)))) lor (((lnot (a4_))) land (a3_)) in 
    let x4_ = ((x3_) land ((lnot (x2_)))) lor (((lnot (x3_))) land (x2_)) in 
    let x5_ = (a3_) lor (x2_) in 
    let x6_ = (x5_) land (x1_) in 
    let x7_ = (a6_) lor (x6_) in 
    let x8_ = ((x4_) land ((lnot (x7_)))) lor (((lnot (x4_))) land (x7_)) in 
    let x9_ = (x1_) lor (x2_) in 
    let x10_ = (a6_) land (x9_) in 
    let x11_ = ((x7_) land ((lnot (x10_)))) lor (((lnot (x7_))) land (x10_)) in 
    let x12_ = (a2_) lor (x11_) in 
    let x13_ = ((x8_) land ((lnot (x12_)))) lor (((lnot (x8_))) land (x12_)) in 
    let x14_ = ((x9_) land ((lnot (x13_)))) lor (((lnot (x9_))) land (x13_)) in 
    let x15_ = (a6_) lor (x14_) in 
    let x16_ = ((x1_) land ((lnot (x15_)))) lor (((lnot (x1_))) land (x15_)) in 
    let x17_ = (lnot (x14_)) in 
    let x18_ = (x17_) land (x3_) in 
    let x19_ = (a2_) lor (x18_) in 
    let x20_ = ((x16_) land ((lnot (x19_)))) lor (((lnot (x16_))) land (x19_)) in 
    let x21_ = (a5_) lor (x20_) in 
    let x22_ = ((x13_) land ((lnot (x21_)))) lor (((lnot (x13_))) land (x21_)) in 
    let out4_ = x22_ in 
    let x23_ = (a3_) lor (x4_) in 
    let x24_ = (lnot (x23_)) in 
    let x25_ = (a6_) lor (x24_) in 
    let x26_ = ((x6_) land ((lnot (x25_)))) lor (((lnot (x6_))) land (x25_)) in 
    let x27_ = (x1_) land (x8_) in 
    let x28_ = (a2_) lor (x27_) in 
    let x29_ = ((x26_) land ((lnot (x28_)))) lor (((lnot (x26_))) land (x28_)) in 
    let x30_ = (x1_) lor (x8_) in 
    let x31_ = ((x30_) land ((lnot (x6_)))) lor (((lnot (x30_))) land (x6_)) in 
    let x32_ = (x5_) land (x14_) in 
    let x33_ = ((x32_) land ((lnot (x8_)))) lor (((lnot (x32_))) land (x8_)) in 
    let x34_ = (a2_) land (x33_) in 
    let x35_ = ((x31_) land ((lnot (x34_)))) lor (((lnot (x31_))) land (x34_)) in 
    let x36_ = (a5_) lor (x35_) in 
    let x37_ = ((x29_) land ((lnot (x36_)))) lor (((lnot (x29_))) land (x36_)) in 
    let out1_ = x37_ in 
    let x38_ = (a3_) land (x10_) in 
    let x39_ = (x38_) lor (x4_) in 
    let x40_ = (a3_) land (x33_) in 
    let x41_ = ((x40_) land ((lnot (x25_)))) lor (((lnot (x40_))) land (x25_)) in 
    let x42_ = (a2_) lor (x41_) in 
    let x43_ = ((x39_) land ((lnot (x42_)))) lor (((lnot (x39_))) land (x42_)) in 
    let x44_ = (a3_) lor (x26_) in 
    let x45_ = ((x44_) land ((lnot (x14_)))) lor (((lnot (x44_))) land (x14_)) in 
    let x46_ = (a1_) lor (x8_) in 
    let x47_ = ((x46_) land ((lnot (x20_)))) lor (((lnot (x46_))) land (x20_)) in 
    let x48_ = (a2_) lor (x47_) in 
    let x49_ = ((x45_) land ((lnot (x48_)))) lor (((lnot (x45_))) land (x48_)) in 
    let x50_ = (a5_) land (x49_) in 
    let x51_ = ((x43_) land ((lnot (x50_)))) lor (((lnot (x43_))) land (x50_)) in 
    let out2_ = x51_ in 
    let x52_ = ((x8_) land ((lnot (x40_)))) lor (((lnot (x8_))) land (x40_)) in 
    let x53_ = ((a3_) land ((lnot (x11_)))) lor (((lnot (a3_))) land (x11_)) in 
    let x54_ = (x53_) land (x5_) in 
    let x55_ = (a2_) lor (x54_) in 
    let x56_ = ((x52_) land ((lnot (x55_)))) lor (((lnot (x52_))) land (x55_)) in 
    let x57_ = (a6_) lor (x4_) in 
    let x58_ = ((x57_) land ((lnot (x38_)))) lor (((lnot (x57_))) land (x38_)) in 
    let x59_ = (x13_) land (x56_) in 
    let x60_ = (a2_) land (x59_) in 
    let x61_ = ((x58_) land ((lnot (x60_)))) lor (((lnot (x58_))) land (x60_)) in 
    let x62_ = (a5_) land (x61_) in 
    let x63_ = ((x56_) land ((lnot (x62_)))) lor (((lnot (x56_))) land (x62_)) in 
    let out3_ = x63_ in 
    (out1_,out2_,out3_,out4_)



let sbox_2_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a5_)) in 
    let x2_ = (lnot (a1_)) in 
    let x3_ = ((a5_) land ((lnot (a6_)))) lor (((lnot (a5_))) land (a6_)) in 
    let x4_ = ((x3_) land ((lnot (x2_)))) lor (((lnot (x3_))) land (x2_)) in 
    let x5_ = ((x4_) land ((lnot (a2_)))) lor (((lnot (x4_))) land (a2_)) in 
    let x6_ = (a6_) lor (x1_) in 
    let x7_ = (x6_) lor (x2_) in 
    let x8_ = (a2_) land (x7_) in 
    let x9_ = ((a6_) land ((lnot (x8_)))) lor (((lnot (a6_))) land (x8_)) in 
    let x10_ = (a3_) land (x9_) in 
    let x11_ = ((x5_) land ((lnot (x10_)))) lor (((lnot (x5_))) land (x10_)) in 
    let x12_ = (a2_) land (x9_) in 
    let x13_ = ((a5_) land ((lnot (x6_)))) lor (((lnot (a5_))) land (x6_)) in 
    let x14_ = (a3_) lor (x13_) in 
    let x15_ = ((x12_) land ((lnot (x14_)))) lor (((lnot (x12_))) land (x14_)) in 
    let x16_ = (a4_) land (x15_) in 
    let x17_ = ((x11_) land ((lnot (x16_)))) lor (((lnot (x11_))) land (x16_)) in 
    let out2_ = x17_ in 
    let x18_ = (a5_) lor (a1_) in 
    let x19_ = (a6_) lor (x18_) in 
    let x20_ = ((x13_) land ((lnot (x19_)))) lor (((lnot (x13_))) land (x19_)) in 
    let x21_ = ((x20_) land ((lnot (a2_)))) lor (((lnot (x20_))) land (a2_)) in 
    let x22_ = (a6_) lor (x4_) in 
    let x23_ = (x22_) land (x17_) in 
    let x24_ = (a3_) lor (x23_) in 
    let x25_ = ((x21_) land ((lnot (x24_)))) lor (((lnot (x21_))) land (x24_)) in 
    let x26_ = (a6_) lor (x2_) in 
    let x27_ = (a5_) land (x2_) in 
    let x28_ = (a2_) lor (x27_) in 
    let x29_ = ((x26_) land ((lnot (x28_)))) lor (((lnot (x26_))) land (x28_)) in 
    let x30_ = ((x3_) land ((lnot (x27_)))) lor (((lnot (x3_))) land (x27_)) in 
    let x31_ = ((x2_) land ((lnot (x19_)))) lor (((lnot (x2_))) land (x19_)) in 
    let x32_ = (a2_) land (x31_) in 
    let x33_ = ((x30_) land ((lnot (x32_)))) lor (((lnot (x30_))) land (x32_)) in 
    let x34_ = (a3_) land (x33_) in 
    let x35_ = ((x29_) land ((lnot (x34_)))) lor (((lnot (x29_))) land (x34_)) in 
    let x36_ = (a4_) lor (x35_) in 
    let x37_ = ((x25_) land ((lnot (x36_)))) lor (((lnot (x25_))) land (x36_)) in 
    let out3_ = x37_ in 
    let x38_ = (x21_) land (x32_) in 
    let x39_ = ((x38_) land ((lnot (x5_)))) lor (((lnot (x38_))) land (x5_)) in 
    let x40_ = (a1_) lor (x15_) in 
    let x41_ = ((x40_) land ((lnot (x13_)))) lor (((lnot (x40_))) land (x13_)) in 
    let x42_ = (a3_) lor (x41_) in 
    let x43_ = ((x39_) land ((lnot (x42_)))) lor (((lnot (x39_))) land (x42_)) in 
    let x44_ = (x28_) lor (x41_) in 
    let x45_ = (a4_) land (x44_) in 
    let x46_ = ((x43_) land ((lnot (x45_)))) lor (((lnot (x43_))) land (x45_)) in 
    let out1_ = x46_ in 
    let x47_ = (x19_) land (x21_) in 
    let x48_ = ((x47_) land ((lnot (x26_)))) lor (((lnot (x47_))) land (x26_)) in 
    let x49_ = (a2_) land (x33_) in 
    let x50_ = ((x49_) land ((lnot (x21_)))) lor (((lnot (x49_))) land (x21_)) in 
    let x51_ = (a3_) land (x50_) in 
    let x52_ = ((x48_) land ((lnot (x51_)))) lor (((lnot (x48_))) land (x51_)) in 
    let x53_ = (x18_) land (x28_) in 
    let x54_ = (x53_) land (x50_) in 
    let x55_ = (a4_) lor (x54_) in 
    let x56_ = ((x52_) land ((lnot (x55_)))) lor (((lnot (x52_))) land (x55_)) in 
    let out4_ = x56_ in 
    (out1_,out2_,out3_,out4_)



let sbox_3_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a5_)) in 
    let x2_ = (lnot (a6_)) in 
    let x3_ = (a5_) land (a3_) in 
    let x4_ = ((x3_) land ((lnot (a6_)))) lor (((lnot (x3_))) land (a6_)) in 
    let x5_ = (a4_) land (x1_) in 
    let x6_ = ((x4_) land ((lnot (x5_)))) lor (((lnot (x4_))) land (x5_)) in 
    let x7_ = ((x6_) land ((lnot (a2_)))) lor (((lnot (x6_))) land (a2_)) in 
    let x8_ = (a3_) land (x1_) in 
    let x9_ = ((a5_) land ((lnot (x2_)))) lor (((lnot (a5_))) land (x2_)) in 
    let x10_ = (a4_) lor (x9_) in 
    let x11_ = ((x8_) land ((lnot (x10_)))) lor (((lnot (x8_))) land (x10_)) in 
    let x12_ = (x7_) land (x11_) in 
    let x13_ = ((a5_) land ((lnot (x11_)))) lor (((lnot (a5_))) land (x11_)) in 
    let x14_ = (x13_) lor (x7_) in 
    let x15_ = (a4_) land (x14_) in 
    let x16_ = ((x12_) land ((lnot (x15_)))) lor (((lnot (x12_))) land (x15_)) in 
    let x17_ = (a2_) land (x16_) in 
    let x18_ = ((x11_) land ((lnot (x17_)))) lor (((lnot (x11_))) land (x17_)) in 
    let x19_ = (a1_) land (x18_) in 
    let x20_ = ((x7_) land ((lnot (x19_)))) lor (((lnot (x7_))) land (x19_)) in 
    let out4_ = x20_ in 
    let x21_ = ((a3_) land ((lnot (a4_)))) lor (((lnot (a3_))) land (a4_)) in 
    let x22_ = ((x21_) land ((lnot (x9_)))) lor (((lnot (x21_))) land (x9_)) in 
    let x23_ = (x2_) lor (x4_) in 
    let x24_ = ((x23_) land ((lnot (x8_)))) lor (((lnot (x23_))) land (x8_)) in 
    let x25_ = (a2_) lor (x24_) in 
    let x26_ = ((x22_) land ((lnot (x25_)))) lor (((lnot (x22_))) land (x25_)) in 
    let x27_ = ((a6_) land ((lnot (x23_)))) lor (((lnot (a6_))) land (x23_)) in 
    let x28_ = (x27_) lor (a4_) in 
    let x29_ = ((a3_) land ((lnot (x15_)))) lor (((lnot (a3_))) land (x15_)) in 
    let x30_ = (x29_) lor (x5_) in 
    let x31_ = (a2_) lor (x30_) in 
    let x32_ = ((x28_) land ((lnot (x31_)))) lor (((lnot (x28_))) land (x31_)) in 
    let x33_ = (a1_) lor (x32_) in 
    let x34_ = ((x26_) land ((lnot (x33_)))) lor (((lnot (x26_))) land (x33_)) in 
    let out1_ = x34_ in 
    let x35_ = ((a3_) land ((lnot (x9_)))) lor (((lnot (a3_))) land (x9_)) in 
    let x36_ = (x35_) lor (x5_) in 
    let x37_ = (x4_) lor (x29_) in 
    let x38_ = ((x37_) land ((lnot (a4_)))) lor (((lnot (x37_))) land (a4_)) in 
    let x39_ = (a2_) lor (x38_) in 
    let x40_ = ((x36_) land ((lnot (x39_)))) lor (((lnot (x36_))) land (x39_)) in 
    let x41_ = (a6_) land (x11_) in 
    let x42_ = (x41_) lor (x6_) in 
    let x43_ = ((x34_) land ((lnot (x38_)))) lor (((lnot (x34_))) land (x38_)) in 
    let x44_ = ((x43_) land ((lnot (x41_)))) lor (((lnot (x43_))) land (x41_)) in 
    let x45_ = (a2_) land (x44_) in 
    let x46_ = ((x42_) land ((lnot (x45_)))) lor (((lnot (x42_))) land (x45_)) in 
    let x47_ = (a1_) lor (x46_) in 
    let x48_ = ((x40_) land ((lnot (x47_)))) lor (((lnot (x40_))) land (x47_)) in 
    let out3_ = x48_ in 
    let x49_ = (x2_) lor (x38_) in 
    let x50_ = ((x49_) land ((lnot (x13_)))) lor (((lnot (x49_))) land (x13_)) in 
    let x51_ = ((x27_) land ((lnot (x28_)))) lor (((lnot (x27_))) land (x28_)) in 
    let x52_ = (a2_) lor (x51_) in 
    let x53_ = ((x50_) land ((lnot (x52_)))) lor (((lnot (x50_))) land (x52_)) in 
    let x54_ = (x12_) land (x23_) in 
    let x55_ = (x54_) land (x52_) in 
    let x56_ = (a1_) lor (x55_) in 
    let x57_ = ((x53_) land ((lnot (x56_)))) lor (((lnot (x53_))) land (x56_)) in 
    let out2_ = x57_ in 
    (out1_,out2_,out3_,out4_)



let sbox_4_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a1_)) in 
    let x2_ = (lnot (a3_)) in 
    let x3_ = (a1_) lor (a3_) in 
    let x4_ = (a5_) land (x3_) in 
    let x5_ = ((x1_) land ((lnot (x4_)))) lor (((lnot (x1_))) land (x4_)) in 
    let x6_ = (a2_) lor (a3_) in 
    let x7_ = ((x5_) land ((lnot (x6_)))) lor (((lnot (x5_))) land (x6_)) in 
    let x8_ = (a1_) land (a5_) in 
    let x9_ = ((x8_) land ((lnot (x3_)))) lor (((lnot (x8_))) land (x3_)) in 
    let x10_ = (a2_) land (x9_) in 
    let x11_ = ((a5_) land ((lnot (x10_)))) lor (((lnot (a5_))) land (x10_)) in 
    let x12_ = (a4_) land (x11_) in 
    let x13_ = ((x7_) land ((lnot (x12_)))) lor (((lnot (x7_))) land (x12_)) in 
    let x14_ = ((x2_) land ((lnot (x4_)))) lor (((lnot (x2_))) land (x4_)) in 
    let x15_ = (a2_) land (x14_) in 
    let x16_ = ((x9_) land ((lnot (x15_)))) lor (((lnot (x9_))) land (x15_)) in 
    let x17_ = (x5_) land (x14_) in 
    let x18_ = ((a5_) land ((lnot (x2_)))) lor (((lnot (a5_))) land (x2_)) in 
    let x19_ = (a2_) lor (x18_) in 
    let x20_ = ((x17_) land ((lnot (x19_)))) lor (((lnot (x17_))) land (x19_)) in 
    let x21_ = (a4_) lor (x20_) in 
    let x22_ = ((x16_) land ((lnot (x21_)))) lor (((lnot (x16_))) land (x21_)) in 
    let x23_ = (a6_) land (x22_) in 
    let x24_ = ((x13_) land ((lnot (x23_)))) lor (((lnot (x13_))) land (x23_)) in 
    let out2_ = x24_ in 
    let x25_ = (lnot (x13_)) in 
    let x26_ = (a6_) lor (x22_) in 
    let x27_ = ((x25_) land ((lnot (x26_)))) lor (((lnot (x25_))) land (x26_)) in 
    let out1_ = x27_ in 
    let x28_ = (a2_) land (x11_) in 
    let x29_ = ((x28_) land ((lnot (x17_)))) lor (((lnot (x28_))) land (x17_)) in 
    let x30_ = ((a3_) land ((lnot (x10_)))) lor (((lnot (a3_))) land (x10_)) in 
    let x31_ = ((x30_) land ((lnot (x19_)))) lor (((lnot (x30_))) land (x19_)) in 
    let x32_ = (a4_) land (x31_) in 
    let x33_ = ((x29_) land ((lnot (x32_)))) lor (((lnot (x29_))) land (x32_)) in 
    let x34_ = ((x25_) land ((lnot (x33_)))) lor (((lnot (x25_))) land (x33_)) in 
    let x35_ = (a2_) land (x34_) in 
    let x36_ = ((x24_) land ((lnot (x35_)))) lor (((lnot (x24_))) land (x35_)) in 
    let x37_ = (a4_) lor (x34_) in 
    let x38_ = ((x36_) land ((lnot (x37_)))) lor (((lnot (x36_))) land (x37_)) in 
    let x39_ = (a6_) land (x38_) in 
    let x40_ = ((x33_) land ((lnot (x39_)))) lor (((lnot (x33_))) land (x39_)) in 
    let out4_ = x40_ in 
    let x41_ = ((x26_) land ((lnot (x38_)))) lor (((lnot (x26_))) land (x38_)) in 
    let x42_ = ((x41_) land ((lnot (x40_)))) lor (((lnot (x41_))) land (x40_)) in 
    let out3_ = x42_ in 
    (out1_,out2_,out3_,out4_)



let sbox_5_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a6_)) in 
    let x2_ = (lnot (a3_)) in 
    let x3_ = (x1_) lor (x2_) in 
    let x4_ = ((x3_) land ((lnot (a4_)))) lor (((lnot (x3_))) land (a4_)) in 
    let x5_ = (a1_) land (x3_) in 
    let x6_ = ((x4_) land ((lnot (x5_)))) lor (((lnot (x4_))) land (x5_)) in 
    let x7_ = (a6_) lor (a4_) in 
    let x8_ = ((x7_) land ((lnot (a3_)))) lor (((lnot (x7_))) land (a3_)) in 
    let x9_ = (a3_) lor (x7_) in 
    let x10_ = (a1_) lor (x9_) in 
    let x11_ = ((x8_) land ((lnot (x10_)))) lor (((lnot (x8_))) land (x10_)) in 
    let x12_ = (a5_) land (x11_) in 
    let x13_ = ((x6_) land ((lnot (x12_)))) lor (((lnot (x6_))) land (x12_)) in 
    let x14_ = (lnot (x4_)) in 
    let x15_ = (x14_) land (a6_) in 
    let x16_ = (a1_) lor (x15_) in 
    let x17_ = ((x8_) land ((lnot (x16_)))) lor (((lnot (x8_))) land (x16_)) in 
    let x18_ = (a5_) lor (x17_) in 
    let x19_ = ((x10_) land ((lnot (x18_)))) lor (((lnot (x10_))) land (x18_)) in 
    let x20_ = (a2_) lor (x19_) in 
    let x21_ = ((x13_) land ((lnot (x20_)))) lor (((lnot (x13_))) land (x20_)) in 
    let out3_ = x21_ in 
    let x22_ = (x2_) lor (x15_) in 
    let x23_ = ((x22_) land ((lnot (a6_)))) lor (((lnot (x22_))) land (a6_)) in 
    let x24_ = ((a4_) land ((lnot (x22_)))) lor (((lnot (a4_))) land (x22_)) in 
    let x25_ = (a1_) land (x24_) in 
    let x26_ = ((x23_) land ((lnot (x25_)))) lor (((lnot (x23_))) land (x25_)) in 
    let x27_ = ((a1_) land ((lnot (x11_)))) lor (((lnot (a1_))) land (x11_)) in 
    let x28_ = (x27_) land (x22_) in 
    let x29_ = (a5_) lor (x28_) in 
    let x30_ = ((x26_) land ((lnot (x29_)))) lor (((lnot (x26_))) land (x29_)) in 
    let x31_ = (a4_) lor (x27_) in 
    let x32_ = (lnot (x31_)) in 
    let x33_ = (a2_) lor (x32_) in 
    let x34_ = ((x30_) land ((lnot (x33_)))) lor (((lnot (x30_))) land (x33_)) in 
    let out2_ = x34_ in 
    let x35_ = ((x2_) land ((lnot (x15_)))) lor (((lnot (x2_))) land (x15_)) in 
    let x36_ = (a1_) land (x35_) in 
    let x37_ = ((x14_) land ((lnot (x36_)))) lor (((lnot (x14_))) land (x36_)) in 
    let x38_ = ((x5_) land ((lnot (x7_)))) lor (((lnot (x5_))) land (x7_)) in 
    let x39_ = (x38_) land (x34_) in 
    let x40_ = (a5_) lor (x39_) in 
    let x41_ = ((x37_) land ((lnot (x40_)))) lor (((lnot (x37_))) land (x40_)) in 
    let x42_ = ((x2_) land ((lnot (x5_)))) lor (((lnot (x2_))) land (x5_)) in 
    let x43_ = (x42_) land (x16_) in 
    let x44_ = (x4_) land (x27_) in 
    let x45_ = (a5_) land (x44_) in 
    let x46_ = ((x43_) land ((lnot (x45_)))) lor (((lnot (x43_))) land (x45_)) in 
    let x47_ = (a2_) lor (x46_) in 
    let x48_ = ((x41_) land ((lnot (x47_)))) lor (((lnot (x41_))) land (x47_)) in 
    let out1_ = x48_ in 
    let x49_ = (x24_) land (x48_) in 
    let x50_ = ((x49_) land ((lnot (x5_)))) lor (((lnot (x49_))) land (x5_)) in 
    let x51_ = ((x11_) land ((lnot (x30_)))) lor (((lnot (x11_))) land (x30_)) in 
    let x52_ = (x51_) lor (x50_) in 
    let x53_ = (a5_) land (x52_) in 
    let x54_ = ((x50_) land ((lnot (x53_)))) lor (((lnot (x50_))) land (x53_)) in 
    let x55_ = ((x14_) land ((lnot (x19_)))) lor (((lnot (x14_))) land (x19_)) in 
    let x56_ = ((x55_) land ((lnot (x34_)))) lor (((lnot (x55_))) land (x34_)) in 
    let x57_ = ((x4_) land ((lnot (x16_)))) lor (((lnot (x4_))) land (x16_)) in 
    let x58_ = (x57_) land (x30_) in 
    let x59_ = (a5_) land (x58_) in 
    let x60_ = ((x56_) land ((lnot (x59_)))) lor (((lnot (x56_))) land (x59_)) in 
    let x61_ = (a2_) lor (x60_) in 
    let x62_ = ((x54_) land ((lnot (x61_)))) lor (((lnot (x54_))) land (x61_)) in 
    let out4_ = x62_ in 
    (out1_,out2_,out3_,out4_)



let sbox_6_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a2_)) in 
    let x2_ = (lnot (a5_)) in 
    let x3_ = ((a2_) land ((lnot (a6_)))) lor (((lnot (a2_))) land (a6_)) in 
    let x4_ = ((x3_) land ((lnot (x2_)))) lor (((lnot (x3_))) land (x2_)) in 
    let x5_ = ((x4_) land ((lnot (a1_)))) lor (((lnot (x4_))) land (a1_)) in 
    let x6_ = (a5_) land (a6_) in 
    let x7_ = (x6_) lor (x1_) in 
    let x8_ = (a5_) land (x5_) in 
    let x9_ = (a1_) land (x8_) in 
    let x10_ = ((x7_) land ((lnot (x9_)))) lor (((lnot (x7_))) land (x9_)) in 
    let x11_ = (a4_) land (x10_) in 
    let x12_ = ((x5_) land ((lnot (x11_)))) lor (((lnot (x5_))) land (x11_)) in 
    let x13_ = ((a6_) land ((lnot (x10_)))) lor (((lnot (a6_))) land (x10_)) in 
    let x14_ = (x13_) land (a1_) in 
    let x15_ = (a2_) land (a6_) in 
    let x16_ = ((x15_) land ((lnot (a5_)))) lor (((lnot (x15_))) land (a5_)) in 
    let x17_ = (a1_) land (x16_) in 
    let x18_ = ((x2_) land ((lnot (x17_)))) lor (((lnot (x2_))) land (x17_)) in 
    let x19_ = (a4_) lor (x18_) in 
    let x20_ = ((x14_) land ((lnot (x19_)))) lor (((lnot (x14_))) land (x19_)) in 
    let x21_ = (a3_) land (x20_) in 
    let x22_ = ((x12_) land ((lnot (x21_)))) lor (((lnot (x12_))) land (x21_)) in 
    let out2_ = x22_ in 
    let x23_ = ((a6_) land ((lnot (x18_)))) lor (((lnot (a6_))) land (x18_)) in 
    let x24_ = (a1_) land (x23_) in 
    let x25_ = ((a5_) land ((lnot (x24_)))) lor (((lnot (a5_))) land (x24_)) in 
    let x26_ = ((a2_) land ((lnot (x17_)))) lor (((lnot (a2_))) land (x17_)) in 
    let x27_ = (x26_) lor (x6_) in 
    let x28_ = (a4_) land (x27_) in 
    let x29_ = ((x25_) land ((lnot (x28_)))) lor (((lnot (x25_))) land (x28_)) in 
    let x30_ = (lnot (x26_)) in 
    let x31_ = (a6_) lor (x29_) in 
    let x32_ = (lnot (x31_)) in 
    let x33_ = (a4_) land (x32_) in 
    let x34_ = ((x30_) land ((lnot (x33_)))) lor (((lnot (x30_))) land (x33_)) in 
    let x35_ = (a3_) land (x34_) in 
    let x36_ = ((x29_) land ((lnot (x35_)))) lor (((lnot (x29_))) land (x35_)) in 
    let out4_ = x36_ in 
    let x37_ = ((x6_) land ((lnot (x34_)))) lor (((lnot (x6_))) land (x34_)) in 
    let x38_ = (a5_) land (x23_) in 
    let x39_ = ((x38_) land ((lnot (x5_)))) lor (((lnot (x38_))) land (x5_)) in 
    let x40_ = (a4_) lor (x39_) in 
    let x41_ = ((x37_) land ((lnot (x40_)))) lor (((lnot (x37_))) land (x40_)) in 
    let x42_ = (x16_) lor (x24_) in 
    let x43_ = ((x42_) land ((lnot (x1_)))) lor (((lnot (x42_))) land (x1_)) in 
    let x44_ = ((x15_) land ((lnot (x24_)))) lor (((lnot (x15_))) land (x24_)) in 
    let x45_ = ((x44_) land ((lnot (x31_)))) lor (((lnot (x44_))) land (x31_)) in 
    let x46_ = (a4_) lor (x45_) in 
    let x47_ = ((x43_) land ((lnot (x46_)))) lor (((lnot (x43_))) land (x46_)) in 
    let x48_ = (a3_) lor (x47_) in 
    let x49_ = ((x41_) land ((lnot (x48_)))) lor (((lnot (x41_))) land (x48_)) in 
    let out1_ = x49_ in 
    let x50_ = (x5_) lor (x38_) in 
    let x51_ = ((x50_) land ((lnot (x6_)))) lor (((lnot (x50_))) land (x6_)) in 
    let x52_ = (x8_) land (x31_) in 
    let x53_ = (a4_) lor (x52_) in 
    let x54_ = ((x51_) land ((lnot (x53_)))) lor (((lnot (x51_))) land (x53_)) in 
    let x55_ = (x30_) land (x43_) in 
    let x56_ = (a3_) lor (x55_) in 
    let x57_ = ((x54_) land ((lnot (x56_)))) lor (((lnot (x54_))) land (x56_)) in 
    let out3_ = x57_ in 
    (out1_,out2_,out3_,out4_)



let sbox_7_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a2_)) in 
    let x2_ = (lnot (a5_)) in 
    let x3_ = (a2_) land (a4_) in 
    let x4_ = ((x3_) land ((lnot (a5_)))) lor (((lnot (x3_))) land (a5_)) in 
    let x5_ = ((x4_) land ((lnot (a3_)))) lor (((lnot (x4_))) land (a3_)) in 
    let x6_ = (a4_) land (x4_) in 
    let x7_ = ((x6_) land ((lnot (a2_)))) lor (((lnot (x6_))) land (a2_)) in 
    let x8_ = (a3_) land (x7_) in 
    let x9_ = ((a1_) land ((lnot (x8_)))) lor (((lnot (a1_))) land (x8_)) in 
    let x10_ = (a6_) lor (x9_) in 
    let x11_ = ((x5_) land ((lnot (x10_)))) lor (((lnot (x5_))) land (x10_)) in 
    let x12_ = (a4_) land (x2_) in 
    let x13_ = (x12_) lor (a2_) in 
    let x14_ = (a2_) lor (x2_) in 
    let x15_ = (a3_) land (x14_) in 
    let x16_ = ((x13_) land ((lnot (x15_)))) lor (((lnot (x13_))) land (x15_)) in 
    let x17_ = ((x6_) land ((lnot (x11_)))) lor (((lnot (x6_))) land (x11_)) in 
    let x18_ = (a6_) lor (x17_) in 
    let x19_ = ((x16_) land ((lnot (x18_)))) lor (((lnot (x16_))) land (x18_)) in 
    let x20_ = (a1_) land (x19_) in 
    let x21_ = ((x11_) land ((lnot (x20_)))) lor (((lnot (x11_))) land (x20_)) in 
    let out1_ = x21_ in 
    let x22_ = (a2_) lor (x21_) in 
    let x23_ = ((x22_) land ((lnot (x6_)))) lor (((lnot (x22_))) land (x6_)) in 
    let x24_ = ((x23_) land ((lnot (x15_)))) lor (((lnot (x23_))) land (x15_)) in 
    let x25_ = ((x5_) land ((lnot (x6_)))) lor (((lnot (x5_))) land (x6_)) in 
    let x26_ = (x25_) lor (x12_) in 
    let x27_ = (a6_) lor (x26_) in 
    let x28_ = ((x24_) land ((lnot (x27_)))) lor (((lnot (x24_))) land (x27_)) in 
    let x29_ = (x1_) land (x19_) in 
    let x30_ = (x23_) land (x26_) in 
    let x31_ = (a6_) land (x30_) in 
    let x32_ = ((x29_) land ((lnot (x31_)))) lor (((lnot (x29_))) land (x31_)) in 
    let x33_ = (a1_) lor (x32_) in 
    let x34_ = ((x28_) land ((lnot (x33_)))) lor (((lnot (x28_))) land (x33_)) in 
    let out4_ = x34_ in 
    let x35_ = (a4_) land (x16_) in 
    let x36_ = (x35_) lor (x1_) in 
    let x37_ = (a6_) land (x36_) in 
    let x38_ = ((x11_) land ((lnot (x37_)))) lor (((lnot (x11_))) land (x37_)) in 
    let x39_ = (a4_) land (x13_) in 
    let x40_ = (a3_) lor (x7_) in 
    let x41_ = ((x39_) land ((lnot (x40_)))) lor (((lnot (x39_))) land (x40_)) in 
    let x42_ = (x1_) lor (x24_) in 
    let x43_ = (a6_) lor (x42_) in 
    let x44_ = ((x41_) land ((lnot (x43_)))) lor (((lnot (x41_))) land (x43_)) in 
    let x45_ = (a1_) lor (x44_) in 
    let x46_ = ((x38_) land ((lnot (x45_)))) lor (((lnot (x38_))) land (x45_)) in 
    let out2_ = x46_ in 
    let x47_ = ((x8_) land ((lnot (x44_)))) lor (((lnot (x8_))) land (x44_)) in 
    let x48_ = ((x6_) land ((lnot (x15_)))) lor (((lnot (x6_))) land (x15_)) in 
    let x49_ = (a6_) lor (x48_) in 
    let x50_ = ((x47_) land ((lnot (x49_)))) lor (((lnot (x47_))) land (x49_)) in 
    let x51_ = ((x19_) land ((lnot (x44_)))) lor (((lnot (x19_))) land (x44_)) in 
    let x52_ = ((a4_) land ((lnot (x25_)))) lor (((lnot (a4_))) land (x25_)) in 
    let x53_ = (x52_) land (x46_) in 
    let x54_ = (a6_) land (x53_) in 
    let x55_ = ((x51_) land ((lnot (x54_)))) lor (((lnot (x51_))) land (x54_)) in 
    let x56_ = (a1_) lor (x55_) in 
    let x57_ = ((x50_) land ((lnot (x56_)))) lor (((lnot (x50_))) land (x56_)) in 
    let out3_ = x57_ in 
    (out1_,out2_,out3_,out4_)



let sbox_8_ (a1_,a2_,a3_,a4_,a5_,a6_) = 
    let x1_ = (lnot (a1_)) in 
    let x2_ = (lnot (a4_)) in 
    let x3_ = ((a3_) land ((lnot (x1_)))) lor (((lnot (a3_))) land (x1_)) in 
    let x4_ = (a3_) lor (x1_) in 
    let x5_ = ((x4_) land ((lnot (x2_)))) lor (((lnot (x4_))) land (x2_)) in 
    let x6_ = (a5_) lor (x5_) in 
    let x7_ = ((x3_) land ((lnot (x6_)))) lor (((lnot (x3_))) land (x6_)) in 
    let x8_ = (x1_) lor (x5_) in 
    let x9_ = ((x2_) land ((lnot (x8_)))) lor (((lnot (x2_))) land (x8_)) in 
    let x10_ = (a5_) land (x9_) in 
    let x11_ = ((x8_) land ((lnot (x10_)))) lor (((lnot (x8_))) land (x10_)) in 
    let x12_ = (a2_) land (x11_) in 
    let x13_ = ((x7_) land ((lnot (x12_)))) lor (((lnot (x7_))) land (x12_)) in 
    let x14_ = ((x6_) land ((lnot (x9_)))) lor (((lnot (x6_))) land (x9_)) in 
    let x15_ = (x3_) land (x9_) in 
    let x16_ = (a5_) land (x8_) in 
    let x17_ = ((x15_) land ((lnot (x16_)))) lor (((lnot (x15_))) land (x16_)) in 
    let x18_ = (a2_) lor (x17_) in 
    let x19_ = ((x14_) land ((lnot (x18_)))) lor (((lnot (x14_))) land (x18_)) in 
    let x20_ = (a6_) lor (x19_) in 
    let x21_ = ((x13_) land ((lnot (x20_)))) lor (((lnot (x13_))) land (x20_)) in 
    let out1_ = x21_ in 
    let x22_ = (a5_) lor (x3_) in 
    let x23_ = (x22_) land (x2_) in 
    let x24_ = (lnot (a3_)) in 
    let x25_ = (x24_) land (x8_) in 
    let x26_ = (a5_) land (x4_) in 
    let x27_ = ((x25_) land ((lnot (x26_)))) lor (((lnot (x25_))) land (x26_)) in 
    let x28_ = (a2_) lor (x27_) in 
    let x29_ = ((x23_) land ((lnot (x28_)))) lor (((lnot (x23_))) land (x28_)) in 
    let x30_ = (a6_) land (x29_) in 
    let x31_ = ((x13_) land ((lnot (x30_)))) lor (((lnot (x13_))) land (x30_)) in 
    let out4_ = x31_ in 
    let x32_ = ((x5_) land ((lnot (x6_)))) lor (((lnot (x5_))) land (x6_)) in 
    let x33_ = ((x32_) land ((lnot (x22_)))) lor (((lnot (x32_))) land (x22_)) in 
    let x34_ = (a4_) lor (x13_) in 
    let x35_ = (a2_) land (x34_) in 
    let x36_ = ((x33_) land ((lnot (x35_)))) lor (((lnot (x33_))) land (x35_)) in 
    let x37_ = (a1_) land (x33_) in 
    let x38_ = ((x37_) land ((lnot (x8_)))) lor (((lnot (x37_))) land (x8_)) in 
    let x39_ = ((a1_) land ((lnot (x23_)))) lor (((lnot (a1_))) land (x23_)) in 
    let x40_ = (x39_) land (x7_) in 
    let x41_ = (a2_) land (x40_) in 
    let x42_ = ((x38_) land ((lnot (x41_)))) lor (((lnot (x38_))) land (x41_)) in 
    let x43_ = (a6_) lor (x42_) in 
    let x44_ = ((x36_) land ((lnot (x43_)))) lor (((lnot (x36_))) land (x43_)) in 
    let out3_ = x44_ in 
    let x45_ = ((a1_) land ((lnot (x10_)))) lor (((lnot (a1_))) land (x10_)) in 
    let x46_ = ((x45_) land ((lnot (x22_)))) lor (((lnot (x45_))) land (x22_)) in 
    let x47_ = (lnot (x7_)) in 
    let x48_ = (x47_) land (x8_) in 
    let x49_ = (a2_) lor (x48_) in 
    let x50_ = ((x46_) land ((lnot (x49_)))) lor (((lnot (x46_))) land (x49_)) in 
    let x51_ = ((x19_) land ((lnot (x29_)))) lor (((lnot (x19_))) land (x29_)) in 
    let x52_ = (x51_) lor (x38_) in 
    let x53_ = (a6_) land (x52_) in 
    let x54_ = ((x50_) land ((lnot (x53_)))) lor (((lnot (x50_))) land (x53_)) in 
    let out2_ = x54_ in 
    (out1_,out2_,out3_,out4_)



let expand_ ((a_1,a_2,a_3,a_4,a_5,a_6,a_7,a_8,a_9,a_10,a_11,a_12,a_13,a_14,a_15,a_16,a_17,a_18,a_19,a_20,a_21,a_22,a_23,a_24,a_25,a_26,a_27,a_28,a_29,a_30,a_31,a_32)) = 
    let out_1 = a_32 in 
    let out_2 = a_1 in 
    let out_3 = a_2 in 
    let out_4 = a_3 in 
    let out_5 = a_4 in 
    let out_6 = a_5 in 
    let out_7 = a_4 in 
    let out_8 = a_5 in 
    let out_9 = a_6 in 
    let out_10 = a_7 in 
    let out_11 = a_8 in 
    let out_12 = a_9 in 
    let out_13 = a_8 in 
    let out_14 = a_9 in 
    let out_15 = a_10 in 
    let out_16 = a_11 in 
    let out_17 = a_12 in 
    let out_18 = a_13 in 
    let out_19 = a_12 in 
    let out_20 = a_13 in 
    let out_21 = a_14 in 
    let out_22 = a_15 in 
    let out_23 = a_16 in 
    let out_24 = a_17 in 
    let out_25 = a_16 in 
    let out_26 = a_17 in 
    let out_27 = a_18 in 
    let out_28 = a_19 in 
    let out_29 = a_20 in 
    let out_30 = a_21 in 
    let out_31 = a_20 in 
    let out_32 = a_21 in 
    let out_33 = a_22 in 
    let out_34 = a_23 in 
    let out_35 = a_24 in 
    let out_36 = a_25 in 
    let out_37 = a_24 in 
    let out_38 = a_25 in 
    let out_39 = a_26 in 
    let out_40 = a_27 in 
    let out_41 = a_28 in 
    let out_42 = a_29 in 
    let out_43 = a_28 in 
    let out_44 = a_29 in 
    let out_45 = a_30 in 
    let out_46 = a_31 in 
    let out_47 = a_32 in 
    let out_48 = a_1 in 
    (out_1,out_2,out_3,out_4,out_5,out_6,out_7,out_8,out_9,out_10,out_11,out_12,out_13,out_14,out_15,out_16,out_17,out_18,out_19,out_20,out_21,out_22,out_23,out_24,out_25,out_26,out_27,out_28,out_29,out_30,out_31,out_32,out_33,out_34,out_35,out_36,out_37,out_38,out_39,out_40,out_41,out_42,out_43,out_44,out_45,out_46,out_47,out_48)



let init_p_ ((a_1,a_2,a_3,a_4,a_5,a_6,a_7,a_8,a_9,a_10,a_11,a_12,a_13,a_14,a_15,a_16,a_17,a_18,a_19,a_20,a_21,a_22,a_23,a_24,a_25,a_26,a_27,a_28,a_29,a_30,a_31,a_32,a_33,a_34,a_35,a_36,a_37,a_38,a_39,a_40,a_41,a_42,a_43,a_44,a_45,a_46,a_47,a_48,a_49,a_50,a_51,a_52,a_53,a_54,a_55,a_56,a_57,a_58,a_59,a_60,a_61,a_62,a_63,a_64)) = 
    let out_1 = a_58 in 
    let out_2 = a_50 in 
    let out_3 = a_42 in 
    let out_4 = a_34 in 
    let out_5 = a_26 in 
    let out_6 = a_18 in 
    let out_7 = a_10 in 
    let out_8 = a_2 in 
    let out_9 = a_60 in 
    let out_10 = a_52 in 
    let out_11 = a_44 in 
    let out_12 = a_36 in 
    let out_13 = a_28 in 
    let out_14 = a_20 in 
    let out_15 = a_12 in 
    let out_16 = a_4 in 
    let out_17 = a_62 in 
    let out_18 = a_54 in 
    let out_19 = a_46 in 
    let out_20 = a_38 in 
    let out_21 = a_30 in 
    let out_22 = a_22 in 
    let out_23 = a_14 in 
    let out_24 = a_6 in 
    let out_25 = a_64 in 
    let out_26 = a_56 in 
    let out_27 = a_48 in 
    let out_28 = a_40 in 
    let out_29 = a_32 in 
    let out_30 = a_24 in 
    let out_31 = a_16 in 
    let out_32 = a_8 in 
    let out_33 = a_57 in 
    let out_34 = a_49 in 
    let out_35 = a_41 in 
    let out_36 = a_33 in 
    let out_37 = a_25 in 
    let out_38 = a_17 in 
    let out_39 = a_9 in 
    let out_40 = a_1 in 
    let out_41 = a_59 in 
    let out_42 = a_51 in 
    let out_43 = a_43 in 
    let out_44 = a_35 in 
    let out_45 = a_27 in 
    let out_46 = a_19 in 
    let out_47 = a_11 in 
    let out_48 = a_3 in 
    let out_49 = a_61 in 
    let out_50 = a_53 in 
    let out_51 = a_45 in 
    let out_52 = a_37 in 
    let out_53 = a_29 in 
    let out_54 = a_21 in 
    let out_55 = a_13 in 
    let out_56 = a_5 in 
    let out_57 = a_63 in 
    let out_58 = a_55 in 
    let out_59 = a_47 in 
    let out_60 = a_39 in 
    let out_61 = a_31 in 
    let out_62 = a_23 in 
    let out_63 = a_15 in 
    let out_64 = a_7 in 
    (out_1,out_2,out_3,out_4,out_5,out_6,out_7,out_8,out_9,out_10,out_11,out_12,out_13,out_14,out_15,out_16,out_17,out_18,out_19,out_20,out_21,out_22,out_23,out_24,out_25,out_26,out_27,out_28,out_29,out_30,out_31,out_32,out_33,out_34,out_35,out_36,out_37,out_38,out_39,out_40,out_41,out_42,out_43,out_44,out_45,out_46,out_47,out_48,out_49,out_50,out_51,out_52,out_53,out_54,out_55,out_56,out_57,out_58,out_59,out_60,out_61,out_62,out_63,out_64)



let final_p_ ((a_1,a_2,a_3,a_4,a_5,a_6,a_7,a_8,a_9,a_10,a_11,a_12,a_13,a_14,a_15,a_16,a_17,a_18,a_19,a_20,a_21,a_22,a_23,a_24,a_25,a_26,a_27,a_28,a_29,a_30,a_31,a_32,a_33,a_34,a_35,a_36,a_37,a_38,a_39,a_40,a_41,a_42,a_43,a_44,a_45,a_46,a_47,a_48,a_49,a_50,a_51,a_52,a_53,a_54,a_55,a_56,a_57,a_58,a_59,a_60,a_61,a_62,a_63,a_64)) = 
    let out_1 = a_40 in 
    let out_2 = a_8 in 
    let out_3 = a_48 in 
    let out_4 = a_16 in 
    let out_5 = a_56 in 
    let out_6 = a_24 in 
    let out_7 = a_64 in 
    let out_8 = a_32 in 
    let out_9 = a_39 in 
    let out_10 = a_7 in 
    let out_11 = a_47 in 
    let out_12 = a_15 in 
    let out_13 = a_55 in 
    let out_14 = a_23 in 
    let out_15 = a_63 in 
    let out_16 = a_31 in 
    let out_17 = a_38 in 
    let out_18 = a_6 in 
    let out_19 = a_46 in 
    let out_20 = a_14 in 
    let out_21 = a_54 in 
    let out_22 = a_22 in 
    let out_23 = a_62 in 
    let out_24 = a_30 in 
    let out_25 = a_37 in 
    let out_26 = a_5 in 
    let out_27 = a_45 in 
    let out_28 = a_13 in 
    let out_29 = a_53 in 
    let out_30 = a_21 in 
    let out_31 = a_61 in 
    let out_32 = a_29 in 
    let out_33 = a_36 in 
    let out_34 = a_4 in 
    let out_35 = a_44 in 
    let out_36 = a_12 in 
    let out_37 = a_52 in 
    let out_38 = a_20 in 
    let out_39 = a_60 in 
    let out_40 = a_28 in 
    let out_41 = a_35 in 
    let out_42 = a_3 in 
    let out_43 = a_43 in 
    let out_44 = a_11 in 
    let out_45 = a_51 in 
    let out_46 = a_19 in 
    let out_47 = a_59 in 
    let out_48 = a_27 in 
    let out_49 = a_34 in 
    let out_50 = a_2 in 
    let out_51 = a_42 in 
    let out_52 = a_10 in 
    let out_53 = a_50 in 
    let out_54 = a_18 in 
    let out_55 = a_58 in 
    let out_56 = a_26 in 
    let out_57 = a_33 in 
    let out_58 = a_1 in 
    let out_59 = a_41 in 
    let out_60 = a_9 in 
    let out_61 = a_49 in 
    let out_62 = a_17 in 
    let out_63 = a_57 in 
    let out_64 = a_25 in 
    (out_1,out_2,out_3,out_4,out_5,out_6,out_7,out_8,out_9,out_10,out_11,out_12,out_13,out_14,out_15,out_16,out_17,out_18,out_19,out_20,out_21,out_22,out_23,out_24,out_25,out_26,out_27,out_28,out_29,out_30,out_31,out_32,out_33,out_34,out_35,out_36,out_37,out_38,out_39,out_40,out_41,out_42,out_43,out_44,out_45,out_46,out_47,out_48,out_49,out_50,out_51,out_52,out_53,out_54,out_55,out_56,out_57,out_58,out_59,out_60,out_61,out_62,out_63,out_64)



let permut_ ((a_1,a_2,a_3,a_4,a_5,a_6,a_7,a_8,a_9,a_10,a_11,a_12,a_13,a_14,a_15,a_16,a_17,a_18,a_19,a_20,a_21,a_22,a_23,a_24,a_25,a_26,a_27,a_28,a_29,a_30,a_31,a_32)) = 
    let out_1 = a_16 in 
    let out_2 = a_7 in 
    let out_3 = a_20 in 
    let out_4 = a_21 in 
    let out_5 = a_29 in 
    let out_6 = a_12 in 
    let out_7 = a_28 in 
    let out_8 = a_17 in 
    let out_9 = a_1 in 
    let out_10 = a_15 in 
    let out_11 = a_23 in 
    let out_12 = a_26 in 
    let out_13 = a_5 in 
    let out_14 = a_18 in 
    let out_15 = a_31 in 
    let out_16 = a_10 in 
    let out_17 = a_2 in 
    let out_18 = a_8 in 
    let out_19 = a_24 in 
    let out_20 = a_14 in 
    let out_21 = a_32 in 
    let out_22 = a_27 in 
    let out_23 = a_3 in 
    let out_24 = a_9 in 
    let out_25 = a_19 in 
    let out_26 = a_13 in 
    let out_27 = a_30 in 
    let out_28 = a_6 in 
    let out_29 = a_22 in 
    let out_30 = a_11 in 
    let out_31 = a_4 in 
    let out_32 = a_25 in 
    (out_1,out_2,out_3,out_4,out_5,out_6,out_7,out_8,out_9,out_10,out_11,out_12,out_13,out_14,out_15,out_16,out_17,out_18,out_19,out_20,out_21,out_22,out_23,out_24,out_25,out_26,out_27,out_28,out_29,out_30,out_31,out_32)



let roundkey1_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_10 in 
    let roundkey_2 = key_51 in 
    let roundkey_3 = key_34 in 
    let roundkey_4 = key_60 in 
    let roundkey_5 = key_49 in 
    let roundkey_6 = key_17 in 
    let roundkey_7 = key_33 in 
    let roundkey_8 = key_57 in 
    let roundkey_9 = key_2 in 
    let roundkey_10 = key_9 in 
    let roundkey_11 = key_19 in 
    let roundkey_12 = key_42 in 
    let roundkey_13 = key_3 in 
    let roundkey_14 = key_35 in 
    let roundkey_15 = key_26 in 
    let roundkey_16 = key_25 in 
    let roundkey_17 = key_44 in 
    let roundkey_18 = key_58 in 
    let roundkey_19 = key_59 in 
    let roundkey_20 = key_1 in 
    let roundkey_21 = key_36 in 
    let roundkey_22 = key_27 in 
    let roundkey_23 = key_18 in 
    let roundkey_24 = key_41 in 
    let roundkey_25 = key_22 in 
    let roundkey_26 = key_28 in 
    let roundkey_27 = key_39 in 
    let roundkey_28 = key_54 in 
    let roundkey_29 = key_37 in 
    let roundkey_30 = key_4 in 
    let roundkey_31 = key_47 in 
    let roundkey_32 = key_30 in 
    let roundkey_33 = key_5 in 
    let roundkey_34 = key_53 in 
    let roundkey_35 = key_23 in 
    let roundkey_36 = key_29 in 
    let roundkey_37 = key_61 in 
    let roundkey_38 = key_21 in 
    let roundkey_39 = key_38 in 
    let roundkey_40 = key_63 in 
    let roundkey_41 = key_15 in 
    let roundkey_42 = key_20 in 
    let roundkey_43 = key_45 in 
    let roundkey_44 = key_14 in 
    let roundkey_45 = key_13 in 
    let roundkey_46 = key_62 in 
    let roundkey_47 = key_55 in 
    let roundkey_48 = key_31 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey2_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_2 in 
    let roundkey_2 = key_43 in 
    let roundkey_3 = key_26 in 
    let roundkey_4 = key_52 in 
    let roundkey_5 = key_41 in 
    let roundkey_6 = key_9 in 
    let roundkey_7 = key_25 in 
    let roundkey_8 = key_49 in 
    let roundkey_9 = key_59 in 
    let roundkey_10 = key_1 in 
    let roundkey_11 = key_11 in 
    let roundkey_12 = key_34 in 
    let roundkey_13 = key_60 in 
    let roundkey_14 = key_27 in 
    let roundkey_15 = key_18 in 
    let roundkey_16 = key_17 in 
    let roundkey_17 = key_36 in 
    let roundkey_18 = key_50 in 
    let roundkey_19 = key_51 in 
    let roundkey_20 = key_58 in 
    let roundkey_21 = key_57 in 
    let roundkey_22 = key_19 in 
    let roundkey_23 = key_10 in 
    let roundkey_24 = key_33 in 
    let roundkey_25 = key_14 in 
    let roundkey_26 = key_20 in 
    let roundkey_27 = key_31 in 
    let roundkey_28 = key_46 in 
    let roundkey_29 = key_29 in 
    let roundkey_30 = key_63 in 
    let roundkey_31 = key_39 in 
    let roundkey_32 = key_22 in 
    let roundkey_33 = key_28 in 
    let roundkey_34 = key_45 in 
    let roundkey_35 = key_15 in 
    let roundkey_36 = key_21 in 
    let roundkey_37 = key_53 in 
    let roundkey_38 = key_13 in 
    let roundkey_39 = key_30 in 
    let roundkey_40 = key_55 in 
    let roundkey_41 = key_7 in 
    let roundkey_42 = key_12 in 
    let roundkey_43 = key_37 in 
    let roundkey_44 = key_6 in 
    let roundkey_45 = key_5 in 
    let roundkey_46 = key_54 in 
    let roundkey_47 = key_47 in 
    let roundkey_48 = key_23 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey3_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_51 in 
    let roundkey_2 = key_27 in 
    let roundkey_3 = key_10 in 
    let roundkey_4 = key_36 in 
    let roundkey_5 = key_25 in 
    let roundkey_6 = key_58 in 
    let roundkey_7 = key_9 in 
    let roundkey_8 = key_33 in 
    let roundkey_9 = key_43 in 
    let roundkey_10 = key_50 in 
    let roundkey_11 = key_60 in 
    let roundkey_12 = key_18 in 
    let roundkey_13 = key_44 in 
    let roundkey_14 = key_11 in 
    let roundkey_15 = key_2 in 
    let roundkey_16 = key_1 in 
    let roundkey_17 = key_49 in 
    let roundkey_18 = key_34 in 
    let roundkey_19 = key_35 in 
    let roundkey_20 = key_42 in 
    let roundkey_21 = key_41 in 
    let roundkey_22 = key_3 in 
    let roundkey_23 = key_59 in 
    let roundkey_24 = key_17 in 
    let roundkey_25 = key_61 in 
    let roundkey_26 = key_4 in 
    let roundkey_27 = key_15 in 
    let roundkey_28 = key_30 in 
    let roundkey_29 = key_13 in 
    let roundkey_30 = key_47 in 
    let roundkey_31 = key_23 in 
    let roundkey_32 = key_6 in 
    let roundkey_33 = key_12 in 
    let roundkey_34 = key_29 in 
    let roundkey_35 = key_62 in 
    let roundkey_36 = key_5 in 
    let roundkey_37 = key_37 in 
    let roundkey_38 = key_28 in 
    let roundkey_39 = key_14 in 
    let roundkey_40 = key_39 in 
    let roundkey_41 = key_54 in 
    let roundkey_42 = key_63 in 
    let roundkey_43 = key_21 in 
    let roundkey_44 = key_53 in 
    let roundkey_45 = key_20 in 
    let roundkey_46 = key_38 in 
    let roundkey_47 = key_31 in 
    let roundkey_48 = key_7 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey4_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_35 in 
    let roundkey_2 = key_11 in 
    let roundkey_3 = key_59 in 
    let roundkey_4 = key_49 in 
    let roundkey_5 = key_9 in 
    let roundkey_6 = key_42 in 
    let roundkey_7 = key_58 in 
    let roundkey_8 = key_17 in 
    let roundkey_9 = key_27 in 
    let roundkey_10 = key_34 in 
    let roundkey_11 = key_44 in 
    let roundkey_12 = key_2 in 
    let roundkey_13 = key_57 in 
    let roundkey_14 = key_60 in 
    let roundkey_15 = key_51 in 
    let roundkey_16 = key_50 in 
    let roundkey_17 = key_33 in 
    let roundkey_18 = key_18 in 
    let roundkey_19 = key_19 in 
    let roundkey_20 = key_26 in 
    let roundkey_21 = key_25 in 
    let roundkey_22 = key_52 in 
    let roundkey_23 = key_43 in 
    let roundkey_24 = key_1 in 
    let roundkey_25 = key_45 in 
    let roundkey_26 = key_55 in 
    let roundkey_27 = key_62 in 
    let roundkey_28 = key_14 in 
    let roundkey_29 = key_28 in 
    let roundkey_30 = key_31 in 
    let roundkey_31 = key_7 in 
    let roundkey_32 = key_53 in 
    let roundkey_33 = key_63 in 
    let roundkey_34 = key_13 in 
    let roundkey_35 = key_46 in 
    let roundkey_36 = key_20 in 
    let roundkey_37 = key_21 in 
    let roundkey_38 = key_12 in 
    let roundkey_39 = key_61 in 
    let roundkey_40 = key_23 in 
    let roundkey_41 = key_38 in 
    let roundkey_42 = key_47 in 
    let roundkey_43 = key_5 in 
    let roundkey_44 = key_37 in 
    let roundkey_45 = key_4 in 
    let roundkey_46 = key_22 in 
    let roundkey_47 = key_15 in 
    let roundkey_48 = key_54 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey5_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_19 in 
    let roundkey_2 = key_60 in 
    let roundkey_3 = key_43 in 
    let roundkey_4 = key_33 in 
    let roundkey_5 = key_58 in 
    let roundkey_6 = key_26 in 
    let roundkey_7 = key_42 in 
    let roundkey_8 = key_1 in 
    let roundkey_9 = key_11 in 
    let roundkey_10 = key_18 in 
    let roundkey_11 = key_57 in 
    let roundkey_12 = key_51 in 
    let roundkey_13 = key_41 in 
    let roundkey_14 = key_44 in 
    let roundkey_15 = key_35 in 
    let roundkey_16 = key_34 in 
    let roundkey_17 = key_17 in 
    let roundkey_18 = key_2 in 
    let roundkey_19 = key_3 in 
    let roundkey_20 = key_10 in 
    let roundkey_21 = key_9 in 
    let roundkey_22 = key_36 in 
    let roundkey_23 = key_27 in 
    let roundkey_24 = key_50 in 
    let roundkey_25 = key_29 in 
    let roundkey_26 = key_39 in 
    let roundkey_27 = key_46 in 
    let roundkey_28 = key_61 in 
    let roundkey_29 = key_12 in 
    let roundkey_30 = key_15 in 
    let roundkey_31 = key_54 in 
    let roundkey_32 = key_37 in 
    let roundkey_33 = key_47 in 
    let roundkey_34 = key_28 in 
    let roundkey_35 = key_30 in 
    let roundkey_36 = key_4 in 
    let roundkey_37 = key_5 in 
    let roundkey_38 = key_63 in 
    let roundkey_39 = key_45 in 
    let roundkey_40 = key_7 in 
    let roundkey_41 = key_22 in 
    let roundkey_42 = key_31 in 
    let roundkey_43 = key_20 in 
    let roundkey_44 = key_21 in 
    let roundkey_45 = key_55 in 
    let roundkey_46 = key_6 in 
    let roundkey_47 = key_62 in 
    let roundkey_48 = key_38 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey6_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_3 in 
    let roundkey_2 = key_44 in 
    let roundkey_3 = key_27 in 
    let roundkey_4 = key_17 in 
    let roundkey_5 = key_42 in 
    let roundkey_6 = key_10 in 
    let roundkey_7 = key_26 in 
    let roundkey_8 = key_50 in 
    let roundkey_9 = key_60 in 
    let roundkey_10 = key_2 in 
    let roundkey_11 = key_41 in 
    let roundkey_12 = key_35 in 
    let roundkey_13 = key_25 in 
    let roundkey_14 = key_57 in 
    let roundkey_15 = key_19 in 
    let roundkey_16 = key_18 in 
    let roundkey_17 = key_1 in 
    let roundkey_18 = key_51 in 
    let roundkey_19 = key_52 in 
    let roundkey_20 = key_59 in 
    let roundkey_21 = key_58 in 
    let roundkey_22 = key_49 in 
    let roundkey_23 = key_11 in 
    let roundkey_24 = key_34 in 
    let roundkey_25 = key_13 in 
    let roundkey_26 = key_23 in 
    let roundkey_27 = key_30 in 
    let roundkey_28 = key_45 in 
    let roundkey_29 = key_63 in 
    let roundkey_30 = key_62 in 
    let roundkey_31 = key_38 in 
    let roundkey_32 = key_21 in 
    let roundkey_33 = key_31 in 
    let roundkey_34 = key_12 in 
    let roundkey_35 = key_14 in 
    let roundkey_36 = key_55 in 
    let roundkey_37 = key_20 in 
    let roundkey_38 = key_47 in 
    let roundkey_39 = key_29 in 
    let roundkey_40 = key_54 in 
    let roundkey_41 = key_6 in 
    let roundkey_42 = key_15 in 
    let roundkey_43 = key_4 in 
    let roundkey_44 = key_5 in 
    let roundkey_45 = key_39 in 
    let roundkey_46 = key_53 in 
    let roundkey_47 = key_46 in 
    let roundkey_48 = key_22 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey7_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_52 in 
    let roundkey_2 = key_57 in 
    let roundkey_3 = key_11 in 
    let roundkey_4 = key_1 in 
    let roundkey_5 = key_26 in 
    let roundkey_6 = key_59 in 
    let roundkey_7 = key_10 in 
    let roundkey_8 = key_34 in 
    let roundkey_9 = key_44 in 
    let roundkey_10 = key_51 in 
    let roundkey_11 = key_25 in 
    let roundkey_12 = key_19 in 
    let roundkey_13 = key_9 in 
    let roundkey_14 = key_41 in 
    let roundkey_15 = key_3 in 
    let roundkey_16 = key_2 in 
    let roundkey_17 = key_50 in 
    let roundkey_18 = key_35 in 
    let roundkey_19 = key_36 in 
    let roundkey_20 = key_43 in 
    let roundkey_21 = key_42 in 
    let roundkey_22 = key_33 in 
    let roundkey_23 = key_60 in 
    let roundkey_24 = key_18 in 
    let roundkey_25 = key_28 in 
    let roundkey_26 = key_7 in 
    let roundkey_27 = key_14 in 
    let roundkey_28 = key_29 in 
    let roundkey_29 = key_47 in 
    let roundkey_30 = key_46 in 
    let roundkey_31 = key_22 in 
    let roundkey_32 = key_5 in 
    let roundkey_33 = key_15 in 
    let roundkey_34 = key_63 in 
    let roundkey_35 = key_61 in 
    let roundkey_36 = key_39 in 
    let roundkey_37 = key_4 in 
    let roundkey_38 = key_31 in 
    let roundkey_39 = key_13 in 
    let roundkey_40 = key_38 in 
    let roundkey_41 = key_53 in 
    let roundkey_42 = key_62 in 
    let roundkey_43 = key_55 in 
    let roundkey_44 = key_20 in 
    let roundkey_45 = key_23 in 
    let roundkey_46 = key_37 in 
    let roundkey_47 = key_30 in 
    let roundkey_48 = key_6 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey8_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_36 in 
    let roundkey_2 = key_41 in 
    let roundkey_3 = key_60 in 
    let roundkey_4 = key_50 in 
    let roundkey_5 = key_10 in 
    let roundkey_6 = key_43 in 
    let roundkey_7 = key_59 in 
    let roundkey_8 = key_18 in 
    let roundkey_9 = key_57 in 
    let roundkey_10 = key_35 in 
    let roundkey_11 = key_9 in 
    let roundkey_12 = key_3 in 
    let roundkey_13 = key_58 in 
    let roundkey_14 = key_25 in 
    let roundkey_15 = key_52 in 
    let roundkey_16 = key_51 in 
    let roundkey_17 = key_34 in 
    let roundkey_18 = key_19 in 
    let roundkey_19 = key_49 in 
    let roundkey_20 = key_27 in 
    let roundkey_21 = key_26 in 
    let roundkey_22 = key_17 in 
    let roundkey_23 = key_44 in 
    let roundkey_24 = key_2 in 
    let roundkey_25 = key_12 in 
    let roundkey_26 = key_54 in 
    let roundkey_27 = key_61 in 
    let roundkey_28 = key_13 in 
    let roundkey_29 = key_31 in 
    let roundkey_30 = key_30 in 
    let roundkey_31 = key_6 in 
    let roundkey_32 = key_20 in 
    let roundkey_33 = key_62 in 
    let roundkey_34 = key_47 in 
    let roundkey_35 = key_45 in 
    let roundkey_36 = key_23 in 
    let roundkey_37 = key_55 in 
    let roundkey_38 = key_15 in 
    let roundkey_39 = key_28 in 
    let roundkey_40 = key_22 in 
    let roundkey_41 = key_37 in 
    let roundkey_42 = key_46 in 
    let roundkey_43 = key_39 in 
    let roundkey_44 = key_4 in 
    let roundkey_45 = key_7 in 
    let roundkey_46 = key_21 in 
    let roundkey_47 = key_14 in 
    let roundkey_48 = key_53 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey9_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_57 in 
    let roundkey_2 = key_33 in 
    let roundkey_3 = key_52 in 
    let roundkey_4 = key_42 in 
    let roundkey_5 = key_2 in 
    let roundkey_6 = key_35 in 
    let roundkey_7 = key_51 in 
    let roundkey_8 = key_10 in 
    let roundkey_9 = key_49 in 
    let roundkey_10 = key_27 in 
    let roundkey_11 = key_1 in 
    let roundkey_12 = key_60 in 
    let roundkey_13 = key_50 in 
    let roundkey_14 = key_17 in 
    let roundkey_15 = key_44 in 
    let roundkey_16 = key_43 in 
    let roundkey_17 = key_26 in 
    let roundkey_18 = key_11 in 
    let roundkey_19 = key_41 in 
    let roundkey_20 = key_19 in 
    let roundkey_21 = key_18 in 
    let roundkey_22 = key_9 in 
    let roundkey_23 = key_36 in 
    let roundkey_24 = key_59 in 
    let roundkey_25 = key_4 in 
    let roundkey_26 = key_46 in 
    let roundkey_27 = key_53 in 
    let roundkey_28 = key_5 in 
    let roundkey_29 = key_23 in 
    let roundkey_30 = key_22 in 
    let roundkey_31 = key_61 in 
    let roundkey_32 = key_12 in 
    let roundkey_33 = key_54 in 
    let roundkey_34 = key_39 in 
    let roundkey_35 = key_37 in 
    let roundkey_36 = key_15 in 
    let roundkey_37 = key_47 in 
    let roundkey_38 = key_7 in 
    let roundkey_39 = key_20 in 
    let roundkey_40 = key_14 in 
    let roundkey_41 = key_29 in 
    let roundkey_42 = key_38 in 
    let roundkey_43 = key_31 in 
    let roundkey_44 = key_63 in 
    let roundkey_45 = key_62 in 
    let roundkey_46 = key_13 in 
    let roundkey_47 = key_6 in 
    let roundkey_48 = key_45 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey10_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_41 in 
    let roundkey_2 = key_17 in 
    let roundkey_3 = key_36 in 
    let roundkey_4 = key_26 in 
    let roundkey_5 = key_51 in 
    let roundkey_6 = key_19 in 
    let roundkey_7 = key_35 in 
    let roundkey_8 = key_59 in 
    let roundkey_9 = key_33 in 
    let roundkey_10 = key_11 in 
    let roundkey_11 = key_50 in 
    let roundkey_12 = key_44 in 
    let roundkey_13 = key_34 in 
    let roundkey_14 = key_1 in 
    let roundkey_15 = key_57 in 
    let roundkey_16 = key_27 in 
    let roundkey_17 = key_10 in 
    let roundkey_18 = key_60 in 
    let roundkey_19 = key_25 in 
    let roundkey_20 = key_3 in 
    let roundkey_21 = key_2 in 
    let roundkey_22 = key_58 in 
    let roundkey_23 = key_49 in 
    let roundkey_24 = key_43 in 
    let roundkey_25 = key_55 in 
    let roundkey_26 = key_30 in 
    let roundkey_27 = key_37 in 
    let roundkey_28 = key_20 in 
    let roundkey_29 = key_7 in 
    let roundkey_30 = key_6 in 
    let roundkey_31 = key_45 in 
    let roundkey_32 = key_63 in 
    let roundkey_33 = key_38 in 
    let roundkey_34 = key_23 in 
    let roundkey_35 = key_21 in 
    let roundkey_36 = key_62 in 
    let roundkey_37 = key_31 in 
    let roundkey_38 = key_54 in 
    let roundkey_39 = key_4 in 
    let roundkey_40 = key_61 in 
    let roundkey_41 = key_13 in 
    let roundkey_42 = key_22 in 
    let roundkey_43 = key_15 in 
    let roundkey_44 = key_47 in 
    let roundkey_45 = key_46 in 
    let roundkey_46 = key_28 in 
    let roundkey_47 = key_53 in 
    let roundkey_48 = key_29 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey11_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_25 in 
    let roundkey_2 = key_1 in 
    let roundkey_3 = key_49 in 
    let roundkey_4 = key_10 in 
    let roundkey_5 = key_35 in 
    let roundkey_6 = key_3 in 
    let roundkey_7 = key_19 in 
    let roundkey_8 = key_43 in 
    let roundkey_9 = key_17 in 
    let roundkey_10 = key_60 in 
    let roundkey_11 = key_34 in 
    let roundkey_12 = key_57 in 
    let roundkey_13 = key_18 in 
    let roundkey_14 = key_50 in 
    let roundkey_15 = key_41 in 
    let roundkey_16 = key_11 in 
    let roundkey_17 = key_59 in 
    let roundkey_18 = key_44 in 
    let roundkey_19 = key_9 in 
    let roundkey_20 = key_52 in 
    let roundkey_21 = key_51 in 
    let roundkey_22 = key_42 in 
    let roundkey_23 = key_33 in 
    let roundkey_24 = key_27 in 
    let roundkey_25 = key_39 in 
    let roundkey_26 = key_14 in 
    let roundkey_27 = key_21 in 
    let roundkey_28 = key_4 in 
    let roundkey_29 = key_54 in 
    let roundkey_30 = key_53 in 
    let roundkey_31 = key_29 in 
    let roundkey_32 = key_47 in 
    let roundkey_33 = key_22 in 
    let roundkey_34 = key_7 in 
    let roundkey_35 = key_5 in 
    let roundkey_36 = key_46 in 
    let roundkey_37 = key_15 in 
    let roundkey_38 = key_38 in 
    let roundkey_39 = key_55 in 
    let roundkey_40 = key_45 in 
    let roundkey_41 = key_28 in 
    let roundkey_42 = key_6 in 
    let roundkey_43 = key_62 in 
    let roundkey_44 = key_31 in 
    let roundkey_45 = key_30 in 
    let roundkey_46 = key_12 in 
    let roundkey_47 = key_37 in 
    let roundkey_48 = key_13 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey12_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_9 in 
    let roundkey_2 = key_50 in 
    let roundkey_3 = key_33 in 
    let roundkey_4 = key_59 in 
    let roundkey_5 = key_19 in 
    let roundkey_6 = key_52 in 
    let roundkey_7 = key_3 in 
    let roundkey_8 = key_27 in 
    let roundkey_9 = key_1 in 
    let roundkey_10 = key_44 in 
    let roundkey_11 = key_18 in 
    let roundkey_12 = key_41 in 
    let roundkey_13 = key_2 in 
    let roundkey_14 = key_34 in 
    let roundkey_15 = key_25 in 
    let roundkey_16 = key_60 in 
    let roundkey_17 = key_43 in 
    let roundkey_18 = key_57 in 
    let roundkey_19 = key_58 in 
    let roundkey_20 = key_36 in 
    let roundkey_21 = key_35 in 
    let roundkey_22 = key_26 in 
    let roundkey_23 = key_17 in 
    let roundkey_24 = key_11 in 
    let roundkey_25 = key_23 in 
    let roundkey_26 = key_61 in 
    let roundkey_27 = key_5 in 
    let roundkey_28 = key_55 in 
    let roundkey_29 = key_38 in 
    let roundkey_30 = key_37 in 
    let roundkey_31 = key_13 in 
    let roundkey_32 = key_31 in 
    let roundkey_33 = key_6 in 
    let roundkey_34 = key_54 in 
    let roundkey_35 = key_20 in 
    let roundkey_36 = key_30 in 
    let roundkey_37 = key_62 in 
    let roundkey_38 = key_22 in 
    let roundkey_39 = key_39 in 
    let roundkey_40 = key_29 in 
    let roundkey_41 = key_12 in 
    let roundkey_42 = key_53 in 
    let roundkey_43 = key_46 in 
    let roundkey_44 = key_15 in 
    let roundkey_45 = key_14 in 
    let roundkey_46 = key_63 in 
    let roundkey_47 = key_21 in 
    let roundkey_48 = key_28 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey13_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_58 in 
    let roundkey_2 = key_34 in 
    let roundkey_3 = key_17 in 
    let roundkey_4 = key_43 in 
    let roundkey_5 = key_3 in 
    let roundkey_6 = key_36 in 
    let roundkey_7 = key_52 in 
    let roundkey_8 = key_11 in 
    let roundkey_9 = key_50 in 
    let roundkey_10 = key_57 in 
    let roundkey_11 = key_2 in 
    let roundkey_12 = key_25 in 
    let roundkey_13 = key_51 in 
    let roundkey_14 = key_18 in 
    let roundkey_15 = key_9 in 
    let roundkey_16 = key_44 in 
    let roundkey_17 = key_27 in 
    let roundkey_18 = key_41 in 
    let roundkey_19 = key_42 in 
    let roundkey_20 = key_49 in 
    let roundkey_21 = key_19 in 
    let roundkey_22 = key_10 in 
    let roundkey_23 = key_1 in 
    let roundkey_24 = key_60 in 
    let roundkey_25 = key_7 in 
    let roundkey_26 = key_45 in 
    let roundkey_27 = key_20 in 
    let roundkey_28 = key_39 in 
    let roundkey_29 = key_22 in 
    let roundkey_30 = key_21 in 
    let roundkey_31 = key_28 in 
    let roundkey_32 = key_15 in 
    let roundkey_33 = key_53 in 
    let roundkey_34 = key_38 in 
    let roundkey_35 = key_4 in 
    let roundkey_36 = key_14 in 
    let roundkey_37 = key_46 in 
    let roundkey_38 = key_6 in 
    let roundkey_39 = key_23 in 
    let roundkey_40 = key_13 in 
    let roundkey_41 = key_63 in 
    let roundkey_42 = key_37 in 
    let roundkey_43 = key_30 in 
    let roundkey_44 = key_62 in 
    let roundkey_45 = key_61 in 
    let roundkey_46 = key_47 in 
    let roundkey_47 = key_5 in 
    let roundkey_48 = key_12 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey14_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_42 in 
    let roundkey_2 = key_18 in 
    let roundkey_3 = key_1 in 
    let roundkey_4 = key_27 in 
    let roundkey_5 = key_52 in 
    let roundkey_6 = key_49 in 
    let roundkey_7 = key_36 in 
    let roundkey_8 = key_60 in 
    let roundkey_9 = key_34 in 
    let roundkey_10 = key_41 in 
    let roundkey_11 = key_51 in 
    let roundkey_12 = key_9 in 
    let roundkey_13 = key_35 in 
    let roundkey_14 = key_2 in 
    let roundkey_15 = key_58 in 
    let roundkey_16 = key_57 in 
    let roundkey_17 = key_11 in 
    let roundkey_18 = key_25 in 
    let roundkey_19 = key_26 in 
    let roundkey_20 = key_33 in 
    let roundkey_21 = key_3 in 
    let roundkey_22 = key_59 in 
    let roundkey_23 = key_50 in 
    let roundkey_24 = key_44 in 
    let roundkey_25 = key_54 in 
    let roundkey_26 = key_29 in 
    let roundkey_27 = key_4 in 
    let roundkey_28 = key_23 in 
    let roundkey_29 = key_6 in 
    let roundkey_30 = key_5 in 
    let roundkey_31 = key_12 in 
    let roundkey_32 = key_62 in 
    let roundkey_33 = key_37 in 
    let roundkey_34 = key_22 in 
    let roundkey_35 = key_55 in 
    let roundkey_36 = key_61 in 
    let roundkey_37 = key_30 in 
    let roundkey_38 = key_53 in 
    let roundkey_39 = key_7 in 
    let roundkey_40 = key_28 in 
    let roundkey_41 = key_47 in 
    let roundkey_42 = key_21 in 
    let roundkey_43 = key_14 in 
    let roundkey_44 = key_46 in 
    let roundkey_45 = key_45 in 
    let roundkey_46 = key_31 in 
    let roundkey_47 = key_20 in 
    let roundkey_48 = key_63 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey15_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_26 in 
    let roundkey_2 = key_2 in 
    let roundkey_3 = key_50 in 
    let roundkey_4 = key_11 in 
    let roundkey_5 = key_36 in 
    let roundkey_6 = key_33 in 
    let roundkey_7 = key_49 in 
    let roundkey_8 = key_44 in 
    let roundkey_9 = key_18 in 
    let roundkey_10 = key_25 in 
    let roundkey_11 = key_35 in 
    let roundkey_12 = key_58 in 
    let roundkey_13 = key_19 in 
    let roundkey_14 = key_51 in 
    let roundkey_15 = key_42 in 
    let roundkey_16 = key_41 in 
    let roundkey_17 = key_60 in 
    let roundkey_18 = key_9 in 
    let roundkey_19 = key_10 in 
    let roundkey_20 = key_17 in 
    let roundkey_21 = key_52 in 
    let roundkey_22 = key_43 in 
    let roundkey_23 = key_34 in 
    let roundkey_24 = key_57 in 
    let roundkey_25 = key_38 in 
    let roundkey_26 = key_13 in 
    let roundkey_27 = key_55 in 
    let roundkey_28 = key_7 in 
    let roundkey_29 = key_53 in 
    let roundkey_30 = key_20 in 
    let roundkey_31 = key_63 in 
    let roundkey_32 = key_46 in 
    let roundkey_33 = key_21 in 
    let roundkey_34 = key_6 in 
    let roundkey_35 = key_39 in 
    let roundkey_36 = key_45 in 
    let roundkey_37 = key_14 in 
    let roundkey_38 = key_37 in 
    let roundkey_39 = key_54 in 
    let roundkey_40 = key_12 in 
    let roundkey_41 = key_31 in 
    let roundkey_42 = key_5 in 
    let roundkey_43 = key_61 in 
    let roundkey_44 = key_30 in 
    let roundkey_45 = key_29 in 
    let roundkey_46 = key_15 in 
    let roundkey_47 = key_4 in 
    let roundkey_48 = key_47 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let roundkey16_ ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let roundkey_1 = key_18 in 
    let roundkey_2 = key_59 in 
    let roundkey_3 = key_42 in 
    let roundkey_4 = key_3 in 
    let roundkey_5 = key_57 in 
    let roundkey_6 = key_25 in 
    let roundkey_7 = key_41 in 
    let roundkey_8 = key_36 in 
    let roundkey_9 = key_10 in 
    let roundkey_10 = key_17 in 
    let roundkey_11 = key_27 in 
    let roundkey_12 = key_50 in 
    let roundkey_13 = key_11 in 
    let roundkey_14 = key_43 in 
    let roundkey_15 = key_34 in 
    let roundkey_16 = key_33 in 
    let roundkey_17 = key_52 in 
    let roundkey_18 = key_1 in 
    let roundkey_19 = key_2 in 
    let roundkey_20 = key_9 in 
    let roundkey_21 = key_44 in 
    let roundkey_22 = key_35 in 
    let roundkey_23 = key_26 in 
    let roundkey_24 = key_49 in 
    let roundkey_25 = key_30 in 
    let roundkey_26 = key_5 in 
    let roundkey_27 = key_47 in 
    let roundkey_28 = key_62 in 
    let roundkey_29 = key_45 in 
    let roundkey_30 = key_12 in 
    let roundkey_31 = key_55 in 
    let roundkey_32 = key_38 in 
    let roundkey_33 = key_13 in 
    let roundkey_34 = key_61 in 
    let roundkey_35 = key_31 in 
    let roundkey_36 = key_37 in 
    let roundkey_37 = key_6 in 
    let roundkey_38 = key_29 in 
    let roundkey_39 = key_46 in 
    let roundkey_40 = key_4 in 
    let roundkey_41 = key_23 in 
    let roundkey_42 = key_28 in 
    let roundkey_43 = key_53 in 
    let roundkey_44 = key_22 in 
    let roundkey_45 = key_21 in 
    let roundkey_46 = key_7 in 
    let roundkey_47 = key_63 in 
    let roundkey_48 = key_39 in 
    (roundkey_1,roundkey_2,roundkey_3,roundkey_4,roundkey_5,roundkey_6,roundkey_7,roundkey_8,roundkey_9,roundkey_10,roundkey_11,roundkey_12,roundkey_13,roundkey_14,roundkey_15,roundkey_16,roundkey_17,roundkey_18,roundkey_19,roundkey_20,roundkey_21,roundkey_22,roundkey_23,roundkey_24,roundkey_25,roundkey_26,roundkey_27,roundkey_28,roundkey_29,roundkey_30,roundkey_31,roundkey_32,roundkey_33,roundkey_34,roundkey_35,roundkey_36,roundkey_37,roundkey_38,roundkey_39,roundkey_40,roundkey_41,roundkey_42,roundkey_43,roundkey_44,roundkey_45,roundkey_46,roundkey_47,roundkey_48)



let des_single1_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp1_1,__tmp1_2,__tmp1_3,__tmp1_4,__tmp1_5,__tmp1_6,__tmp1_7,__tmp1_8,__tmp1_9,__tmp1_10,__tmp1_11,__tmp1_12,__tmp1_13,__tmp1_14,__tmp1_15,__tmp1_16,__tmp1_17,__tmp1_18,__tmp1_19,__tmp1_20,__tmp1_21,__tmp1_22,__tmp1_23,__tmp1_24,__tmp1_25,__tmp1_26,__tmp1_27,__tmp1_28,__tmp1_29,__tmp1_30,__tmp1_31,__tmp1_32,__tmp1_33,__tmp1_34,__tmp1_35,__tmp1_36,__tmp1_37,__tmp1_38,__tmp1_39,__tmp1_40,__tmp1_41,__tmp1_42,__tmp1_43,__tmp1_44,__tmp1_45,__tmp1_46,__tmp1_47,__tmp1_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp2_1,__tmp2_2,__tmp2_3,__tmp2_4,__tmp2_5,__tmp2_6,__tmp2_7,__tmp2_8,__tmp2_9,__tmp2_10,__tmp2_11,__tmp2_12,__tmp2_13,__tmp2_14,__tmp2_15,__tmp2_16,__tmp2_17,__tmp2_18,__tmp2_19,__tmp2_20,__tmp2_21,__tmp2_22,__tmp2_23,__tmp2_24,__tmp2_25,__tmp2_26,__tmp2_27,__tmp2_28,__tmp2_29,__tmp2_30,__tmp2_31,__tmp2_32,__tmp2_33,__tmp2_34,__tmp2_35,__tmp2_36,__tmp2_37,__tmp2_38,__tmp2_39,__tmp2_40,__tmp2_41,__tmp2_42,__tmp2_43,__tmp2_44,__tmp2_45,__tmp2_46,__tmp2_47,__tmp2_48) = roundkey1_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp1_1) land ((lnot (__tmp2_1)))) lor (((lnot (__tmp1_1))) land (__tmp2_1)),((__tmp1_2) land ((lnot (__tmp2_2)))) lor (((lnot (__tmp1_2))) land (__tmp2_2)),((__tmp1_3) land ((lnot (__tmp2_3)))) lor (((lnot (__tmp1_3))) land (__tmp2_3)),((__tmp1_4) land ((lnot (__tmp2_4)))) lor (((lnot (__tmp1_4))) land (__tmp2_4)),((__tmp1_5) land ((lnot (__tmp2_5)))) lor (((lnot (__tmp1_5))) land (__tmp2_5)),((__tmp1_6) land ((lnot (__tmp2_6)))) lor (((lnot (__tmp1_6))) land (__tmp2_6)),((__tmp1_7) land ((lnot (__tmp2_7)))) lor (((lnot (__tmp1_7))) land (__tmp2_7)),((__tmp1_8) land ((lnot (__tmp2_8)))) lor (((lnot (__tmp1_8))) land (__tmp2_8)),((__tmp1_9) land ((lnot (__tmp2_9)))) lor (((lnot (__tmp1_9))) land (__tmp2_9)),((__tmp1_10) land ((lnot (__tmp2_10)))) lor (((lnot (__tmp1_10))) land (__tmp2_10)),((__tmp1_11) land ((lnot (__tmp2_11)))) lor (((lnot (__tmp1_11))) land (__tmp2_11)),((__tmp1_12) land ((lnot (__tmp2_12)))) lor (((lnot (__tmp1_12))) land (__tmp2_12)),((__tmp1_13) land ((lnot (__tmp2_13)))) lor (((lnot (__tmp1_13))) land (__tmp2_13)),((__tmp1_14) land ((lnot (__tmp2_14)))) lor (((lnot (__tmp1_14))) land (__tmp2_14)),((__tmp1_15) land ((lnot (__tmp2_15)))) lor (((lnot (__tmp1_15))) land (__tmp2_15)),((__tmp1_16) land ((lnot (__tmp2_16)))) lor (((lnot (__tmp1_16))) land (__tmp2_16)),((__tmp1_17) land ((lnot (__tmp2_17)))) lor (((lnot (__tmp1_17))) land (__tmp2_17)),((__tmp1_18) land ((lnot (__tmp2_18)))) lor (((lnot (__tmp1_18))) land (__tmp2_18)),((__tmp1_19) land ((lnot (__tmp2_19)))) lor (((lnot (__tmp1_19))) land (__tmp2_19)),((__tmp1_20) land ((lnot (__tmp2_20)))) lor (((lnot (__tmp1_20))) land (__tmp2_20)),((__tmp1_21) land ((lnot (__tmp2_21)))) lor (((lnot (__tmp1_21))) land (__tmp2_21)),((__tmp1_22) land ((lnot (__tmp2_22)))) lor (((lnot (__tmp1_22))) land (__tmp2_22)),((__tmp1_23) land ((lnot (__tmp2_23)))) lor (((lnot (__tmp1_23))) land (__tmp2_23)),((__tmp1_24) land ((lnot (__tmp2_24)))) lor (((lnot (__tmp1_24))) land (__tmp2_24)),((__tmp1_25) land ((lnot (__tmp2_25)))) lor (((lnot (__tmp1_25))) land (__tmp2_25)),((__tmp1_26) land ((lnot (__tmp2_26)))) lor (((lnot (__tmp1_26))) land (__tmp2_26)),((__tmp1_27) land ((lnot (__tmp2_27)))) lor (((lnot (__tmp1_27))) land (__tmp2_27)),((__tmp1_28) land ((lnot (__tmp2_28)))) lor (((lnot (__tmp1_28))) land (__tmp2_28)),((__tmp1_29) land ((lnot (__tmp2_29)))) lor (((lnot (__tmp1_29))) land (__tmp2_29)),((__tmp1_30) land ((lnot (__tmp2_30)))) lor (((lnot (__tmp1_30))) land (__tmp2_30)),((__tmp1_31) land ((lnot (__tmp2_31)))) lor (((lnot (__tmp1_31))) land (__tmp2_31)),((__tmp1_32) land ((lnot (__tmp2_32)))) lor (((lnot (__tmp1_32))) land (__tmp2_32)),((__tmp1_33) land ((lnot (__tmp2_33)))) lor (((lnot (__tmp1_33))) land (__tmp2_33)),((__tmp1_34) land ((lnot (__tmp2_34)))) lor (((lnot (__tmp1_34))) land (__tmp2_34)),((__tmp1_35) land ((lnot (__tmp2_35)))) lor (((lnot (__tmp1_35))) land (__tmp2_35)),((__tmp1_36) land ((lnot (__tmp2_36)))) lor (((lnot (__tmp1_36))) land (__tmp2_36)),((__tmp1_37) land ((lnot (__tmp2_37)))) lor (((lnot (__tmp1_37))) land (__tmp2_37)),((__tmp1_38) land ((lnot (__tmp2_38)))) lor (((lnot (__tmp1_38))) land (__tmp2_38)),((__tmp1_39) land ((lnot (__tmp2_39)))) lor (((lnot (__tmp1_39))) land (__tmp2_39)),((__tmp1_40) land ((lnot (__tmp2_40)))) lor (((lnot (__tmp1_40))) land (__tmp2_40)),((__tmp1_41) land ((lnot (__tmp2_41)))) lor (((lnot (__tmp1_41))) land (__tmp2_41)),((__tmp1_42) land ((lnot (__tmp2_42)))) lor (((lnot (__tmp1_42))) land (__tmp2_42)),((__tmp1_43) land ((lnot (__tmp2_43)))) lor (((lnot (__tmp1_43))) land (__tmp2_43)),((__tmp1_44) land ((lnot (__tmp2_44)))) lor (((lnot (__tmp1_44))) land (__tmp2_44)),((__tmp1_45) land ((lnot (__tmp2_45)))) lor (((lnot (__tmp1_45))) land (__tmp2_45)),((__tmp1_46) land ((lnot (__tmp2_46)))) lor (((lnot (__tmp1_46))) land (__tmp2_46)),((__tmp1_47) land ((lnot (__tmp2_47)))) lor (((lnot (__tmp1_47))) land (__tmp2_47)),((__tmp1_48) land ((lnot (__tmp2_48)))) lor (((lnot (__tmp1_48))) land (__tmp2_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp3_1,__tmp3_2,__tmp3_3,__tmp3_4,__tmp3_5,__tmp3_6,__tmp3_7,__tmp3_8,__tmp3_9,__tmp3_10,__tmp3_11,__tmp3_12,__tmp3_13,__tmp3_14,__tmp3_15,__tmp3_16,__tmp3_17,__tmp3_18,__tmp3_19,__tmp3_20,__tmp3_21,__tmp3_22,__tmp3_23,__tmp3_24,__tmp3_25,__tmp3_26,__tmp3_27,__tmp3_28,__tmp3_29,__tmp3_30,__tmp3_31,__tmp3_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp4_1,__tmp4_2,__tmp4_3,__tmp4_4,__tmp4_5,__tmp4_6,__tmp4_7,__tmp4_8,__tmp4_9,__tmp4_10,__tmp4_11,__tmp4_12,__tmp4_13,__tmp4_14,__tmp4_15,__tmp4_16,__tmp4_17,__tmp4_18,__tmp4_19,__tmp4_20,__tmp4_21,__tmp4_22,__tmp4_23,__tmp4_24,__tmp4_25,__tmp4_26,__tmp4_27,__tmp4_28,__tmp4_29,__tmp4_30,__tmp4_31,__tmp4_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp3_1) land ((lnot (__tmp4_1)))) lor (((lnot (__tmp3_1))) land (__tmp4_1)),((__tmp3_2) land ((lnot (__tmp4_2)))) lor (((lnot (__tmp3_2))) land (__tmp4_2)),((__tmp3_3) land ((lnot (__tmp4_3)))) lor (((lnot (__tmp3_3))) land (__tmp4_3)),((__tmp3_4) land ((lnot (__tmp4_4)))) lor (((lnot (__tmp3_4))) land (__tmp4_4)),((__tmp3_5) land ((lnot (__tmp4_5)))) lor (((lnot (__tmp3_5))) land (__tmp4_5)),((__tmp3_6) land ((lnot (__tmp4_6)))) lor (((lnot (__tmp3_6))) land (__tmp4_6)),((__tmp3_7) land ((lnot (__tmp4_7)))) lor (((lnot (__tmp3_7))) land (__tmp4_7)),((__tmp3_8) land ((lnot (__tmp4_8)))) lor (((lnot (__tmp3_8))) land (__tmp4_8)),((__tmp3_9) land ((lnot (__tmp4_9)))) lor (((lnot (__tmp3_9))) land (__tmp4_9)),((__tmp3_10) land ((lnot (__tmp4_10)))) lor (((lnot (__tmp3_10))) land (__tmp4_10)),((__tmp3_11) land ((lnot (__tmp4_11)))) lor (((lnot (__tmp3_11))) land (__tmp4_11)),((__tmp3_12) land ((lnot (__tmp4_12)))) lor (((lnot (__tmp3_12))) land (__tmp4_12)),((__tmp3_13) land ((lnot (__tmp4_13)))) lor (((lnot (__tmp3_13))) land (__tmp4_13)),((__tmp3_14) land ((lnot (__tmp4_14)))) lor (((lnot (__tmp3_14))) land (__tmp4_14)),((__tmp3_15) land ((lnot (__tmp4_15)))) lor (((lnot (__tmp3_15))) land (__tmp4_15)),((__tmp3_16) land ((lnot (__tmp4_16)))) lor (((lnot (__tmp3_16))) land (__tmp4_16)),((__tmp3_17) land ((lnot (__tmp4_17)))) lor (((lnot (__tmp3_17))) land (__tmp4_17)),((__tmp3_18) land ((lnot (__tmp4_18)))) lor (((lnot (__tmp3_18))) land (__tmp4_18)),((__tmp3_19) land ((lnot (__tmp4_19)))) lor (((lnot (__tmp3_19))) land (__tmp4_19)),((__tmp3_20) land ((lnot (__tmp4_20)))) lor (((lnot (__tmp3_20))) land (__tmp4_20)),((__tmp3_21) land ((lnot (__tmp4_21)))) lor (((lnot (__tmp3_21))) land (__tmp4_21)),((__tmp3_22) land ((lnot (__tmp4_22)))) lor (((lnot (__tmp3_22))) land (__tmp4_22)),((__tmp3_23) land ((lnot (__tmp4_23)))) lor (((lnot (__tmp3_23))) land (__tmp4_23)),((__tmp3_24) land ((lnot (__tmp4_24)))) lor (((lnot (__tmp3_24))) land (__tmp4_24)),((__tmp3_25) land ((lnot (__tmp4_25)))) lor (((lnot (__tmp3_25))) land (__tmp4_25)),((__tmp3_26) land ((lnot (__tmp4_26)))) lor (((lnot (__tmp3_26))) land (__tmp4_26)),((__tmp3_27) land ((lnot (__tmp4_27)))) lor (((lnot (__tmp3_27))) land (__tmp4_27)),((__tmp3_28) land ((lnot (__tmp4_28)))) lor (((lnot (__tmp3_28))) land (__tmp4_28)),((__tmp3_29) land ((lnot (__tmp4_29)))) lor (((lnot (__tmp3_29))) land (__tmp4_29)),((__tmp3_30) land ((lnot (__tmp4_30)))) lor (((lnot (__tmp3_30))) land (__tmp4_30)),((__tmp3_31) land ((lnot (__tmp4_31)))) lor (((lnot (__tmp3_31))) land (__tmp4_31)),((__tmp3_32) land ((lnot (__tmp4_32)))) lor (((lnot (__tmp3_32))) land (__tmp4_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single2_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp5_1,__tmp5_2,__tmp5_3,__tmp5_4,__tmp5_5,__tmp5_6,__tmp5_7,__tmp5_8,__tmp5_9,__tmp5_10,__tmp5_11,__tmp5_12,__tmp5_13,__tmp5_14,__tmp5_15,__tmp5_16,__tmp5_17,__tmp5_18,__tmp5_19,__tmp5_20,__tmp5_21,__tmp5_22,__tmp5_23,__tmp5_24,__tmp5_25,__tmp5_26,__tmp5_27,__tmp5_28,__tmp5_29,__tmp5_30,__tmp5_31,__tmp5_32,__tmp5_33,__tmp5_34,__tmp5_35,__tmp5_36,__tmp5_37,__tmp5_38,__tmp5_39,__tmp5_40,__tmp5_41,__tmp5_42,__tmp5_43,__tmp5_44,__tmp5_45,__tmp5_46,__tmp5_47,__tmp5_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp6_1,__tmp6_2,__tmp6_3,__tmp6_4,__tmp6_5,__tmp6_6,__tmp6_7,__tmp6_8,__tmp6_9,__tmp6_10,__tmp6_11,__tmp6_12,__tmp6_13,__tmp6_14,__tmp6_15,__tmp6_16,__tmp6_17,__tmp6_18,__tmp6_19,__tmp6_20,__tmp6_21,__tmp6_22,__tmp6_23,__tmp6_24,__tmp6_25,__tmp6_26,__tmp6_27,__tmp6_28,__tmp6_29,__tmp6_30,__tmp6_31,__tmp6_32,__tmp6_33,__tmp6_34,__tmp6_35,__tmp6_36,__tmp6_37,__tmp6_38,__tmp6_39,__tmp6_40,__tmp6_41,__tmp6_42,__tmp6_43,__tmp6_44,__tmp6_45,__tmp6_46,__tmp6_47,__tmp6_48) = roundkey2_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp5_1) land ((lnot (__tmp6_1)))) lor (((lnot (__tmp5_1))) land (__tmp6_1)),((__tmp5_2) land ((lnot (__tmp6_2)))) lor (((lnot (__tmp5_2))) land (__tmp6_2)),((__tmp5_3) land ((lnot (__tmp6_3)))) lor (((lnot (__tmp5_3))) land (__tmp6_3)),((__tmp5_4) land ((lnot (__tmp6_4)))) lor (((lnot (__tmp5_4))) land (__tmp6_4)),((__tmp5_5) land ((lnot (__tmp6_5)))) lor (((lnot (__tmp5_5))) land (__tmp6_5)),((__tmp5_6) land ((lnot (__tmp6_6)))) lor (((lnot (__tmp5_6))) land (__tmp6_6)),((__tmp5_7) land ((lnot (__tmp6_7)))) lor (((lnot (__tmp5_7))) land (__tmp6_7)),((__tmp5_8) land ((lnot (__tmp6_8)))) lor (((lnot (__tmp5_8))) land (__tmp6_8)),((__tmp5_9) land ((lnot (__tmp6_9)))) lor (((lnot (__tmp5_9))) land (__tmp6_9)),((__tmp5_10) land ((lnot (__tmp6_10)))) lor (((lnot (__tmp5_10))) land (__tmp6_10)),((__tmp5_11) land ((lnot (__tmp6_11)))) lor (((lnot (__tmp5_11))) land (__tmp6_11)),((__tmp5_12) land ((lnot (__tmp6_12)))) lor (((lnot (__tmp5_12))) land (__tmp6_12)),((__tmp5_13) land ((lnot (__tmp6_13)))) lor (((lnot (__tmp5_13))) land (__tmp6_13)),((__tmp5_14) land ((lnot (__tmp6_14)))) lor (((lnot (__tmp5_14))) land (__tmp6_14)),((__tmp5_15) land ((lnot (__tmp6_15)))) lor (((lnot (__tmp5_15))) land (__tmp6_15)),((__tmp5_16) land ((lnot (__tmp6_16)))) lor (((lnot (__tmp5_16))) land (__tmp6_16)),((__tmp5_17) land ((lnot (__tmp6_17)))) lor (((lnot (__tmp5_17))) land (__tmp6_17)),((__tmp5_18) land ((lnot (__tmp6_18)))) lor (((lnot (__tmp5_18))) land (__tmp6_18)),((__tmp5_19) land ((lnot (__tmp6_19)))) lor (((lnot (__tmp5_19))) land (__tmp6_19)),((__tmp5_20) land ((lnot (__tmp6_20)))) lor (((lnot (__tmp5_20))) land (__tmp6_20)),((__tmp5_21) land ((lnot (__tmp6_21)))) lor (((lnot (__tmp5_21))) land (__tmp6_21)),((__tmp5_22) land ((lnot (__tmp6_22)))) lor (((lnot (__tmp5_22))) land (__tmp6_22)),((__tmp5_23) land ((lnot (__tmp6_23)))) lor (((lnot (__tmp5_23))) land (__tmp6_23)),((__tmp5_24) land ((lnot (__tmp6_24)))) lor (((lnot (__tmp5_24))) land (__tmp6_24)),((__tmp5_25) land ((lnot (__tmp6_25)))) lor (((lnot (__tmp5_25))) land (__tmp6_25)),((__tmp5_26) land ((lnot (__tmp6_26)))) lor (((lnot (__tmp5_26))) land (__tmp6_26)),((__tmp5_27) land ((lnot (__tmp6_27)))) lor (((lnot (__tmp5_27))) land (__tmp6_27)),((__tmp5_28) land ((lnot (__tmp6_28)))) lor (((lnot (__tmp5_28))) land (__tmp6_28)),((__tmp5_29) land ((lnot (__tmp6_29)))) lor (((lnot (__tmp5_29))) land (__tmp6_29)),((__tmp5_30) land ((lnot (__tmp6_30)))) lor (((lnot (__tmp5_30))) land (__tmp6_30)),((__tmp5_31) land ((lnot (__tmp6_31)))) lor (((lnot (__tmp5_31))) land (__tmp6_31)),((__tmp5_32) land ((lnot (__tmp6_32)))) lor (((lnot (__tmp5_32))) land (__tmp6_32)),((__tmp5_33) land ((lnot (__tmp6_33)))) lor (((lnot (__tmp5_33))) land (__tmp6_33)),((__tmp5_34) land ((lnot (__tmp6_34)))) lor (((lnot (__tmp5_34))) land (__tmp6_34)),((__tmp5_35) land ((lnot (__tmp6_35)))) lor (((lnot (__tmp5_35))) land (__tmp6_35)),((__tmp5_36) land ((lnot (__tmp6_36)))) lor (((lnot (__tmp5_36))) land (__tmp6_36)),((__tmp5_37) land ((lnot (__tmp6_37)))) lor (((lnot (__tmp5_37))) land (__tmp6_37)),((__tmp5_38) land ((lnot (__tmp6_38)))) lor (((lnot (__tmp5_38))) land (__tmp6_38)),((__tmp5_39) land ((lnot (__tmp6_39)))) lor (((lnot (__tmp5_39))) land (__tmp6_39)),((__tmp5_40) land ((lnot (__tmp6_40)))) lor (((lnot (__tmp5_40))) land (__tmp6_40)),((__tmp5_41) land ((lnot (__tmp6_41)))) lor (((lnot (__tmp5_41))) land (__tmp6_41)),((__tmp5_42) land ((lnot (__tmp6_42)))) lor (((lnot (__tmp5_42))) land (__tmp6_42)),((__tmp5_43) land ((lnot (__tmp6_43)))) lor (((lnot (__tmp5_43))) land (__tmp6_43)),((__tmp5_44) land ((lnot (__tmp6_44)))) lor (((lnot (__tmp5_44))) land (__tmp6_44)),((__tmp5_45) land ((lnot (__tmp6_45)))) lor (((lnot (__tmp5_45))) land (__tmp6_45)),((__tmp5_46) land ((lnot (__tmp6_46)))) lor (((lnot (__tmp5_46))) land (__tmp6_46)),((__tmp5_47) land ((lnot (__tmp6_47)))) lor (((lnot (__tmp5_47))) land (__tmp6_47)),((__tmp5_48) land ((lnot (__tmp6_48)))) lor (((lnot (__tmp5_48))) land (__tmp6_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp7_1,__tmp7_2,__tmp7_3,__tmp7_4,__tmp7_5,__tmp7_6,__tmp7_7,__tmp7_8,__tmp7_9,__tmp7_10,__tmp7_11,__tmp7_12,__tmp7_13,__tmp7_14,__tmp7_15,__tmp7_16,__tmp7_17,__tmp7_18,__tmp7_19,__tmp7_20,__tmp7_21,__tmp7_22,__tmp7_23,__tmp7_24,__tmp7_25,__tmp7_26,__tmp7_27,__tmp7_28,__tmp7_29,__tmp7_30,__tmp7_31,__tmp7_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp8_1,__tmp8_2,__tmp8_3,__tmp8_4,__tmp8_5,__tmp8_6,__tmp8_7,__tmp8_8,__tmp8_9,__tmp8_10,__tmp8_11,__tmp8_12,__tmp8_13,__tmp8_14,__tmp8_15,__tmp8_16,__tmp8_17,__tmp8_18,__tmp8_19,__tmp8_20,__tmp8_21,__tmp8_22,__tmp8_23,__tmp8_24,__tmp8_25,__tmp8_26,__tmp8_27,__tmp8_28,__tmp8_29,__tmp8_30,__tmp8_31,__tmp8_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp7_1) land ((lnot (__tmp8_1)))) lor (((lnot (__tmp7_1))) land (__tmp8_1)),((__tmp7_2) land ((lnot (__tmp8_2)))) lor (((lnot (__tmp7_2))) land (__tmp8_2)),((__tmp7_3) land ((lnot (__tmp8_3)))) lor (((lnot (__tmp7_3))) land (__tmp8_3)),((__tmp7_4) land ((lnot (__tmp8_4)))) lor (((lnot (__tmp7_4))) land (__tmp8_4)),((__tmp7_5) land ((lnot (__tmp8_5)))) lor (((lnot (__tmp7_5))) land (__tmp8_5)),((__tmp7_6) land ((lnot (__tmp8_6)))) lor (((lnot (__tmp7_6))) land (__tmp8_6)),((__tmp7_7) land ((lnot (__tmp8_7)))) lor (((lnot (__tmp7_7))) land (__tmp8_7)),((__tmp7_8) land ((lnot (__tmp8_8)))) lor (((lnot (__tmp7_8))) land (__tmp8_8)),((__tmp7_9) land ((lnot (__tmp8_9)))) lor (((lnot (__tmp7_9))) land (__tmp8_9)),((__tmp7_10) land ((lnot (__tmp8_10)))) lor (((lnot (__tmp7_10))) land (__tmp8_10)),((__tmp7_11) land ((lnot (__tmp8_11)))) lor (((lnot (__tmp7_11))) land (__tmp8_11)),((__tmp7_12) land ((lnot (__tmp8_12)))) lor (((lnot (__tmp7_12))) land (__tmp8_12)),((__tmp7_13) land ((lnot (__tmp8_13)))) lor (((lnot (__tmp7_13))) land (__tmp8_13)),((__tmp7_14) land ((lnot (__tmp8_14)))) lor (((lnot (__tmp7_14))) land (__tmp8_14)),((__tmp7_15) land ((lnot (__tmp8_15)))) lor (((lnot (__tmp7_15))) land (__tmp8_15)),((__tmp7_16) land ((lnot (__tmp8_16)))) lor (((lnot (__tmp7_16))) land (__tmp8_16)),((__tmp7_17) land ((lnot (__tmp8_17)))) lor (((lnot (__tmp7_17))) land (__tmp8_17)),((__tmp7_18) land ((lnot (__tmp8_18)))) lor (((lnot (__tmp7_18))) land (__tmp8_18)),((__tmp7_19) land ((lnot (__tmp8_19)))) lor (((lnot (__tmp7_19))) land (__tmp8_19)),((__tmp7_20) land ((lnot (__tmp8_20)))) lor (((lnot (__tmp7_20))) land (__tmp8_20)),((__tmp7_21) land ((lnot (__tmp8_21)))) lor (((lnot (__tmp7_21))) land (__tmp8_21)),((__tmp7_22) land ((lnot (__tmp8_22)))) lor (((lnot (__tmp7_22))) land (__tmp8_22)),((__tmp7_23) land ((lnot (__tmp8_23)))) lor (((lnot (__tmp7_23))) land (__tmp8_23)),((__tmp7_24) land ((lnot (__tmp8_24)))) lor (((lnot (__tmp7_24))) land (__tmp8_24)),((__tmp7_25) land ((lnot (__tmp8_25)))) lor (((lnot (__tmp7_25))) land (__tmp8_25)),((__tmp7_26) land ((lnot (__tmp8_26)))) lor (((lnot (__tmp7_26))) land (__tmp8_26)),((__tmp7_27) land ((lnot (__tmp8_27)))) lor (((lnot (__tmp7_27))) land (__tmp8_27)),((__tmp7_28) land ((lnot (__tmp8_28)))) lor (((lnot (__tmp7_28))) land (__tmp8_28)),((__tmp7_29) land ((lnot (__tmp8_29)))) lor (((lnot (__tmp7_29))) land (__tmp8_29)),((__tmp7_30) land ((lnot (__tmp8_30)))) lor (((lnot (__tmp7_30))) land (__tmp8_30)),((__tmp7_31) land ((lnot (__tmp8_31)))) lor (((lnot (__tmp7_31))) land (__tmp8_31)),((__tmp7_32) land ((lnot (__tmp8_32)))) lor (((lnot (__tmp7_32))) land (__tmp8_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single3_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp9_1,__tmp9_2,__tmp9_3,__tmp9_4,__tmp9_5,__tmp9_6,__tmp9_7,__tmp9_8,__tmp9_9,__tmp9_10,__tmp9_11,__tmp9_12,__tmp9_13,__tmp9_14,__tmp9_15,__tmp9_16,__tmp9_17,__tmp9_18,__tmp9_19,__tmp9_20,__tmp9_21,__tmp9_22,__tmp9_23,__tmp9_24,__tmp9_25,__tmp9_26,__tmp9_27,__tmp9_28,__tmp9_29,__tmp9_30,__tmp9_31,__tmp9_32,__tmp9_33,__tmp9_34,__tmp9_35,__tmp9_36,__tmp9_37,__tmp9_38,__tmp9_39,__tmp9_40,__tmp9_41,__tmp9_42,__tmp9_43,__tmp9_44,__tmp9_45,__tmp9_46,__tmp9_47,__tmp9_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp10_1,__tmp10_2,__tmp10_3,__tmp10_4,__tmp10_5,__tmp10_6,__tmp10_7,__tmp10_8,__tmp10_9,__tmp10_10,__tmp10_11,__tmp10_12,__tmp10_13,__tmp10_14,__tmp10_15,__tmp10_16,__tmp10_17,__tmp10_18,__tmp10_19,__tmp10_20,__tmp10_21,__tmp10_22,__tmp10_23,__tmp10_24,__tmp10_25,__tmp10_26,__tmp10_27,__tmp10_28,__tmp10_29,__tmp10_30,__tmp10_31,__tmp10_32,__tmp10_33,__tmp10_34,__tmp10_35,__tmp10_36,__tmp10_37,__tmp10_38,__tmp10_39,__tmp10_40,__tmp10_41,__tmp10_42,__tmp10_43,__tmp10_44,__tmp10_45,__tmp10_46,__tmp10_47,__tmp10_48) = roundkey3_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp9_1) land ((lnot (__tmp10_1)))) lor (((lnot (__tmp9_1))) land (__tmp10_1)),((__tmp9_2) land ((lnot (__tmp10_2)))) lor (((lnot (__tmp9_2))) land (__tmp10_2)),((__tmp9_3) land ((lnot (__tmp10_3)))) lor (((lnot (__tmp9_3))) land (__tmp10_3)),((__tmp9_4) land ((lnot (__tmp10_4)))) lor (((lnot (__tmp9_4))) land (__tmp10_4)),((__tmp9_5) land ((lnot (__tmp10_5)))) lor (((lnot (__tmp9_5))) land (__tmp10_5)),((__tmp9_6) land ((lnot (__tmp10_6)))) lor (((lnot (__tmp9_6))) land (__tmp10_6)),((__tmp9_7) land ((lnot (__tmp10_7)))) lor (((lnot (__tmp9_7))) land (__tmp10_7)),((__tmp9_8) land ((lnot (__tmp10_8)))) lor (((lnot (__tmp9_8))) land (__tmp10_8)),((__tmp9_9) land ((lnot (__tmp10_9)))) lor (((lnot (__tmp9_9))) land (__tmp10_9)),((__tmp9_10) land ((lnot (__tmp10_10)))) lor (((lnot (__tmp9_10))) land (__tmp10_10)),((__tmp9_11) land ((lnot (__tmp10_11)))) lor (((lnot (__tmp9_11))) land (__tmp10_11)),((__tmp9_12) land ((lnot (__tmp10_12)))) lor (((lnot (__tmp9_12))) land (__tmp10_12)),((__tmp9_13) land ((lnot (__tmp10_13)))) lor (((lnot (__tmp9_13))) land (__tmp10_13)),((__tmp9_14) land ((lnot (__tmp10_14)))) lor (((lnot (__tmp9_14))) land (__tmp10_14)),((__tmp9_15) land ((lnot (__tmp10_15)))) lor (((lnot (__tmp9_15))) land (__tmp10_15)),((__tmp9_16) land ((lnot (__tmp10_16)))) lor (((lnot (__tmp9_16))) land (__tmp10_16)),((__tmp9_17) land ((lnot (__tmp10_17)))) lor (((lnot (__tmp9_17))) land (__tmp10_17)),((__tmp9_18) land ((lnot (__tmp10_18)))) lor (((lnot (__tmp9_18))) land (__tmp10_18)),((__tmp9_19) land ((lnot (__tmp10_19)))) lor (((lnot (__tmp9_19))) land (__tmp10_19)),((__tmp9_20) land ((lnot (__tmp10_20)))) lor (((lnot (__tmp9_20))) land (__tmp10_20)),((__tmp9_21) land ((lnot (__tmp10_21)))) lor (((lnot (__tmp9_21))) land (__tmp10_21)),((__tmp9_22) land ((lnot (__tmp10_22)))) lor (((lnot (__tmp9_22))) land (__tmp10_22)),((__tmp9_23) land ((lnot (__tmp10_23)))) lor (((lnot (__tmp9_23))) land (__tmp10_23)),((__tmp9_24) land ((lnot (__tmp10_24)))) lor (((lnot (__tmp9_24))) land (__tmp10_24)),((__tmp9_25) land ((lnot (__tmp10_25)))) lor (((lnot (__tmp9_25))) land (__tmp10_25)),((__tmp9_26) land ((lnot (__tmp10_26)))) lor (((lnot (__tmp9_26))) land (__tmp10_26)),((__tmp9_27) land ((lnot (__tmp10_27)))) lor (((lnot (__tmp9_27))) land (__tmp10_27)),((__tmp9_28) land ((lnot (__tmp10_28)))) lor (((lnot (__tmp9_28))) land (__tmp10_28)),((__tmp9_29) land ((lnot (__tmp10_29)))) lor (((lnot (__tmp9_29))) land (__tmp10_29)),((__tmp9_30) land ((lnot (__tmp10_30)))) lor (((lnot (__tmp9_30))) land (__tmp10_30)),((__tmp9_31) land ((lnot (__tmp10_31)))) lor (((lnot (__tmp9_31))) land (__tmp10_31)),((__tmp9_32) land ((lnot (__tmp10_32)))) lor (((lnot (__tmp9_32))) land (__tmp10_32)),((__tmp9_33) land ((lnot (__tmp10_33)))) lor (((lnot (__tmp9_33))) land (__tmp10_33)),((__tmp9_34) land ((lnot (__tmp10_34)))) lor (((lnot (__tmp9_34))) land (__tmp10_34)),((__tmp9_35) land ((lnot (__tmp10_35)))) lor (((lnot (__tmp9_35))) land (__tmp10_35)),((__tmp9_36) land ((lnot (__tmp10_36)))) lor (((lnot (__tmp9_36))) land (__tmp10_36)),((__tmp9_37) land ((lnot (__tmp10_37)))) lor (((lnot (__tmp9_37))) land (__tmp10_37)),((__tmp9_38) land ((lnot (__tmp10_38)))) lor (((lnot (__tmp9_38))) land (__tmp10_38)),((__tmp9_39) land ((lnot (__tmp10_39)))) lor (((lnot (__tmp9_39))) land (__tmp10_39)),((__tmp9_40) land ((lnot (__tmp10_40)))) lor (((lnot (__tmp9_40))) land (__tmp10_40)),((__tmp9_41) land ((lnot (__tmp10_41)))) lor (((lnot (__tmp9_41))) land (__tmp10_41)),((__tmp9_42) land ((lnot (__tmp10_42)))) lor (((lnot (__tmp9_42))) land (__tmp10_42)),((__tmp9_43) land ((lnot (__tmp10_43)))) lor (((lnot (__tmp9_43))) land (__tmp10_43)),((__tmp9_44) land ((lnot (__tmp10_44)))) lor (((lnot (__tmp9_44))) land (__tmp10_44)),((__tmp9_45) land ((lnot (__tmp10_45)))) lor (((lnot (__tmp9_45))) land (__tmp10_45)),((__tmp9_46) land ((lnot (__tmp10_46)))) lor (((lnot (__tmp9_46))) land (__tmp10_46)),((__tmp9_47) land ((lnot (__tmp10_47)))) lor (((lnot (__tmp9_47))) land (__tmp10_47)),((__tmp9_48) land ((lnot (__tmp10_48)))) lor (((lnot (__tmp9_48))) land (__tmp10_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp11_1,__tmp11_2,__tmp11_3,__tmp11_4,__tmp11_5,__tmp11_6,__tmp11_7,__tmp11_8,__tmp11_9,__tmp11_10,__tmp11_11,__tmp11_12,__tmp11_13,__tmp11_14,__tmp11_15,__tmp11_16,__tmp11_17,__tmp11_18,__tmp11_19,__tmp11_20,__tmp11_21,__tmp11_22,__tmp11_23,__tmp11_24,__tmp11_25,__tmp11_26,__tmp11_27,__tmp11_28,__tmp11_29,__tmp11_30,__tmp11_31,__tmp11_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp12_1,__tmp12_2,__tmp12_3,__tmp12_4,__tmp12_5,__tmp12_6,__tmp12_7,__tmp12_8,__tmp12_9,__tmp12_10,__tmp12_11,__tmp12_12,__tmp12_13,__tmp12_14,__tmp12_15,__tmp12_16,__tmp12_17,__tmp12_18,__tmp12_19,__tmp12_20,__tmp12_21,__tmp12_22,__tmp12_23,__tmp12_24,__tmp12_25,__tmp12_26,__tmp12_27,__tmp12_28,__tmp12_29,__tmp12_30,__tmp12_31,__tmp12_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp11_1) land ((lnot (__tmp12_1)))) lor (((lnot (__tmp11_1))) land (__tmp12_1)),((__tmp11_2) land ((lnot (__tmp12_2)))) lor (((lnot (__tmp11_2))) land (__tmp12_2)),((__tmp11_3) land ((lnot (__tmp12_3)))) lor (((lnot (__tmp11_3))) land (__tmp12_3)),((__tmp11_4) land ((lnot (__tmp12_4)))) lor (((lnot (__tmp11_4))) land (__tmp12_4)),((__tmp11_5) land ((lnot (__tmp12_5)))) lor (((lnot (__tmp11_5))) land (__tmp12_5)),((__tmp11_6) land ((lnot (__tmp12_6)))) lor (((lnot (__tmp11_6))) land (__tmp12_6)),((__tmp11_7) land ((lnot (__tmp12_7)))) lor (((lnot (__tmp11_7))) land (__tmp12_7)),((__tmp11_8) land ((lnot (__tmp12_8)))) lor (((lnot (__tmp11_8))) land (__tmp12_8)),((__tmp11_9) land ((lnot (__tmp12_9)))) lor (((lnot (__tmp11_9))) land (__tmp12_9)),((__tmp11_10) land ((lnot (__tmp12_10)))) lor (((lnot (__tmp11_10))) land (__tmp12_10)),((__tmp11_11) land ((lnot (__tmp12_11)))) lor (((lnot (__tmp11_11))) land (__tmp12_11)),((__tmp11_12) land ((lnot (__tmp12_12)))) lor (((lnot (__tmp11_12))) land (__tmp12_12)),((__tmp11_13) land ((lnot (__tmp12_13)))) lor (((lnot (__tmp11_13))) land (__tmp12_13)),((__tmp11_14) land ((lnot (__tmp12_14)))) lor (((lnot (__tmp11_14))) land (__tmp12_14)),((__tmp11_15) land ((lnot (__tmp12_15)))) lor (((lnot (__tmp11_15))) land (__tmp12_15)),((__tmp11_16) land ((lnot (__tmp12_16)))) lor (((lnot (__tmp11_16))) land (__tmp12_16)),((__tmp11_17) land ((lnot (__tmp12_17)))) lor (((lnot (__tmp11_17))) land (__tmp12_17)),((__tmp11_18) land ((lnot (__tmp12_18)))) lor (((lnot (__tmp11_18))) land (__tmp12_18)),((__tmp11_19) land ((lnot (__tmp12_19)))) lor (((lnot (__tmp11_19))) land (__tmp12_19)),((__tmp11_20) land ((lnot (__tmp12_20)))) lor (((lnot (__tmp11_20))) land (__tmp12_20)),((__tmp11_21) land ((lnot (__tmp12_21)))) lor (((lnot (__tmp11_21))) land (__tmp12_21)),((__tmp11_22) land ((lnot (__tmp12_22)))) lor (((lnot (__tmp11_22))) land (__tmp12_22)),((__tmp11_23) land ((lnot (__tmp12_23)))) lor (((lnot (__tmp11_23))) land (__tmp12_23)),((__tmp11_24) land ((lnot (__tmp12_24)))) lor (((lnot (__tmp11_24))) land (__tmp12_24)),((__tmp11_25) land ((lnot (__tmp12_25)))) lor (((lnot (__tmp11_25))) land (__tmp12_25)),((__tmp11_26) land ((lnot (__tmp12_26)))) lor (((lnot (__tmp11_26))) land (__tmp12_26)),((__tmp11_27) land ((lnot (__tmp12_27)))) lor (((lnot (__tmp11_27))) land (__tmp12_27)),((__tmp11_28) land ((lnot (__tmp12_28)))) lor (((lnot (__tmp11_28))) land (__tmp12_28)),((__tmp11_29) land ((lnot (__tmp12_29)))) lor (((lnot (__tmp11_29))) land (__tmp12_29)),((__tmp11_30) land ((lnot (__tmp12_30)))) lor (((lnot (__tmp11_30))) land (__tmp12_30)),((__tmp11_31) land ((lnot (__tmp12_31)))) lor (((lnot (__tmp11_31))) land (__tmp12_31)),((__tmp11_32) land ((lnot (__tmp12_32)))) lor (((lnot (__tmp11_32))) land (__tmp12_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single4_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp13_1,__tmp13_2,__tmp13_3,__tmp13_4,__tmp13_5,__tmp13_6,__tmp13_7,__tmp13_8,__tmp13_9,__tmp13_10,__tmp13_11,__tmp13_12,__tmp13_13,__tmp13_14,__tmp13_15,__tmp13_16,__tmp13_17,__tmp13_18,__tmp13_19,__tmp13_20,__tmp13_21,__tmp13_22,__tmp13_23,__tmp13_24,__tmp13_25,__tmp13_26,__tmp13_27,__tmp13_28,__tmp13_29,__tmp13_30,__tmp13_31,__tmp13_32,__tmp13_33,__tmp13_34,__tmp13_35,__tmp13_36,__tmp13_37,__tmp13_38,__tmp13_39,__tmp13_40,__tmp13_41,__tmp13_42,__tmp13_43,__tmp13_44,__tmp13_45,__tmp13_46,__tmp13_47,__tmp13_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp14_1,__tmp14_2,__tmp14_3,__tmp14_4,__tmp14_5,__tmp14_6,__tmp14_7,__tmp14_8,__tmp14_9,__tmp14_10,__tmp14_11,__tmp14_12,__tmp14_13,__tmp14_14,__tmp14_15,__tmp14_16,__tmp14_17,__tmp14_18,__tmp14_19,__tmp14_20,__tmp14_21,__tmp14_22,__tmp14_23,__tmp14_24,__tmp14_25,__tmp14_26,__tmp14_27,__tmp14_28,__tmp14_29,__tmp14_30,__tmp14_31,__tmp14_32,__tmp14_33,__tmp14_34,__tmp14_35,__tmp14_36,__tmp14_37,__tmp14_38,__tmp14_39,__tmp14_40,__tmp14_41,__tmp14_42,__tmp14_43,__tmp14_44,__tmp14_45,__tmp14_46,__tmp14_47,__tmp14_48) = roundkey4_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp13_1) land ((lnot (__tmp14_1)))) lor (((lnot (__tmp13_1))) land (__tmp14_1)),((__tmp13_2) land ((lnot (__tmp14_2)))) lor (((lnot (__tmp13_2))) land (__tmp14_2)),((__tmp13_3) land ((lnot (__tmp14_3)))) lor (((lnot (__tmp13_3))) land (__tmp14_3)),((__tmp13_4) land ((lnot (__tmp14_4)))) lor (((lnot (__tmp13_4))) land (__tmp14_4)),((__tmp13_5) land ((lnot (__tmp14_5)))) lor (((lnot (__tmp13_5))) land (__tmp14_5)),((__tmp13_6) land ((lnot (__tmp14_6)))) lor (((lnot (__tmp13_6))) land (__tmp14_6)),((__tmp13_7) land ((lnot (__tmp14_7)))) lor (((lnot (__tmp13_7))) land (__tmp14_7)),((__tmp13_8) land ((lnot (__tmp14_8)))) lor (((lnot (__tmp13_8))) land (__tmp14_8)),((__tmp13_9) land ((lnot (__tmp14_9)))) lor (((lnot (__tmp13_9))) land (__tmp14_9)),((__tmp13_10) land ((lnot (__tmp14_10)))) lor (((lnot (__tmp13_10))) land (__tmp14_10)),((__tmp13_11) land ((lnot (__tmp14_11)))) lor (((lnot (__tmp13_11))) land (__tmp14_11)),((__tmp13_12) land ((lnot (__tmp14_12)))) lor (((lnot (__tmp13_12))) land (__tmp14_12)),((__tmp13_13) land ((lnot (__tmp14_13)))) lor (((lnot (__tmp13_13))) land (__tmp14_13)),((__tmp13_14) land ((lnot (__tmp14_14)))) lor (((lnot (__tmp13_14))) land (__tmp14_14)),((__tmp13_15) land ((lnot (__tmp14_15)))) lor (((lnot (__tmp13_15))) land (__tmp14_15)),((__tmp13_16) land ((lnot (__tmp14_16)))) lor (((lnot (__tmp13_16))) land (__tmp14_16)),((__tmp13_17) land ((lnot (__tmp14_17)))) lor (((lnot (__tmp13_17))) land (__tmp14_17)),((__tmp13_18) land ((lnot (__tmp14_18)))) lor (((lnot (__tmp13_18))) land (__tmp14_18)),((__tmp13_19) land ((lnot (__tmp14_19)))) lor (((lnot (__tmp13_19))) land (__tmp14_19)),((__tmp13_20) land ((lnot (__tmp14_20)))) lor (((lnot (__tmp13_20))) land (__tmp14_20)),((__tmp13_21) land ((lnot (__tmp14_21)))) lor (((lnot (__tmp13_21))) land (__tmp14_21)),((__tmp13_22) land ((lnot (__tmp14_22)))) lor (((lnot (__tmp13_22))) land (__tmp14_22)),((__tmp13_23) land ((lnot (__tmp14_23)))) lor (((lnot (__tmp13_23))) land (__tmp14_23)),((__tmp13_24) land ((lnot (__tmp14_24)))) lor (((lnot (__tmp13_24))) land (__tmp14_24)),((__tmp13_25) land ((lnot (__tmp14_25)))) lor (((lnot (__tmp13_25))) land (__tmp14_25)),((__tmp13_26) land ((lnot (__tmp14_26)))) lor (((lnot (__tmp13_26))) land (__tmp14_26)),((__tmp13_27) land ((lnot (__tmp14_27)))) lor (((lnot (__tmp13_27))) land (__tmp14_27)),((__tmp13_28) land ((lnot (__tmp14_28)))) lor (((lnot (__tmp13_28))) land (__tmp14_28)),((__tmp13_29) land ((lnot (__tmp14_29)))) lor (((lnot (__tmp13_29))) land (__tmp14_29)),((__tmp13_30) land ((lnot (__tmp14_30)))) lor (((lnot (__tmp13_30))) land (__tmp14_30)),((__tmp13_31) land ((lnot (__tmp14_31)))) lor (((lnot (__tmp13_31))) land (__tmp14_31)),((__tmp13_32) land ((lnot (__tmp14_32)))) lor (((lnot (__tmp13_32))) land (__tmp14_32)),((__tmp13_33) land ((lnot (__tmp14_33)))) lor (((lnot (__tmp13_33))) land (__tmp14_33)),((__tmp13_34) land ((lnot (__tmp14_34)))) lor (((lnot (__tmp13_34))) land (__tmp14_34)),((__tmp13_35) land ((lnot (__tmp14_35)))) lor (((lnot (__tmp13_35))) land (__tmp14_35)),((__tmp13_36) land ((lnot (__tmp14_36)))) lor (((lnot (__tmp13_36))) land (__tmp14_36)),((__tmp13_37) land ((lnot (__tmp14_37)))) lor (((lnot (__tmp13_37))) land (__tmp14_37)),((__tmp13_38) land ((lnot (__tmp14_38)))) lor (((lnot (__tmp13_38))) land (__tmp14_38)),((__tmp13_39) land ((lnot (__tmp14_39)))) lor (((lnot (__tmp13_39))) land (__tmp14_39)),((__tmp13_40) land ((lnot (__tmp14_40)))) lor (((lnot (__tmp13_40))) land (__tmp14_40)),((__tmp13_41) land ((lnot (__tmp14_41)))) lor (((lnot (__tmp13_41))) land (__tmp14_41)),((__tmp13_42) land ((lnot (__tmp14_42)))) lor (((lnot (__tmp13_42))) land (__tmp14_42)),((__tmp13_43) land ((lnot (__tmp14_43)))) lor (((lnot (__tmp13_43))) land (__tmp14_43)),((__tmp13_44) land ((lnot (__tmp14_44)))) lor (((lnot (__tmp13_44))) land (__tmp14_44)),((__tmp13_45) land ((lnot (__tmp14_45)))) lor (((lnot (__tmp13_45))) land (__tmp14_45)),((__tmp13_46) land ((lnot (__tmp14_46)))) lor (((lnot (__tmp13_46))) land (__tmp14_46)),((__tmp13_47) land ((lnot (__tmp14_47)))) lor (((lnot (__tmp13_47))) land (__tmp14_47)),((__tmp13_48) land ((lnot (__tmp14_48)))) lor (((lnot (__tmp13_48))) land (__tmp14_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp15_1,__tmp15_2,__tmp15_3,__tmp15_4,__tmp15_5,__tmp15_6,__tmp15_7,__tmp15_8,__tmp15_9,__tmp15_10,__tmp15_11,__tmp15_12,__tmp15_13,__tmp15_14,__tmp15_15,__tmp15_16,__tmp15_17,__tmp15_18,__tmp15_19,__tmp15_20,__tmp15_21,__tmp15_22,__tmp15_23,__tmp15_24,__tmp15_25,__tmp15_26,__tmp15_27,__tmp15_28,__tmp15_29,__tmp15_30,__tmp15_31,__tmp15_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp16_1,__tmp16_2,__tmp16_3,__tmp16_4,__tmp16_5,__tmp16_6,__tmp16_7,__tmp16_8,__tmp16_9,__tmp16_10,__tmp16_11,__tmp16_12,__tmp16_13,__tmp16_14,__tmp16_15,__tmp16_16,__tmp16_17,__tmp16_18,__tmp16_19,__tmp16_20,__tmp16_21,__tmp16_22,__tmp16_23,__tmp16_24,__tmp16_25,__tmp16_26,__tmp16_27,__tmp16_28,__tmp16_29,__tmp16_30,__tmp16_31,__tmp16_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp15_1) land ((lnot (__tmp16_1)))) lor (((lnot (__tmp15_1))) land (__tmp16_1)),((__tmp15_2) land ((lnot (__tmp16_2)))) lor (((lnot (__tmp15_2))) land (__tmp16_2)),((__tmp15_3) land ((lnot (__tmp16_3)))) lor (((lnot (__tmp15_3))) land (__tmp16_3)),((__tmp15_4) land ((lnot (__tmp16_4)))) lor (((lnot (__tmp15_4))) land (__tmp16_4)),((__tmp15_5) land ((lnot (__tmp16_5)))) lor (((lnot (__tmp15_5))) land (__tmp16_5)),((__tmp15_6) land ((lnot (__tmp16_6)))) lor (((lnot (__tmp15_6))) land (__tmp16_6)),((__tmp15_7) land ((lnot (__tmp16_7)))) lor (((lnot (__tmp15_7))) land (__tmp16_7)),((__tmp15_8) land ((lnot (__tmp16_8)))) lor (((lnot (__tmp15_8))) land (__tmp16_8)),((__tmp15_9) land ((lnot (__tmp16_9)))) lor (((lnot (__tmp15_9))) land (__tmp16_9)),((__tmp15_10) land ((lnot (__tmp16_10)))) lor (((lnot (__tmp15_10))) land (__tmp16_10)),((__tmp15_11) land ((lnot (__tmp16_11)))) lor (((lnot (__tmp15_11))) land (__tmp16_11)),((__tmp15_12) land ((lnot (__tmp16_12)))) lor (((lnot (__tmp15_12))) land (__tmp16_12)),((__tmp15_13) land ((lnot (__tmp16_13)))) lor (((lnot (__tmp15_13))) land (__tmp16_13)),((__tmp15_14) land ((lnot (__tmp16_14)))) lor (((lnot (__tmp15_14))) land (__tmp16_14)),((__tmp15_15) land ((lnot (__tmp16_15)))) lor (((lnot (__tmp15_15))) land (__tmp16_15)),((__tmp15_16) land ((lnot (__tmp16_16)))) lor (((lnot (__tmp15_16))) land (__tmp16_16)),((__tmp15_17) land ((lnot (__tmp16_17)))) lor (((lnot (__tmp15_17))) land (__tmp16_17)),((__tmp15_18) land ((lnot (__tmp16_18)))) lor (((lnot (__tmp15_18))) land (__tmp16_18)),((__tmp15_19) land ((lnot (__tmp16_19)))) lor (((lnot (__tmp15_19))) land (__tmp16_19)),((__tmp15_20) land ((lnot (__tmp16_20)))) lor (((lnot (__tmp15_20))) land (__tmp16_20)),((__tmp15_21) land ((lnot (__tmp16_21)))) lor (((lnot (__tmp15_21))) land (__tmp16_21)),((__tmp15_22) land ((lnot (__tmp16_22)))) lor (((lnot (__tmp15_22))) land (__tmp16_22)),((__tmp15_23) land ((lnot (__tmp16_23)))) lor (((lnot (__tmp15_23))) land (__tmp16_23)),((__tmp15_24) land ((lnot (__tmp16_24)))) lor (((lnot (__tmp15_24))) land (__tmp16_24)),((__tmp15_25) land ((lnot (__tmp16_25)))) lor (((lnot (__tmp15_25))) land (__tmp16_25)),((__tmp15_26) land ((lnot (__tmp16_26)))) lor (((lnot (__tmp15_26))) land (__tmp16_26)),((__tmp15_27) land ((lnot (__tmp16_27)))) lor (((lnot (__tmp15_27))) land (__tmp16_27)),((__tmp15_28) land ((lnot (__tmp16_28)))) lor (((lnot (__tmp15_28))) land (__tmp16_28)),((__tmp15_29) land ((lnot (__tmp16_29)))) lor (((lnot (__tmp15_29))) land (__tmp16_29)),((__tmp15_30) land ((lnot (__tmp16_30)))) lor (((lnot (__tmp15_30))) land (__tmp16_30)),((__tmp15_31) land ((lnot (__tmp16_31)))) lor (((lnot (__tmp15_31))) land (__tmp16_31)),((__tmp15_32) land ((lnot (__tmp16_32)))) lor (((lnot (__tmp15_32))) land (__tmp16_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single5_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp17_1,__tmp17_2,__tmp17_3,__tmp17_4,__tmp17_5,__tmp17_6,__tmp17_7,__tmp17_8,__tmp17_9,__tmp17_10,__tmp17_11,__tmp17_12,__tmp17_13,__tmp17_14,__tmp17_15,__tmp17_16,__tmp17_17,__tmp17_18,__tmp17_19,__tmp17_20,__tmp17_21,__tmp17_22,__tmp17_23,__tmp17_24,__tmp17_25,__tmp17_26,__tmp17_27,__tmp17_28,__tmp17_29,__tmp17_30,__tmp17_31,__tmp17_32,__tmp17_33,__tmp17_34,__tmp17_35,__tmp17_36,__tmp17_37,__tmp17_38,__tmp17_39,__tmp17_40,__tmp17_41,__tmp17_42,__tmp17_43,__tmp17_44,__tmp17_45,__tmp17_46,__tmp17_47,__tmp17_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp18_1,__tmp18_2,__tmp18_3,__tmp18_4,__tmp18_5,__tmp18_6,__tmp18_7,__tmp18_8,__tmp18_9,__tmp18_10,__tmp18_11,__tmp18_12,__tmp18_13,__tmp18_14,__tmp18_15,__tmp18_16,__tmp18_17,__tmp18_18,__tmp18_19,__tmp18_20,__tmp18_21,__tmp18_22,__tmp18_23,__tmp18_24,__tmp18_25,__tmp18_26,__tmp18_27,__tmp18_28,__tmp18_29,__tmp18_30,__tmp18_31,__tmp18_32,__tmp18_33,__tmp18_34,__tmp18_35,__tmp18_36,__tmp18_37,__tmp18_38,__tmp18_39,__tmp18_40,__tmp18_41,__tmp18_42,__tmp18_43,__tmp18_44,__tmp18_45,__tmp18_46,__tmp18_47,__tmp18_48) = roundkey5_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp17_1) land ((lnot (__tmp18_1)))) lor (((lnot (__tmp17_1))) land (__tmp18_1)),((__tmp17_2) land ((lnot (__tmp18_2)))) lor (((lnot (__tmp17_2))) land (__tmp18_2)),((__tmp17_3) land ((lnot (__tmp18_3)))) lor (((lnot (__tmp17_3))) land (__tmp18_3)),((__tmp17_4) land ((lnot (__tmp18_4)))) lor (((lnot (__tmp17_4))) land (__tmp18_4)),((__tmp17_5) land ((lnot (__tmp18_5)))) lor (((lnot (__tmp17_5))) land (__tmp18_5)),((__tmp17_6) land ((lnot (__tmp18_6)))) lor (((lnot (__tmp17_6))) land (__tmp18_6)),((__tmp17_7) land ((lnot (__tmp18_7)))) lor (((lnot (__tmp17_7))) land (__tmp18_7)),((__tmp17_8) land ((lnot (__tmp18_8)))) lor (((lnot (__tmp17_8))) land (__tmp18_8)),((__tmp17_9) land ((lnot (__tmp18_9)))) lor (((lnot (__tmp17_9))) land (__tmp18_9)),((__tmp17_10) land ((lnot (__tmp18_10)))) lor (((lnot (__tmp17_10))) land (__tmp18_10)),((__tmp17_11) land ((lnot (__tmp18_11)))) lor (((lnot (__tmp17_11))) land (__tmp18_11)),((__tmp17_12) land ((lnot (__tmp18_12)))) lor (((lnot (__tmp17_12))) land (__tmp18_12)),((__tmp17_13) land ((lnot (__tmp18_13)))) lor (((lnot (__tmp17_13))) land (__tmp18_13)),((__tmp17_14) land ((lnot (__tmp18_14)))) lor (((lnot (__tmp17_14))) land (__tmp18_14)),((__tmp17_15) land ((lnot (__tmp18_15)))) lor (((lnot (__tmp17_15))) land (__tmp18_15)),((__tmp17_16) land ((lnot (__tmp18_16)))) lor (((lnot (__tmp17_16))) land (__tmp18_16)),((__tmp17_17) land ((lnot (__tmp18_17)))) lor (((lnot (__tmp17_17))) land (__tmp18_17)),((__tmp17_18) land ((lnot (__tmp18_18)))) lor (((lnot (__tmp17_18))) land (__tmp18_18)),((__tmp17_19) land ((lnot (__tmp18_19)))) lor (((lnot (__tmp17_19))) land (__tmp18_19)),((__tmp17_20) land ((lnot (__tmp18_20)))) lor (((lnot (__tmp17_20))) land (__tmp18_20)),((__tmp17_21) land ((lnot (__tmp18_21)))) lor (((lnot (__tmp17_21))) land (__tmp18_21)),((__tmp17_22) land ((lnot (__tmp18_22)))) lor (((lnot (__tmp17_22))) land (__tmp18_22)),((__tmp17_23) land ((lnot (__tmp18_23)))) lor (((lnot (__tmp17_23))) land (__tmp18_23)),((__tmp17_24) land ((lnot (__tmp18_24)))) lor (((lnot (__tmp17_24))) land (__tmp18_24)),((__tmp17_25) land ((lnot (__tmp18_25)))) lor (((lnot (__tmp17_25))) land (__tmp18_25)),((__tmp17_26) land ((lnot (__tmp18_26)))) lor (((lnot (__tmp17_26))) land (__tmp18_26)),((__tmp17_27) land ((lnot (__tmp18_27)))) lor (((lnot (__tmp17_27))) land (__tmp18_27)),((__tmp17_28) land ((lnot (__tmp18_28)))) lor (((lnot (__tmp17_28))) land (__tmp18_28)),((__tmp17_29) land ((lnot (__tmp18_29)))) lor (((lnot (__tmp17_29))) land (__tmp18_29)),((__tmp17_30) land ((lnot (__tmp18_30)))) lor (((lnot (__tmp17_30))) land (__tmp18_30)),((__tmp17_31) land ((lnot (__tmp18_31)))) lor (((lnot (__tmp17_31))) land (__tmp18_31)),((__tmp17_32) land ((lnot (__tmp18_32)))) lor (((lnot (__tmp17_32))) land (__tmp18_32)),((__tmp17_33) land ((lnot (__tmp18_33)))) lor (((lnot (__tmp17_33))) land (__tmp18_33)),((__tmp17_34) land ((lnot (__tmp18_34)))) lor (((lnot (__tmp17_34))) land (__tmp18_34)),((__tmp17_35) land ((lnot (__tmp18_35)))) lor (((lnot (__tmp17_35))) land (__tmp18_35)),((__tmp17_36) land ((lnot (__tmp18_36)))) lor (((lnot (__tmp17_36))) land (__tmp18_36)),((__tmp17_37) land ((lnot (__tmp18_37)))) lor (((lnot (__tmp17_37))) land (__tmp18_37)),((__tmp17_38) land ((lnot (__tmp18_38)))) lor (((lnot (__tmp17_38))) land (__tmp18_38)),((__tmp17_39) land ((lnot (__tmp18_39)))) lor (((lnot (__tmp17_39))) land (__tmp18_39)),((__tmp17_40) land ((lnot (__tmp18_40)))) lor (((lnot (__tmp17_40))) land (__tmp18_40)),((__tmp17_41) land ((lnot (__tmp18_41)))) lor (((lnot (__tmp17_41))) land (__tmp18_41)),((__tmp17_42) land ((lnot (__tmp18_42)))) lor (((lnot (__tmp17_42))) land (__tmp18_42)),((__tmp17_43) land ((lnot (__tmp18_43)))) lor (((lnot (__tmp17_43))) land (__tmp18_43)),((__tmp17_44) land ((lnot (__tmp18_44)))) lor (((lnot (__tmp17_44))) land (__tmp18_44)),((__tmp17_45) land ((lnot (__tmp18_45)))) lor (((lnot (__tmp17_45))) land (__tmp18_45)),((__tmp17_46) land ((lnot (__tmp18_46)))) lor (((lnot (__tmp17_46))) land (__tmp18_46)),((__tmp17_47) land ((lnot (__tmp18_47)))) lor (((lnot (__tmp17_47))) land (__tmp18_47)),((__tmp17_48) land ((lnot (__tmp18_48)))) lor (((lnot (__tmp17_48))) land (__tmp18_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp19_1,__tmp19_2,__tmp19_3,__tmp19_4,__tmp19_5,__tmp19_6,__tmp19_7,__tmp19_8,__tmp19_9,__tmp19_10,__tmp19_11,__tmp19_12,__tmp19_13,__tmp19_14,__tmp19_15,__tmp19_16,__tmp19_17,__tmp19_18,__tmp19_19,__tmp19_20,__tmp19_21,__tmp19_22,__tmp19_23,__tmp19_24,__tmp19_25,__tmp19_26,__tmp19_27,__tmp19_28,__tmp19_29,__tmp19_30,__tmp19_31,__tmp19_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp20_1,__tmp20_2,__tmp20_3,__tmp20_4,__tmp20_5,__tmp20_6,__tmp20_7,__tmp20_8,__tmp20_9,__tmp20_10,__tmp20_11,__tmp20_12,__tmp20_13,__tmp20_14,__tmp20_15,__tmp20_16,__tmp20_17,__tmp20_18,__tmp20_19,__tmp20_20,__tmp20_21,__tmp20_22,__tmp20_23,__tmp20_24,__tmp20_25,__tmp20_26,__tmp20_27,__tmp20_28,__tmp20_29,__tmp20_30,__tmp20_31,__tmp20_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp19_1) land ((lnot (__tmp20_1)))) lor (((lnot (__tmp19_1))) land (__tmp20_1)),((__tmp19_2) land ((lnot (__tmp20_2)))) lor (((lnot (__tmp19_2))) land (__tmp20_2)),((__tmp19_3) land ((lnot (__tmp20_3)))) lor (((lnot (__tmp19_3))) land (__tmp20_3)),((__tmp19_4) land ((lnot (__tmp20_4)))) lor (((lnot (__tmp19_4))) land (__tmp20_4)),((__tmp19_5) land ((lnot (__tmp20_5)))) lor (((lnot (__tmp19_5))) land (__tmp20_5)),((__tmp19_6) land ((lnot (__tmp20_6)))) lor (((lnot (__tmp19_6))) land (__tmp20_6)),((__tmp19_7) land ((lnot (__tmp20_7)))) lor (((lnot (__tmp19_7))) land (__tmp20_7)),((__tmp19_8) land ((lnot (__tmp20_8)))) lor (((lnot (__tmp19_8))) land (__tmp20_8)),((__tmp19_9) land ((lnot (__tmp20_9)))) lor (((lnot (__tmp19_9))) land (__tmp20_9)),((__tmp19_10) land ((lnot (__tmp20_10)))) lor (((lnot (__tmp19_10))) land (__tmp20_10)),((__tmp19_11) land ((lnot (__tmp20_11)))) lor (((lnot (__tmp19_11))) land (__tmp20_11)),((__tmp19_12) land ((lnot (__tmp20_12)))) lor (((lnot (__tmp19_12))) land (__tmp20_12)),((__tmp19_13) land ((lnot (__tmp20_13)))) lor (((lnot (__tmp19_13))) land (__tmp20_13)),((__tmp19_14) land ((lnot (__tmp20_14)))) lor (((lnot (__tmp19_14))) land (__tmp20_14)),((__tmp19_15) land ((lnot (__tmp20_15)))) lor (((lnot (__tmp19_15))) land (__tmp20_15)),((__tmp19_16) land ((lnot (__tmp20_16)))) lor (((lnot (__tmp19_16))) land (__tmp20_16)),((__tmp19_17) land ((lnot (__tmp20_17)))) lor (((lnot (__tmp19_17))) land (__tmp20_17)),((__tmp19_18) land ((lnot (__tmp20_18)))) lor (((lnot (__tmp19_18))) land (__tmp20_18)),((__tmp19_19) land ((lnot (__tmp20_19)))) lor (((lnot (__tmp19_19))) land (__tmp20_19)),((__tmp19_20) land ((lnot (__tmp20_20)))) lor (((lnot (__tmp19_20))) land (__tmp20_20)),((__tmp19_21) land ((lnot (__tmp20_21)))) lor (((lnot (__tmp19_21))) land (__tmp20_21)),((__tmp19_22) land ((lnot (__tmp20_22)))) lor (((lnot (__tmp19_22))) land (__tmp20_22)),((__tmp19_23) land ((lnot (__tmp20_23)))) lor (((lnot (__tmp19_23))) land (__tmp20_23)),((__tmp19_24) land ((lnot (__tmp20_24)))) lor (((lnot (__tmp19_24))) land (__tmp20_24)),((__tmp19_25) land ((lnot (__tmp20_25)))) lor (((lnot (__tmp19_25))) land (__tmp20_25)),((__tmp19_26) land ((lnot (__tmp20_26)))) lor (((lnot (__tmp19_26))) land (__tmp20_26)),((__tmp19_27) land ((lnot (__tmp20_27)))) lor (((lnot (__tmp19_27))) land (__tmp20_27)),((__tmp19_28) land ((lnot (__tmp20_28)))) lor (((lnot (__tmp19_28))) land (__tmp20_28)),((__tmp19_29) land ((lnot (__tmp20_29)))) lor (((lnot (__tmp19_29))) land (__tmp20_29)),((__tmp19_30) land ((lnot (__tmp20_30)))) lor (((lnot (__tmp19_30))) land (__tmp20_30)),((__tmp19_31) land ((lnot (__tmp20_31)))) lor (((lnot (__tmp19_31))) land (__tmp20_31)),((__tmp19_32) land ((lnot (__tmp20_32)))) lor (((lnot (__tmp19_32))) land (__tmp20_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single6_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp21_1,__tmp21_2,__tmp21_3,__tmp21_4,__tmp21_5,__tmp21_6,__tmp21_7,__tmp21_8,__tmp21_9,__tmp21_10,__tmp21_11,__tmp21_12,__tmp21_13,__tmp21_14,__tmp21_15,__tmp21_16,__tmp21_17,__tmp21_18,__tmp21_19,__tmp21_20,__tmp21_21,__tmp21_22,__tmp21_23,__tmp21_24,__tmp21_25,__tmp21_26,__tmp21_27,__tmp21_28,__tmp21_29,__tmp21_30,__tmp21_31,__tmp21_32,__tmp21_33,__tmp21_34,__tmp21_35,__tmp21_36,__tmp21_37,__tmp21_38,__tmp21_39,__tmp21_40,__tmp21_41,__tmp21_42,__tmp21_43,__tmp21_44,__tmp21_45,__tmp21_46,__tmp21_47,__tmp21_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp22_1,__tmp22_2,__tmp22_3,__tmp22_4,__tmp22_5,__tmp22_6,__tmp22_7,__tmp22_8,__tmp22_9,__tmp22_10,__tmp22_11,__tmp22_12,__tmp22_13,__tmp22_14,__tmp22_15,__tmp22_16,__tmp22_17,__tmp22_18,__tmp22_19,__tmp22_20,__tmp22_21,__tmp22_22,__tmp22_23,__tmp22_24,__tmp22_25,__tmp22_26,__tmp22_27,__tmp22_28,__tmp22_29,__tmp22_30,__tmp22_31,__tmp22_32,__tmp22_33,__tmp22_34,__tmp22_35,__tmp22_36,__tmp22_37,__tmp22_38,__tmp22_39,__tmp22_40,__tmp22_41,__tmp22_42,__tmp22_43,__tmp22_44,__tmp22_45,__tmp22_46,__tmp22_47,__tmp22_48) = roundkey6_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp21_1) land ((lnot (__tmp22_1)))) lor (((lnot (__tmp21_1))) land (__tmp22_1)),((__tmp21_2) land ((lnot (__tmp22_2)))) lor (((lnot (__tmp21_2))) land (__tmp22_2)),((__tmp21_3) land ((lnot (__tmp22_3)))) lor (((lnot (__tmp21_3))) land (__tmp22_3)),((__tmp21_4) land ((lnot (__tmp22_4)))) lor (((lnot (__tmp21_4))) land (__tmp22_4)),((__tmp21_5) land ((lnot (__tmp22_5)))) lor (((lnot (__tmp21_5))) land (__tmp22_5)),((__tmp21_6) land ((lnot (__tmp22_6)))) lor (((lnot (__tmp21_6))) land (__tmp22_6)),((__tmp21_7) land ((lnot (__tmp22_7)))) lor (((lnot (__tmp21_7))) land (__tmp22_7)),((__tmp21_8) land ((lnot (__tmp22_8)))) lor (((lnot (__tmp21_8))) land (__tmp22_8)),((__tmp21_9) land ((lnot (__tmp22_9)))) lor (((lnot (__tmp21_9))) land (__tmp22_9)),((__tmp21_10) land ((lnot (__tmp22_10)))) lor (((lnot (__tmp21_10))) land (__tmp22_10)),((__tmp21_11) land ((lnot (__tmp22_11)))) lor (((lnot (__tmp21_11))) land (__tmp22_11)),((__tmp21_12) land ((lnot (__tmp22_12)))) lor (((lnot (__tmp21_12))) land (__tmp22_12)),((__tmp21_13) land ((lnot (__tmp22_13)))) lor (((lnot (__tmp21_13))) land (__tmp22_13)),((__tmp21_14) land ((lnot (__tmp22_14)))) lor (((lnot (__tmp21_14))) land (__tmp22_14)),((__tmp21_15) land ((lnot (__tmp22_15)))) lor (((lnot (__tmp21_15))) land (__tmp22_15)),((__tmp21_16) land ((lnot (__tmp22_16)))) lor (((lnot (__tmp21_16))) land (__tmp22_16)),((__tmp21_17) land ((lnot (__tmp22_17)))) lor (((lnot (__tmp21_17))) land (__tmp22_17)),((__tmp21_18) land ((lnot (__tmp22_18)))) lor (((lnot (__tmp21_18))) land (__tmp22_18)),((__tmp21_19) land ((lnot (__tmp22_19)))) lor (((lnot (__tmp21_19))) land (__tmp22_19)),((__tmp21_20) land ((lnot (__tmp22_20)))) lor (((lnot (__tmp21_20))) land (__tmp22_20)),((__tmp21_21) land ((lnot (__tmp22_21)))) lor (((lnot (__tmp21_21))) land (__tmp22_21)),((__tmp21_22) land ((lnot (__tmp22_22)))) lor (((lnot (__tmp21_22))) land (__tmp22_22)),((__tmp21_23) land ((lnot (__tmp22_23)))) lor (((lnot (__tmp21_23))) land (__tmp22_23)),((__tmp21_24) land ((lnot (__tmp22_24)))) lor (((lnot (__tmp21_24))) land (__tmp22_24)),((__tmp21_25) land ((lnot (__tmp22_25)))) lor (((lnot (__tmp21_25))) land (__tmp22_25)),((__tmp21_26) land ((lnot (__tmp22_26)))) lor (((lnot (__tmp21_26))) land (__tmp22_26)),((__tmp21_27) land ((lnot (__tmp22_27)))) lor (((lnot (__tmp21_27))) land (__tmp22_27)),((__tmp21_28) land ((lnot (__tmp22_28)))) lor (((lnot (__tmp21_28))) land (__tmp22_28)),((__tmp21_29) land ((lnot (__tmp22_29)))) lor (((lnot (__tmp21_29))) land (__tmp22_29)),((__tmp21_30) land ((lnot (__tmp22_30)))) lor (((lnot (__tmp21_30))) land (__tmp22_30)),((__tmp21_31) land ((lnot (__tmp22_31)))) lor (((lnot (__tmp21_31))) land (__tmp22_31)),((__tmp21_32) land ((lnot (__tmp22_32)))) lor (((lnot (__tmp21_32))) land (__tmp22_32)),((__tmp21_33) land ((lnot (__tmp22_33)))) lor (((lnot (__tmp21_33))) land (__tmp22_33)),((__tmp21_34) land ((lnot (__tmp22_34)))) lor (((lnot (__tmp21_34))) land (__tmp22_34)),((__tmp21_35) land ((lnot (__tmp22_35)))) lor (((lnot (__tmp21_35))) land (__tmp22_35)),((__tmp21_36) land ((lnot (__tmp22_36)))) lor (((lnot (__tmp21_36))) land (__tmp22_36)),((__tmp21_37) land ((lnot (__tmp22_37)))) lor (((lnot (__tmp21_37))) land (__tmp22_37)),((__tmp21_38) land ((lnot (__tmp22_38)))) lor (((lnot (__tmp21_38))) land (__tmp22_38)),((__tmp21_39) land ((lnot (__tmp22_39)))) lor (((lnot (__tmp21_39))) land (__tmp22_39)),((__tmp21_40) land ((lnot (__tmp22_40)))) lor (((lnot (__tmp21_40))) land (__tmp22_40)),((__tmp21_41) land ((lnot (__tmp22_41)))) lor (((lnot (__tmp21_41))) land (__tmp22_41)),((__tmp21_42) land ((lnot (__tmp22_42)))) lor (((lnot (__tmp21_42))) land (__tmp22_42)),((__tmp21_43) land ((lnot (__tmp22_43)))) lor (((lnot (__tmp21_43))) land (__tmp22_43)),((__tmp21_44) land ((lnot (__tmp22_44)))) lor (((lnot (__tmp21_44))) land (__tmp22_44)),((__tmp21_45) land ((lnot (__tmp22_45)))) lor (((lnot (__tmp21_45))) land (__tmp22_45)),((__tmp21_46) land ((lnot (__tmp22_46)))) lor (((lnot (__tmp21_46))) land (__tmp22_46)),((__tmp21_47) land ((lnot (__tmp22_47)))) lor (((lnot (__tmp21_47))) land (__tmp22_47)),((__tmp21_48) land ((lnot (__tmp22_48)))) lor (((lnot (__tmp21_48))) land (__tmp22_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp23_1,__tmp23_2,__tmp23_3,__tmp23_4,__tmp23_5,__tmp23_6,__tmp23_7,__tmp23_8,__tmp23_9,__tmp23_10,__tmp23_11,__tmp23_12,__tmp23_13,__tmp23_14,__tmp23_15,__tmp23_16,__tmp23_17,__tmp23_18,__tmp23_19,__tmp23_20,__tmp23_21,__tmp23_22,__tmp23_23,__tmp23_24,__tmp23_25,__tmp23_26,__tmp23_27,__tmp23_28,__tmp23_29,__tmp23_30,__tmp23_31,__tmp23_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp24_1,__tmp24_2,__tmp24_3,__tmp24_4,__tmp24_5,__tmp24_6,__tmp24_7,__tmp24_8,__tmp24_9,__tmp24_10,__tmp24_11,__tmp24_12,__tmp24_13,__tmp24_14,__tmp24_15,__tmp24_16,__tmp24_17,__tmp24_18,__tmp24_19,__tmp24_20,__tmp24_21,__tmp24_22,__tmp24_23,__tmp24_24,__tmp24_25,__tmp24_26,__tmp24_27,__tmp24_28,__tmp24_29,__tmp24_30,__tmp24_31,__tmp24_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp23_1) land ((lnot (__tmp24_1)))) lor (((lnot (__tmp23_1))) land (__tmp24_1)),((__tmp23_2) land ((lnot (__tmp24_2)))) lor (((lnot (__tmp23_2))) land (__tmp24_2)),((__tmp23_3) land ((lnot (__tmp24_3)))) lor (((lnot (__tmp23_3))) land (__tmp24_3)),((__tmp23_4) land ((lnot (__tmp24_4)))) lor (((lnot (__tmp23_4))) land (__tmp24_4)),((__tmp23_5) land ((lnot (__tmp24_5)))) lor (((lnot (__tmp23_5))) land (__tmp24_5)),((__tmp23_6) land ((lnot (__tmp24_6)))) lor (((lnot (__tmp23_6))) land (__tmp24_6)),((__tmp23_7) land ((lnot (__tmp24_7)))) lor (((lnot (__tmp23_7))) land (__tmp24_7)),((__tmp23_8) land ((lnot (__tmp24_8)))) lor (((lnot (__tmp23_8))) land (__tmp24_8)),((__tmp23_9) land ((lnot (__tmp24_9)))) lor (((lnot (__tmp23_9))) land (__tmp24_9)),((__tmp23_10) land ((lnot (__tmp24_10)))) lor (((lnot (__tmp23_10))) land (__tmp24_10)),((__tmp23_11) land ((lnot (__tmp24_11)))) lor (((lnot (__tmp23_11))) land (__tmp24_11)),((__tmp23_12) land ((lnot (__tmp24_12)))) lor (((lnot (__tmp23_12))) land (__tmp24_12)),((__tmp23_13) land ((lnot (__tmp24_13)))) lor (((lnot (__tmp23_13))) land (__tmp24_13)),((__tmp23_14) land ((lnot (__tmp24_14)))) lor (((lnot (__tmp23_14))) land (__tmp24_14)),((__tmp23_15) land ((lnot (__tmp24_15)))) lor (((lnot (__tmp23_15))) land (__tmp24_15)),((__tmp23_16) land ((lnot (__tmp24_16)))) lor (((lnot (__tmp23_16))) land (__tmp24_16)),((__tmp23_17) land ((lnot (__tmp24_17)))) lor (((lnot (__tmp23_17))) land (__tmp24_17)),((__tmp23_18) land ((lnot (__tmp24_18)))) lor (((lnot (__tmp23_18))) land (__tmp24_18)),((__tmp23_19) land ((lnot (__tmp24_19)))) lor (((lnot (__tmp23_19))) land (__tmp24_19)),((__tmp23_20) land ((lnot (__tmp24_20)))) lor (((lnot (__tmp23_20))) land (__tmp24_20)),((__tmp23_21) land ((lnot (__tmp24_21)))) lor (((lnot (__tmp23_21))) land (__tmp24_21)),((__tmp23_22) land ((lnot (__tmp24_22)))) lor (((lnot (__tmp23_22))) land (__tmp24_22)),((__tmp23_23) land ((lnot (__tmp24_23)))) lor (((lnot (__tmp23_23))) land (__tmp24_23)),((__tmp23_24) land ((lnot (__tmp24_24)))) lor (((lnot (__tmp23_24))) land (__tmp24_24)),((__tmp23_25) land ((lnot (__tmp24_25)))) lor (((lnot (__tmp23_25))) land (__tmp24_25)),((__tmp23_26) land ((lnot (__tmp24_26)))) lor (((lnot (__tmp23_26))) land (__tmp24_26)),((__tmp23_27) land ((lnot (__tmp24_27)))) lor (((lnot (__tmp23_27))) land (__tmp24_27)),((__tmp23_28) land ((lnot (__tmp24_28)))) lor (((lnot (__tmp23_28))) land (__tmp24_28)),((__tmp23_29) land ((lnot (__tmp24_29)))) lor (((lnot (__tmp23_29))) land (__tmp24_29)),((__tmp23_30) land ((lnot (__tmp24_30)))) lor (((lnot (__tmp23_30))) land (__tmp24_30)),((__tmp23_31) land ((lnot (__tmp24_31)))) lor (((lnot (__tmp23_31))) land (__tmp24_31)),((__tmp23_32) land ((lnot (__tmp24_32)))) lor (((lnot (__tmp23_32))) land (__tmp24_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single7_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp25_1,__tmp25_2,__tmp25_3,__tmp25_4,__tmp25_5,__tmp25_6,__tmp25_7,__tmp25_8,__tmp25_9,__tmp25_10,__tmp25_11,__tmp25_12,__tmp25_13,__tmp25_14,__tmp25_15,__tmp25_16,__tmp25_17,__tmp25_18,__tmp25_19,__tmp25_20,__tmp25_21,__tmp25_22,__tmp25_23,__tmp25_24,__tmp25_25,__tmp25_26,__tmp25_27,__tmp25_28,__tmp25_29,__tmp25_30,__tmp25_31,__tmp25_32,__tmp25_33,__tmp25_34,__tmp25_35,__tmp25_36,__tmp25_37,__tmp25_38,__tmp25_39,__tmp25_40,__tmp25_41,__tmp25_42,__tmp25_43,__tmp25_44,__tmp25_45,__tmp25_46,__tmp25_47,__tmp25_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp26_1,__tmp26_2,__tmp26_3,__tmp26_4,__tmp26_5,__tmp26_6,__tmp26_7,__tmp26_8,__tmp26_9,__tmp26_10,__tmp26_11,__tmp26_12,__tmp26_13,__tmp26_14,__tmp26_15,__tmp26_16,__tmp26_17,__tmp26_18,__tmp26_19,__tmp26_20,__tmp26_21,__tmp26_22,__tmp26_23,__tmp26_24,__tmp26_25,__tmp26_26,__tmp26_27,__tmp26_28,__tmp26_29,__tmp26_30,__tmp26_31,__tmp26_32,__tmp26_33,__tmp26_34,__tmp26_35,__tmp26_36,__tmp26_37,__tmp26_38,__tmp26_39,__tmp26_40,__tmp26_41,__tmp26_42,__tmp26_43,__tmp26_44,__tmp26_45,__tmp26_46,__tmp26_47,__tmp26_48) = roundkey7_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp25_1) land ((lnot (__tmp26_1)))) lor (((lnot (__tmp25_1))) land (__tmp26_1)),((__tmp25_2) land ((lnot (__tmp26_2)))) lor (((lnot (__tmp25_2))) land (__tmp26_2)),((__tmp25_3) land ((lnot (__tmp26_3)))) lor (((lnot (__tmp25_3))) land (__tmp26_3)),((__tmp25_4) land ((lnot (__tmp26_4)))) lor (((lnot (__tmp25_4))) land (__tmp26_4)),((__tmp25_5) land ((lnot (__tmp26_5)))) lor (((lnot (__tmp25_5))) land (__tmp26_5)),((__tmp25_6) land ((lnot (__tmp26_6)))) lor (((lnot (__tmp25_6))) land (__tmp26_6)),((__tmp25_7) land ((lnot (__tmp26_7)))) lor (((lnot (__tmp25_7))) land (__tmp26_7)),((__tmp25_8) land ((lnot (__tmp26_8)))) lor (((lnot (__tmp25_8))) land (__tmp26_8)),((__tmp25_9) land ((lnot (__tmp26_9)))) lor (((lnot (__tmp25_9))) land (__tmp26_9)),((__tmp25_10) land ((lnot (__tmp26_10)))) lor (((lnot (__tmp25_10))) land (__tmp26_10)),((__tmp25_11) land ((lnot (__tmp26_11)))) lor (((lnot (__tmp25_11))) land (__tmp26_11)),((__tmp25_12) land ((lnot (__tmp26_12)))) lor (((lnot (__tmp25_12))) land (__tmp26_12)),((__tmp25_13) land ((lnot (__tmp26_13)))) lor (((lnot (__tmp25_13))) land (__tmp26_13)),((__tmp25_14) land ((lnot (__tmp26_14)))) lor (((lnot (__tmp25_14))) land (__tmp26_14)),((__tmp25_15) land ((lnot (__tmp26_15)))) lor (((lnot (__tmp25_15))) land (__tmp26_15)),((__tmp25_16) land ((lnot (__tmp26_16)))) lor (((lnot (__tmp25_16))) land (__tmp26_16)),((__tmp25_17) land ((lnot (__tmp26_17)))) lor (((lnot (__tmp25_17))) land (__tmp26_17)),((__tmp25_18) land ((lnot (__tmp26_18)))) lor (((lnot (__tmp25_18))) land (__tmp26_18)),((__tmp25_19) land ((lnot (__tmp26_19)))) lor (((lnot (__tmp25_19))) land (__tmp26_19)),((__tmp25_20) land ((lnot (__tmp26_20)))) lor (((lnot (__tmp25_20))) land (__tmp26_20)),((__tmp25_21) land ((lnot (__tmp26_21)))) lor (((lnot (__tmp25_21))) land (__tmp26_21)),((__tmp25_22) land ((lnot (__tmp26_22)))) lor (((lnot (__tmp25_22))) land (__tmp26_22)),((__tmp25_23) land ((lnot (__tmp26_23)))) lor (((lnot (__tmp25_23))) land (__tmp26_23)),((__tmp25_24) land ((lnot (__tmp26_24)))) lor (((lnot (__tmp25_24))) land (__tmp26_24)),((__tmp25_25) land ((lnot (__tmp26_25)))) lor (((lnot (__tmp25_25))) land (__tmp26_25)),((__tmp25_26) land ((lnot (__tmp26_26)))) lor (((lnot (__tmp25_26))) land (__tmp26_26)),((__tmp25_27) land ((lnot (__tmp26_27)))) lor (((lnot (__tmp25_27))) land (__tmp26_27)),((__tmp25_28) land ((lnot (__tmp26_28)))) lor (((lnot (__tmp25_28))) land (__tmp26_28)),((__tmp25_29) land ((lnot (__tmp26_29)))) lor (((lnot (__tmp25_29))) land (__tmp26_29)),((__tmp25_30) land ((lnot (__tmp26_30)))) lor (((lnot (__tmp25_30))) land (__tmp26_30)),((__tmp25_31) land ((lnot (__tmp26_31)))) lor (((lnot (__tmp25_31))) land (__tmp26_31)),((__tmp25_32) land ((lnot (__tmp26_32)))) lor (((lnot (__tmp25_32))) land (__tmp26_32)),((__tmp25_33) land ((lnot (__tmp26_33)))) lor (((lnot (__tmp25_33))) land (__tmp26_33)),((__tmp25_34) land ((lnot (__tmp26_34)))) lor (((lnot (__tmp25_34))) land (__tmp26_34)),((__tmp25_35) land ((lnot (__tmp26_35)))) lor (((lnot (__tmp25_35))) land (__tmp26_35)),((__tmp25_36) land ((lnot (__tmp26_36)))) lor (((lnot (__tmp25_36))) land (__tmp26_36)),((__tmp25_37) land ((lnot (__tmp26_37)))) lor (((lnot (__tmp25_37))) land (__tmp26_37)),((__tmp25_38) land ((lnot (__tmp26_38)))) lor (((lnot (__tmp25_38))) land (__tmp26_38)),((__tmp25_39) land ((lnot (__tmp26_39)))) lor (((lnot (__tmp25_39))) land (__tmp26_39)),((__tmp25_40) land ((lnot (__tmp26_40)))) lor (((lnot (__tmp25_40))) land (__tmp26_40)),((__tmp25_41) land ((lnot (__tmp26_41)))) lor (((lnot (__tmp25_41))) land (__tmp26_41)),((__tmp25_42) land ((lnot (__tmp26_42)))) lor (((lnot (__tmp25_42))) land (__tmp26_42)),((__tmp25_43) land ((lnot (__tmp26_43)))) lor (((lnot (__tmp25_43))) land (__tmp26_43)),((__tmp25_44) land ((lnot (__tmp26_44)))) lor (((lnot (__tmp25_44))) land (__tmp26_44)),((__tmp25_45) land ((lnot (__tmp26_45)))) lor (((lnot (__tmp25_45))) land (__tmp26_45)),((__tmp25_46) land ((lnot (__tmp26_46)))) lor (((lnot (__tmp25_46))) land (__tmp26_46)),((__tmp25_47) land ((lnot (__tmp26_47)))) lor (((lnot (__tmp25_47))) land (__tmp26_47)),((__tmp25_48) land ((lnot (__tmp26_48)))) lor (((lnot (__tmp25_48))) land (__tmp26_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp27_1,__tmp27_2,__tmp27_3,__tmp27_4,__tmp27_5,__tmp27_6,__tmp27_7,__tmp27_8,__tmp27_9,__tmp27_10,__tmp27_11,__tmp27_12,__tmp27_13,__tmp27_14,__tmp27_15,__tmp27_16,__tmp27_17,__tmp27_18,__tmp27_19,__tmp27_20,__tmp27_21,__tmp27_22,__tmp27_23,__tmp27_24,__tmp27_25,__tmp27_26,__tmp27_27,__tmp27_28,__tmp27_29,__tmp27_30,__tmp27_31,__tmp27_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp28_1,__tmp28_2,__tmp28_3,__tmp28_4,__tmp28_5,__tmp28_6,__tmp28_7,__tmp28_8,__tmp28_9,__tmp28_10,__tmp28_11,__tmp28_12,__tmp28_13,__tmp28_14,__tmp28_15,__tmp28_16,__tmp28_17,__tmp28_18,__tmp28_19,__tmp28_20,__tmp28_21,__tmp28_22,__tmp28_23,__tmp28_24,__tmp28_25,__tmp28_26,__tmp28_27,__tmp28_28,__tmp28_29,__tmp28_30,__tmp28_31,__tmp28_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp27_1) land ((lnot (__tmp28_1)))) lor (((lnot (__tmp27_1))) land (__tmp28_1)),((__tmp27_2) land ((lnot (__tmp28_2)))) lor (((lnot (__tmp27_2))) land (__tmp28_2)),((__tmp27_3) land ((lnot (__tmp28_3)))) lor (((lnot (__tmp27_3))) land (__tmp28_3)),((__tmp27_4) land ((lnot (__tmp28_4)))) lor (((lnot (__tmp27_4))) land (__tmp28_4)),((__tmp27_5) land ((lnot (__tmp28_5)))) lor (((lnot (__tmp27_5))) land (__tmp28_5)),((__tmp27_6) land ((lnot (__tmp28_6)))) lor (((lnot (__tmp27_6))) land (__tmp28_6)),((__tmp27_7) land ((lnot (__tmp28_7)))) lor (((lnot (__tmp27_7))) land (__tmp28_7)),((__tmp27_8) land ((lnot (__tmp28_8)))) lor (((lnot (__tmp27_8))) land (__tmp28_8)),((__tmp27_9) land ((lnot (__tmp28_9)))) lor (((lnot (__tmp27_9))) land (__tmp28_9)),((__tmp27_10) land ((lnot (__tmp28_10)))) lor (((lnot (__tmp27_10))) land (__tmp28_10)),((__tmp27_11) land ((lnot (__tmp28_11)))) lor (((lnot (__tmp27_11))) land (__tmp28_11)),((__tmp27_12) land ((lnot (__tmp28_12)))) lor (((lnot (__tmp27_12))) land (__tmp28_12)),((__tmp27_13) land ((lnot (__tmp28_13)))) lor (((lnot (__tmp27_13))) land (__tmp28_13)),((__tmp27_14) land ((lnot (__tmp28_14)))) lor (((lnot (__tmp27_14))) land (__tmp28_14)),((__tmp27_15) land ((lnot (__tmp28_15)))) lor (((lnot (__tmp27_15))) land (__tmp28_15)),((__tmp27_16) land ((lnot (__tmp28_16)))) lor (((lnot (__tmp27_16))) land (__tmp28_16)),((__tmp27_17) land ((lnot (__tmp28_17)))) lor (((lnot (__tmp27_17))) land (__tmp28_17)),((__tmp27_18) land ((lnot (__tmp28_18)))) lor (((lnot (__tmp27_18))) land (__tmp28_18)),((__tmp27_19) land ((lnot (__tmp28_19)))) lor (((lnot (__tmp27_19))) land (__tmp28_19)),((__tmp27_20) land ((lnot (__tmp28_20)))) lor (((lnot (__tmp27_20))) land (__tmp28_20)),((__tmp27_21) land ((lnot (__tmp28_21)))) lor (((lnot (__tmp27_21))) land (__tmp28_21)),((__tmp27_22) land ((lnot (__tmp28_22)))) lor (((lnot (__tmp27_22))) land (__tmp28_22)),((__tmp27_23) land ((lnot (__tmp28_23)))) lor (((lnot (__tmp27_23))) land (__tmp28_23)),((__tmp27_24) land ((lnot (__tmp28_24)))) lor (((lnot (__tmp27_24))) land (__tmp28_24)),((__tmp27_25) land ((lnot (__tmp28_25)))) lor (((lnot (__tmp27_25))) land (__tmp28_25)),((__tmp27_26) land ((lnot (__tmp28_26)))) lor (((lnot (__tmp27_26))) land (__tmp28_26)),((__tmp27_27) land ((lnot (__tmp28_27)))) lor (((lnot (__tmp27_27))) land (__tmp28_27)),((__tmp27_28) land ((lnot (__tmp28_28)))) lor (((lnot (__tmp27_28))) land (__tmp28_28)),((__tmp27_29) land ((lnot (__tmp28_29)))) lor (((lnot (__tmp27_29))) land (__tmp28_29)),((__tmp27_30) land ((lnot (__tmp28_30)))) lor (((lnot (__tmp27_30))) land (__tmp28_30)),((__tmp27_31) land ((lnot (__tmp28_31)))) lor (((lnot (__tmp27_31))) land (__tmp28_31)),((__tmp27_32) land ((lnot (__tmp28_32)))) lor (((lnot (__tmp27_32))) land (__tmp28_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single8_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp29_1,__tmp29_2,__tmp29_3,__tmp29_4,__tmp29_5,__tmp29_6,__tmp29_7,__tmp29_8,__tmp29_9,__tmp29_10,__tmp29_11,__tmp29_12,__tmp29_13,__tmp29_14,__tmp29_15,__tmp29_16,__tmp29_17,__tmp29_18,__tmp29_19,__tmp29_20,__tmp29_21,__tmp29_22,__tmp29_23,__tmp29_24,__tmp29_25,__tmp29_26,__tmp29_27,__tmp29_28,__tmp29_29,__tmp29_30,__tmp29_31,__tmp29_32,__tmp29_33,__tmp29_34,__tmp29_35,__tmp29_36,__tmp29_37,__tmp29_38,__tmp29_39,__tmp29_40,__tmp29_41,__tmp29_42,__tmp29_43,__tmp29_44,__tmp29_45,__tmp29_46,__tmp29_47,__tmp29_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp30_1,__tmp30_2,__tmp30_3,__tmp30_4,__tmp30_5,__tmp30_6,__tmp30_7,__tmp30_8,__tmp30_9,__tmp30_10,__tmp30_11,__tmp30_12,__tmp30_13,__tmp30_14,__tmp30_15,__tmp30_16,__tmp30_17,__tmp30_18,__tmp30_19,__tmp30_20,__tmp30_21,__tmp30_22,__tmp30_23,__tmp30_24,__tmp30_25,__tmp30_26,__tmp30_27,__tmp30_28,__tmp30_29,__tmp30_30,__tmp30_31,__tmp30_32,__tmp30_33,__tmp30_34,__tmp30_35,__tmp30_36,__tmp30_37,__tmp30_38,__tmp30_39,__tmp30_40,__tmp30_41,__tmp30_42,__tmp30_43,__tmp30_44,__tmp30_45,__tmp30_46,__tmp30_47,__tmp30_48) = roundkey8_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp29_1) land ((lnot (__tmp30_1)))) lor (((lnot (__tmp29_1))) land (__tmp30_1)),((__tmp29_2) land ((lnot (__tmp30_2)))) lor (((lnot (__tmp29_2))) land (__tmp30_2)),((__tmp29_3) land ((lnot (__tmp30_3)))) lor (((lnot (__tmp29_3))) land (__tmp30_3)),((__tmp29_4) land ((lnot (__tmp30_4)))) lor (((lnot (__tmp29_4))) land (__tmp30_4)),((__tmp29_5) land ((lnot (__tmp30_5)))) lor (((lnot (__tmp29_5))) land (__tmp30_5)),((__tmp29_6) land ((lnot (__tmp30_6)))) lor (((lnot (__tmp29_6))) land (__tmp30_6)),((__tmp29_7) land ((lnot (__tmp30_7)))) lor (((lnot (__tmp29_7))) land (__tmp30_7)),((__tmp29_8) land ((lnot (__tmp30_8)))) lor (((lnot (__tmp29_8))) land (__tmp30_8)),((__tmp29_9) land ((lnot (__tmp30_9)))) lor (((lnot (__tmp29_9))) land (__tmp30_9)),((__tmp29_10) land ((lnot (__tmp30_10)))) lor (((lnot (__tmp29_10))) land (__tmp30_10)),((__tmp29_11) land ((lnot (__tmp30_11)))) lor (((lnot (__tmp29_11))) land (__tmp30_11)),((__tmp29_12) land ((lnot (__tmp30_12)))) lor (((lnot (__tmp29_12))) land (__tmp30_12)),((__tmp29_13) land ((lnot (__tmp30_13)))) lor (((lnot (__tmp29_13))) land (__tmp30_13)),((__tmp29_14) land ((lnot (__tmp30_14)))) lor (((lnot (__tmp29_14))) land (__tmp30_14)),((__tmp29_15) land ((lnot (__tmp30_15)))) lor (((lnot (__tmp29_15))) land (__tmp30_15)),((__tmp29_16) land ((lnot (__tmp30_16)))) lor (((lnot (__tmp29_16))) land (__tmp30_16)),((__tmp29_17) land ((lnot (__tmp30_17)))) lor (((lnot (__tmp29_17))) land (__tmp30_17)),((__tmp29_18) land ((lnot (__tmp30_18)))) lor (((lnot (__tmp29_18))) land (__tmp30_18)),((__tmp29_19) land ((lnot (__tmp30_19)))) lor (((lnot (__tmp29_19))) land (__tmp30_19)),((__tmp29_20) land ((lnot (__tmp30_20)))) lor (((lnot (__tmp29_20))) land (__tmp30_20)),((__tmp29_21) land ((lnot (__tmp30_21)))) lor (((lnot (__tmp29_21))) land (__tmp30_21)),((__tmp29_22) land ((lnot (__tmp30_22)))) lor (((lnot (__tmp29_22))) land (__tmp30_22)),((__tmp29_23) land ((lnot (__tmp30_23)))) lor (((lnot (__tmp29_23))) land (__tmp30_23)),((__tmp29_24) land ((lnot (__tmp30_24)))) lor (((lnot (__tmp29_24))) land (__tmp30_24)),((__tmp29_25) land ((lnot (__tmp30_25)))) lor (((lnot (__tmp29_25))) land (__tmp30_25)),((__tmp29_26) land ((lnot (__tmp30_26)))) lor (((lnot (__tmp29_26))) land (__tmp30_26)),((__tmp29_27) land ((lnot (__tmp30_27)))) lor (((lnot (__tmp29_27))) land (__tmp30_27)),((__tmp29_28) land ((lnot (__tmp30_28)))) lor (((lnot (__tmp29_28))) land (__tmp30_28)),((__tmp29_29) land ((lnot (__tmp30_29)))) lor (((lnot (__tmp29_29))) land (__tmp30_29)),((__tmp29_30) land ((lnot (__tmp30_30)))) lor (((lnot (__tmp29_30))) land (__tmp30_30)),((__tmp29_31) land ((lnot (__tmp30_31)))) lor (((lnot (__tmp29_31))) land (__tmp30_31)),((__tmp29_32) land ((lnot (__tmp30_32)))) lor (((lnot (__tmp29_32))) land (__tmp30_32)),((__tmp29_33) land ((lnot (__tmp30_33)))) lor (((lnot (__tmp29_33))) land (__tmp30_33)),((__tmp29_34) land ((lnot (__tmp30_34)))) lor (((lnot (__tmp29_34))) land (__tmp30_34)),((__tmp29_35) land ((lnot (__tmp30_35)))) lor (((lnot (__tmp29_35))) land (__tmp30_35)),((__tmp29_36) land ((lnot (__tmp30_36)))) lor (((lnot (__tmp29_36))) land (__tmp30_36)),((__tmp29_37) land ((lnot (__tmp30_37)))) lor (((lnot (__tmp29_37))) land (__tmp30_37)),((__tmp29_38) land ((lnot (__tmp30_38)))) lor (((lnot (__tmp29_38))) land (__tmp30_38)),((__tmp29_39) land ((lnot (__tmp30_39)))) lor (((lnot (__tmp29_39))) land (__tmp30_39)),((__tmp29_40) land ((lnot (__tmp30_40)))) lor (((lnot (__tmp29_40))) land (__tmp30_40)),((__tmp29_41) land ((lnot (__tmp30_41)))) lor (((lnot (__tmp29_41))) land (__tmp30_41)),((__tmp29_42) land ((lnot (__tmp30_42)))) lor (((lnot (__tmp29_42))) land (__tmp30_42)),((__tmp29_43) land ((lnot (__tmp30_43)))) lor (((lnot (__tmp29_43))) land (__tmp30_43)),((__tmp29_44) land ((lnot (__tmp30_44)))) lor (((lnot (__tmp29_44))) land (__tmp30_44)),((__tmp29_45) land ((lnot (__tmp30_45)))) lor (((lnot (__tmp29_45))) land (__tmp30_45)),((__tmp29_46) land ((lnot (__tmp30_46)))) lor (((lnot (__tmp29_46))) land (__tmp30_46)),((__tmp29_47) land ((lnot (__tmp30_47)))) lor (((lnot (__tmp29_47))) land (__tmp30_47)),((__tmp29_48) land ((lnot (__tmp30_48)))) lor (((lnot (__tmp29_48))) land (__tmp30_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp31_1,__tmp31_2,__tmp31_3,__tmp31_4,__tmp31_5,__tmp31_6,__tmp31_7,__tmp31_8,__tmp31_9,__tmp31_10,__tmp31_11,__tmp31_12,__tmp31_13,__tmp31_14,__tmp31_15,__tmp31_16,__tmp31_17,__tmp31_18,__tmp31_19,__tmp31_20,__tmp31_21,__tmp31_22,__tmp31_23,__tmp31_24,__tmp31_25,__tmp31_26,__tmp31_27,__tmp31_28,__tmp31_29,__tmp31_30,__tmp31_31,__tmp31_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp32_1,__tmp32_2,__tmp32_3,__tmp32_4,__tmp32_5,__tmp32_6,__tmp32_7,__tmp32_8,__tmp32_9,__tmp32_10,__tmp32_11,__tmp32_12,__tmp32_13,__tmp32_14,__tmp32_15,__tmp32_16,__tmp32_17,__tmp32_18,__tmp32_19,__tmp32_20,__tmp32_21,__tmp32_22,__tmp32_23,__tmp32_24,__tmp32_25,__tmp32_26,__tmp32_27,__tmp32_28,__tmp32_29,__tmp32_30,__tmp32_31,__tmp32_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp31_1) land ((lnot (__tmp32_1)))) lor (((lnot (__tmp31_1))) land (__tmp32_1)),((__tmp31_2) land ((lnot (__tmp32_2)))) lor (((lnot (__tmp31_2))) land (__tmp32_2)),((__tmp31_3) land ((lnot (__tmp32_3)))) lor (((lnot (__tmp31_3))) land (__tmp32_3)),((__tmp31_4) land ((lnot (__tmp32_4)))) lor (((lnot (__tmp31_4))) land (__tmp32_4)),((__tmp31_5) land ((lnot (__tmp32_5)))) lor (((lnot (__tmp31_5))) land (__tmp32_5)),((__tmp31_6) land ((lnot (__tmp32_6)))) lor (((lnot (__tmp31_6))) land (__tmp32_6)),((__tmp31_7) land ((lnot (__tmp32_7)))) lor (((lnot (__tmp31_7))) land (__tmp32_7)),((__tmp31_8) land ((lnot (__tmp32_8)))) lor (((lnot (__tmp31_8))) land (__tmp32_8)),((__tmp31_9) land ((lnot (__tmp32_9)))) lor (((lnot (__tmp31_9))) land (__tmp32_9)),((__tmp31_10) land ((lnot (__tmp32_10)))) lor (((lnot (__tmp31_10))) land (__tmp32_10)),((__tmp31_11) land ((lnot (__tmp32_11)))) lor (((lnot (__tmp31_11))) land (__tmp32_11)),((__tmp31_12) land ((lnot (__tmp32_12)))) lor (((lnot (__tmp31_12))) land (__tmp32_12)),((__tmp31_13) land ((lnot (__tmp32_13)))) lor (((lnot (__tmp31_13))) land (__tmp32_13)),((__tmp31_14) land ((lnot (__tmp32_14)))) lor (((lnot (__tmp31_14))) land (__tmp32_14)),((__tmp31_15) land ((lnot (__tmp32_15)))) lor (((lnot (__tmp31_15))) land (__tmp32_15)),((__tmp31_16) land ((lnot (__tmp32_16)))) lor (((lnot (__tmp31_16))) land (__tmp32_16)),((__tmp31_17) land ((lnot (__tmp32_17)))) lor (((lnot (__tmp31_17))) land (__tmp32_17)),((__tmp31_18) land ((lnot (__tmp32_18)))) lor (((lnot (__tmp31_18))) land (__tmp32_18)),((__tmp31_19) land ((lnot (__tmp32_19)))) lor (((lnot (__tmp31_19))) land (__tmp32_19)),((__tmp31_20) land ((lnot (__tmp32_20)))) lor (((lnot (__tmp31_20))) land (__tmp32_20)),((__tmp31_21) land ((lnot (__tmp32_21)))) lor (((lnot (__tmp31_21))) land (__tmp32_21)),((__tmp31_22) land ((lnot (__tmp32_22)))) lor (((lnot (__tmp31_22))) land (__tmp32_22)),((__tmp31_23) land ((lnot (__tmp32_23)))) lor (((lnot (__tmp31_23))) land (__tmp32_23)),((__tmp31_24) land ((lnot (__tmp32_24)))) lor (((lnot (__tmp31_24))) land (__tmp32_24)),((__tmp31_25) land ((lnot (__tmp32_25)))) lor (((lnot (__tmp31_25))) land (__tmp32_25)),((__tmp31_26) land ((lnot (__tmp32_26)))) lor (((lnot (__tmp31_26))) land (__tmp32_26)),((__tmp31_27) land ((lnot (__tmp32_27)))) lor (((lnot (__tmp31_27))) land (__tmp32_27)),((__tmp31_28) land ((lnot (__tmp32_28)))) lor (((lnot (__tmp31_28))) land (__tmp32_28)),((__tmp31_29) land ((lnot (__tmp32_29)))) lor (((lnot (__tmp31_29))) land (__tmp32_29)),((__tmp31_30) land ((lnot (__tmp32_30)))) lor (((lnot (__tmp31_30))) land (__tmp32_30)),((__tmp31_31) land ((lnot (__tmp32_31)))) lor (((lnot (__tmp31_31))) land (__tmp32_31)),((__tmp31_32) land ((lnot (__tmp32_32)))) lor (((lnot (__tmp31_32))) land (__tmp32_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single9_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp33_1,__tmp33_2,__tmp33_3,__tmp33_4,__tmp33_5,__tmp33_6,__tmp33_7,__tmp33_8,__tmp33_9,__tmp33_10,__tmp33_11,__tmp33_12,__tmp33_13,__tmp33_14,__tmp33_15,__tmp33_16,__tmp33_17,__tmp33_18,__tmp33_19,__tmp33_20,__tmp33_21,__tmp33_22,__tmp33_23,__tmp33_24,__tmp33_25,__tmp33_26,__tmp33_27,__tmp33_28,__tmp33_29,__tmp33_30,__tmp33_31,__tmp33_32,__tmp33_33,__tmp33_34,__tmp33_35,__tmp33_36,__tmp33_37,__tmp33_38,__tmp33_39,__tmp33_40,__tmp33_41,__tmp33_42,__tmp33_43,__tmp33_44,__tmp33_45,__tmp33_46,__tmp33_47,__tmp33_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp34_1,__tmp34_2,__tmp34_3,__tmp34_4,__tmp34_5,__tmp34_6,__tmp34_7,__tmp34_8,__tmp34_9,__tmp34_10,__tmp34_11,__tmp34_12,__tmp34_13,__tmp34_14,__tmp34_15,__tmp34_16,__tmp34_17,__tmp34_18,__tmp34_19,__tmp34_20,__tmp34_21,__tmp34_22,__tmp34_23,__tmp34_24,__tmp34_25,__tmp34_26,__tmp34_27,__tmp34_28,__tmp34_29,__tmp34_30,__tmp34_31,__tmp34_32,__tmp34_33,__tmp34_34,__tmp34_35,__tmp34_36,__tmp34_37,__tmp34_38,__tmp34_39,__tmp34_40,__tmp34_41,__tmp34_42,__tmp34_43,__tmp34_44,__tmp34_45,__tmp34_46,__tmp34_47,__tmp34_48) = roundkey9_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp33_1) land ((lnot (__tmp34_1)))) lor (((lnot (__tmp33_1))) land (__tmp34_1)),((__tmp33_2) land ((lnot (__tmp34_2)))) lor (((lnot (__tmp33_2))) land (__tmp34_2)),((__tmp33_3) land ((lnot (__tmp34_3)))) lor (((lnot (__tmp33_3))) land (__tmp34_3)),((__tmp33_4) land ((lnot (__tmp34_4)))) lor (((lnot (__tmp33_4))) land (__tmp34_4)),((__tmp33_5) land ((lnot (__tmp34_5)))) lor (((lnot (__tmp33_5))) land (__tmp34_5)),((__tmp33_6) land ((lnot (__tmp34_6)))) lor (((lnot (__tmp33_6))) land (__tmp34_6)),((__tmp33_7) land ((lnot (__tmp34_7)))) lor (((lnot (__tmp33_7))) land (__tmp34_7)),((__tmp33_8) land ((lnot (__tmp34_8)))) lor (((lnot (__tmp33_8))) land (__tmp34_8)),((__tmp33_9) land ((lnot (__tmp34_9)))) lor (((lnot (__tmp33_9))) land (__tmp34_9)),((__tmp33_10) land ((lnot (__tmp34_10)))) lor (((lnot (__tmp33_10))) land (__tmp34_10)),((__tmp33_11) land ((lnot (__tmp34_11)))) lor (((lnot (__tmp33_11))) land (__tmp34_11)),((__tmp33_12) land ((lnot (__tmp34_12)))) lor (((lnot (__tmp33_12))) land (__tmp34_12)),((__tmp33_13) land ((lnot (__tmp34_13)))) lor (((lnot (__tmp33_13))) land (__tmp34_13)),((__tmp33_14) land ((lnot (__tmp34_14)))) lor (((lnot (__tmp33_14))) land (__tmp34_14)),((__tmp33_15) land ((lnot (__tmp34_15)))) lor (((lnot (__tmp33_15))) land (__tmp34_15)),((__tmp33_16) land ((lnot (__tmp34_16)))) lor (((lnot (__tmp33_16))) land (__tmp34_16)),((__tmp33_17) land ((lnot (__tmp34_17)))) lor (((lnot (__tmp33_17))) land (__tmp34_17)),((__tmp33_18) land ((lnot (__tmp34_18)))) lor (((lnot (__tmp33_18))) land (__tmp34_18)),((__tmp33_19) land ((lnot (__tmp34_19)))) lor (((lnot (__tmp33_19))) land (__tmp34_19)),((__tmp33_20) land ((lnot (__tmp34_20)))) lor (((lnot (__tmp33_20))) land (__tmp34_20)),((__tmp33_21) land ((lnot (__tmp34_21)))) lor (((lnot (__tmp33_21))) land (__tmp34_21)),((__tmp33_22) land ((lnot (__tmp34_22)))) lor (((lnot (__tmp33_22))) land (__tmp34_22)),((__tmp33_23) land ((lnot (__tmp34_23)))) lor (((lnot (__tmp33_23))) land (__tmp34_23)),((__tmp33_24) land ((lnot (__tmp34_24)))) lor (((lnot (__tmp33_24))) land (__tmp34_24)),((__tmp33_25) land ((lnot (__tmp34_25)))) lor (((lnot (__tmp33_25))) land (__tmp34_25)),((__tmp33_26) land ((lnot (__tmp34_26)))) lor (((lnot (__tmp33_26))) land (__tmp34_26)),((__tmp33_27) land ((lnot (__tmp34_27)))) lor (((lnot (__tmp33_27))) land (__tmp34_27)),((__tmp33_28) land ((lnot (__tmp34_28)))) lor (((lnot (__tmp33_28))) land (__tmp34_28)),((__tmp33_29) land ((lnot (__tmp34_29)))) lor (((lnot (__tmp33_29))) land (__tmp34_29)),((__tmp33_30) land ((lnot (__tmp34_30)))) lor (((lnot (__tmp33_30))) land (__tmp34_30)),((__tmp33_31) land ((lnot (__tmp34_31)))) lor (((lnot (__tmp33_31))) land (__tmp34_31)),((__tmp33_32) land ((lnot (__tmp34_32)))) lor (((lnot (__tmp33_32))) land (__tmp34_32)),((__tmp33_33) land ((lnot (__tmp34_33)))) lor (((lnot (__tmp33_33))) land (__tmp34_33)),((__tmp33_34) land ((lnot (__tmp34_34)))) lor (((lnot (__tmp33_34))) land (__tmp34_34)),((__tmp33_35) land ((lnot (__tmp34_35)))) lor (((lnot (__tmp33_35))) land (__tmp34_35)),((__tmp33_36) land ((lnot (__tmp34_36)))) lor (((lnot (__tmp33_36))) land (__tmp34_36)),((__tmp33_37) land ((lnot (__tmp34_37)))) lor (((lnot (__tmp33_37))) land (__tmp34_37)),((__tmp33_38) land ((lnot (__tmp34_38)))) lor (((lnot (__tmp33_38))) land (__tmp34_38)),((__tmp33_39) land ((lnot (__tmp34_39)))) lor (((lnot (__tmp33_39))) land (__tmp34_39)),((__tmp33_40) land ((lnot (__tmp34_40)))) lor (((lnot (__tmp33_40))) land (__tmp34_40)),((__tmp33_41) land ((lnot (__tmp34_41)))) lor (((lnot (__tmp33_41))) land (__tmp34_41)),((__tmp33_42) land ((lnot (__tmp34_42)))) lor (((lnot (__tmp33_42))) land (__tmp34_42)),((__tmp33_43) land ((lnot (__tmp34_43)))) lor (((lnot (__tmp33_43))) land (__tmp34_43)),((__tmp33_44) land ((lnot (__tmp34_44)))) lor (((lnot (__tmp33_44))) land (__tmp34_44)),((__tmp33_45) land ((lnot (__tmp34_45)))) lor (((lnot (__tmp33_45))) land (__tmp34_45)),((__tmp33_46) land ((lnot (__tmp34_46)))) lor (((lnot (__tmp33_46))) land (__tmp34_46)),((__tmp33_47) land ((lnot (__tmp34_47)))) lor (((lnot (__tmp33_47))) land (__tmp34_47)),((__tmp33_48) land ((lnot (__tmp34_48)))) lor (((lnot (__tmp33_48))) land (__tmp34_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp35_1,__tmp35_2,__tmp35_3,__tmp35_4,__tmp35_5,__tmp35_6,__tmp35_7,__tmp35_8,__tmp35_9,__tmp35_10,__tmp35_11,__tmp35_12,__tmp35_13,__tmp35_14,__tmp35_15,__tmp35_16,__tmp35_17,__tmp35_18,__tmp35_19,__tmp35_20,__tmp35_21,__tmp35_22,__tmp35_23,__tmp35_24,__tmp35_25,__tmp35_26,__tmp35_27,__tmp35_28,__tmp35_29,__tmp35_30,__tmp35_31,__tmp35_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp36_1,__tmp36_2,__tmp36_3,__tmp36_4,__tmp36_5,__tmp36_6,__tmp36_7,__tmp36_8,__tmp36_9,__tmp36_10,__tmp36_11,__tmp36_12,__tmp36_13,__tmp36_14,__tmp36_15,__tmp36_16,__tmp36_17,__tmp36_18,__tmp36_19,__tmp36_20,__tmp36_21,__tmp36_22,__tmp36_23,__tmp36_24,__tmp36_25,__tmp36_26,__tmp36_27,__tmp36_28,__tmp36_29,__tmp36_30,__tmp36_31,__tmp36_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp35_1) land ((lnot (__tmp36_1)))) lor (((lnot (__tmp35_1))) land (__tmp36_1)),((__tmp35_2) land ((lnot (__tmp36_2)))) lor (((lnot (__tmp35_2))) land (__tmp36_2)),((__tmp35_3) land ((lnot (__tmp36_3)))) lor (((lnot (__tmp35_3))) land (__tmp36_3)),((__tmp35_4) land ((lnot (__tmp36_4)))) lor (((lnot (__tmp35_4))) land (__tmp36_4)),((__tmp35_5) land ((lnot (__tmp36_5)))) lor (((lnot (__tmp35_5))) land (__tmp36_5)),((__tmp35_6) land ((lnot (__tmp36_6)))) lor (((lnot (__tmp35_6))) land (__tmp36_6)),((__tmp35_7) land ((lnot (__tmp36_7)))) lor (((lnot (__tmp35_7))) land (__tmp36_7)),((__tmp35_8) land ((lnot (__tmp36_8)))) lor (((lnot (__tmp35_8))) land (__tmp36_8)),((__tmp35_9) land ((lnot (__tmp36_9)))) lor (((lnot (__tmp35_9))) land (__tmp36_9)),((__tmp35_10) land ((lnot (__tmp36_10)))) lor (((lnot (__tmp35_10))) land (__tmp36_10)),((__tmp35_11) land ((lnot (__tmp36_11)))) lor (((lnot (__tmp35_11))) land (__tmp36_11)),((__tmp35_12) land ((lnot (__tmp36_12)))) lor (((lnot (__tmp35_12))) land (__tmp36_12)),((__tmp35_13) land ((lnot (__tmp36_13)))) lor (((lnot (__tmp35_13))) land (__tmp36_13)),((__tmp35_14) land ((lnot (__tmp36_14)))) lor (((lnot (__tmp35_14))) land (__tmp36_14)),((__tmp35_15) land ((lnot (__tmp36_15)))) lor (((lnot (__tmp35_15))) land (__tmp36_15)),((__tmp35_16) land ((lnot (__tmp36_16)))) lor (((lnot (__tmp35_16))) land (__tmp36_16)),((__tmp35_17) land ((lnot (__tmp36_17)))) lor (((lnot (__tmp35_17))) land (__tmp36_17)),((__tmp35_18) land ((lnot (__tmp36_18)))) lor (((lnot (__tmp35_18))) land (__tmp36_18)),((__tmp35_19) land ((lnot (__tmp36_19)))) lor (((lnot (__tmp35_19))) land (__tmp36_19)),((__tmp35_20) land ((lnot (__tmp36_20)))) lor (((lnot (__tmp35_20))) land (__tmp36_20)),((__tmp35_21) land ((lnot (__tmp36_21)))) lor (((lnot (__tmp35_21))) land (__tmp36_21)),((__tmp35_22) land ((lnot (__tmp36_22)))) lor (((lnot (__tmp35_22))) land (__tmp36_22)),((__tmp35_23) land ((lnot (__tmp36_23)))) lor (((lnot (__tmp35_23))) land (__tmp36_23)),((__tmp35_24) land ((lnot (__tmp36_24)))) lor (((lnot (__tmp35_24))) land (__tmp36_24)),((__tmp35_25) land ((lnot (__tmp36_25)))) lor (((lnot (__tmp35_25))) land (__tmp36_25)),((__tmp35_26) land ((lnot (__tmp36_26)))) lor (((lnot (__tmp35_26))) land (__tmp36_26)),((__tmp35_27) land ((lnot (__tmp36_27)))) lor (((lnot (__tmp35_27))) land (__tmp36_27)),((__tmp35_28) land ((lnot (__tmp36_28)))) lor (((lnot (__tmp35_28))) land (__tmp36_28)),((__tmp35_29) land ((lnot (__tmp36_29)))) lor (((lnot (__tmp35_29))) land (__tmp36_29)),((__tmp35_30) land ((lnot (__tmp36_30)))) lor (((lnot (__tmp35_30))) land (__tmp36_30)),((__tmp35_31) land ((lnot (__tmp36_31)))) lor (((lnot (__tmp35_31))) land (__tmp36_31)),((__tmp35_32) land ((lnot (__tmp36_32)))) lor (((lnot (__tmp35_32))) land (__tmp36_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single10_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp37_1,__tmp37_2,__tmp37_3,__tmp37_4,__tmp37_5,__tmp37_6,__tmp37_7,__tmp37_8,__tmp37_9,__tmp37_10,__tmp37_11,__tmp37_12,__tmp37_13,__tmp37_14,__tmp37_15,__tmp37_16,__tmp37_17,__tmp37_18,__tmp37_19,__tmp37_20,__tmp37_21,__tmp37_22,__tmp37_23,__tmp37_24,__tmp37_25,__tmp37_26,__tmp37_27,__tmp37_28,__tmp37_29,__tmp37_30,__tmp37_31,__tmp37_32,__tmp37_33,__tmp37_34,__tmp37_35,__tmp37_36,__tmp37_37,__tmp37_38,__tmp37_39,__tmp37_40,__tmp37_41,__tmp37_42,__tmp37_43,__tmp37_44,__tmp37_45,__tmp37_46,__tmp37_47,__tmp37_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp38_1,__tmp38_2,__tmp38_3,__tmp38_4,__tmp38_5,__tmp38_6,__tmp38_7,__tmp38_8,__tmp38_9,__tmp38_10,__tmp38_11,__tmp38_12,__tmp38_13,__tmp38_14,__tmp38_15,__tmp38_16,__tmp38_17,__tmp38_18,__tmp38_19,__tmp38_20,__tmp38_21,__tmp38_22,__tmp38_23,__tmp38_24,__tmp38_25,__tmp38_26,__tmp38_27,__tmp38_28,__tmp38_29,__tmp38_30,__tmp38_31,__tmp38_32,__tmp38_33,__tmp38_34,__tmp38_35,__tmp38_36,__tmp38_37,__tmp38_38,__tmp38_39,__tmp38_40,__tmp38_41,__tmp38_42,__tmp38_43,__tmp38_44,__tmp38_45,__tmp38_46,__tmp38_47,__tmp38_48) = roundkey10_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp37_1) land ((lnot (__tmp38_1)))) lor (((lnot (__tmp37_1))) land (__tmp38_1)),((__tmp37_2) land ((lnot (__tmp38_2)))) lor (((lnot (__tmp37_2))) land (__tmp38_2)),((__tmp37_3) land ((lnot (__tmp38_3)))) lor (((lnot (__tmp37_3))) land (__tmp38_3)),((__tmp37_4) land ((lnot (__tmp38_4)))) lor (((lnot (__tmp37_4))) land (__tmp38_4)),((__tmp37_5) land ((lnot (__tmp38_5)))) lor (((lnot (__tmp37_5))) land (__tmp38_5)),((__tmp37_6) land ((lnot (__tmp38_6)))) lor (((lnot (__tmp37_6))) land (__tmp38_6)),((__tmp37_7) land ((lnot (__tmp38_7)))) lor (((lnot (__tmp37_7))) land (__tmp38_7)),((__tmp37_8) land ((lnot (__tmp38_8)))) lor (((lnot (__tmp37_8))) land (__tmp38_8)),((__tmp37_9) land ((lnot (__tmp38_9)))) lor (((lnot (__tmp37_9))) land (__tmp38_9)),((__tmp37_10) land ((lnot (__tmp38_10)))) lor (((lnot (__tmp37_10))) land (__tmp38_10)),((__tmp37_11) land ((lnot (__tmp38_11)))) lor (((lnot (__tmp37_11))) land (__tmp38_11)),((__tmp37_12) land ((lnot (__tmp38_12)))) lor (((lnot (__tmp37_12))) land (__tmp38_12)),((__tmp37_13) land ((lnot (__tmp38_13)))) lor (((lnot (__tmp37_13))) land (__tmp38_13)),((__tmp37_14) land ((lnot (__tmp38_14)))) lor (((lnot (__tmp37_14))) land (__tmp38_14)),((__tmp37_15) land ((lnot (__tmp38_15)))) lor (((lnot (__tmp37_15))) land (__tmp38_15)),((__tmp37_16) land ((lnot (__tmp38_16)))) lor (((lnot (__tmp37_16))) land (__tmp38_16)),((__tmp37_17) land ((lnot (__tmp38_17)))) lor (((lnot (__tmp37_17))) land (__tmp38_17)),((__tmp37_18) land ((lnot (__tmp38_18)))) lor (((lnot (__tmp37_18))) land (__tmp38_18)),((__tmp37_19) land ((lnot (__tmp38_19)))) lor (((lnot (__tmp37_19))) land (__tmp38_19)),((__tmp37_20) land ((lnot (__tmp38_20)))) lor (((lnot (__tmp37_20))) land (__tmp38_20)),((__tmp37_21) land ((lnot (__tmp38_21)))) lor (((lnot (__tmp37_21))) land (__tmp38_21)),((__tmp37_22) land ((lnot (__tmp38_22)))) lor (((lnot (__tmp37_22))) land (__tmp38_22)),((__tmp37_23) land ((lnot (__tmp38_23)))) lor (((lnot (__tmp37_23))) land (__tmp38_23)),((__tmp37_24) land ((lnot (__tmp38_24)))) lor (((lnot (__tmp37_24))) land (__tmp38_24)),((__tmp37_25) land ((lnot (__tmp38_25)))) lor (((lnot (__tmp37_25))) land (__tmp38_25)),((__tmp37_26) land ((lnot (__tmp38_26)))) lor (((lnot (__tmp37_26))) land (__tmp38_26)),((__tmp37_27) land ((lnot (__tmp38_27)))) lor (((lnot (__tmp37_27))) land (__tmp38_27)),((__tmp37_28) land ((lnot (__tmp38_28)))) lor (((lnot (__tmp37_28))) land (__tmp38_28)),((__tmp37_29) land ((lnot (__tmp38_29)))) lor (((lnot (__tmp37_29))) land (__tmp38_29)),((__tmp37_30) land ((lnot (__tmp38_30)))) lor (((lnot (__tmp37_30))) land (__tmp38_30)),((__tmp37_31) land ((lnot (__tmp38_31)))) lor (((lnot (__tmp37_31))) land (__tmp38_31)),((__tmp37_32) land ((lnot (__tmp38_32)))) lor (((lnot (__tmp37_32))) land (__tmp38_32)),((__tmp37_33) land ((lnot (__tmp38_33)))) lor (((lnot (__tmp37_33))) land (__tmp38_33)),((__tmp37_34) land ((lnot (__tmp38_34)))) lor (((lnot (__tmp37_34))) land (__tmp38_34)),((__tmp37_35) land ((lnot (__tmp38_35)))) lor (((lnot (__tmp37_35))) land (__tmp38_35)),((__tmp37_36) land ((lnot (__tmp38_36)))) lor (((lnot (__tmp37_36))) land (__tmp38_36)),((__tmp37_37) land ((lnot (__tmp38_37)))) lor (((lnot (__tmp37_37))) land (__tmp38_37)),((__tmp37_38) land ((lnot (__tmp38_38)))) lor (((lnot (__tmp37_38))) land (__tmp38_38)),((__tmp37_39) land ((lnot (__tmp38_39)))) lor (((lnot (__tmp37_39))) land (__tmp38_39)),((__tmp37_40) land ((lnot (__tmp38_40)))) lor (((lnot (__tmp37_40))) land (__tmp38_40)),((__tmp37_41) land ((lnot (__tmp38_41)))) lor (((lnot (__tmp37_41))) land (__tmp38_41)),((__tmp37_42) land ((lnot (__tmp38_42)))) lor (((lnot (__tmp37_42))) land (__tmp38_42)),((__tmp37_43) land ((lnot (__tmp38_43)))) lor (((lnot (__tmp37_43))) land (__tmp38_43)),((__tmp37_44) land ((lnot (__tmp38_44)))) lor (((lnot (__tmp37_44))) land (__tmp38_44)),((__tmp37_45) land ((lnot (__tmp38_45)))) lor (((lnot (__tmp37_45))) land (__tmp38_45)),((__tmp37_46) land ((lnot (__tmp38_46)))) lor (((lnot (__tmp37_46))) land (__tmp38_46)),((__tmp37_47) land ((lnot (__tmp38_47)))) lor (((lnot (__tmp37_47))) land (__tmp38_47)),((__tmp37_48) land ((lnot (__tmp38_48)))) lor (((lnot (__tmp37_48))) land (__tmp38_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp39_1,__tmp39_2,__tmp39_3,__tmp39_4,__tmp39_5,__tmp39_6,__tmp39_7,__tmp39_8,__tmp39_9,__tmp39_10,__tmp39_11,__tmp39_12,__tmp39_13,__tmp39_14,__tmp39_15,__tmp39_16,__tmp39_17,__tmp39_18,__tmp39_19,__tmp39_20,__tmp39_21,__tmp39_22,__tmp39_23,__tmp39_24,__tmp39_25,__tmp39_26,__tmp39_27,__tmp39_28,__tmp39_29,__tmp39_30,__tmp39_31,__tmp39_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp40_1,__tmp40_2,__tmp40_3,__tmp40_4,__tmp40_5,__tmp40_6,__tmp40_7,__tmp40_8,__tmp40_9,__tmp40_10,__tmp40_11,__tmp40_12,__tmp40_13,__tmp40_14,__tmp40_15,__tmp40_16,__tmp40_17,__tmp40_18,__tmp40_19,__tmp40_20,__tmp40_21,__tmp40_22,__tmp40_23,__tmp40_24,__tmp40_25,__tmp40_26,__tmp40_27,__tmp40_28,__tmp40_29,__tmp40_30,__tmp40_31,__tmp40_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp39_1) land ((lnot (__tmp40_1)))) lor (((lnot (__tmp39_1))) land (__tmp40_1)),((__tmp39_2) land ((lnot (__tmp40_2)))) lor (((lnot (__tmp39_2))) land (__tmp40_2)),((__tmp39_3) land ((lnot (__tmp40_3)))) lor (((lnot (__tmp39_3))) land (__tmp40_3)),((__tmp39_4) land ((lnot (__tmp40_4)))) lor (((lnot (__tmp39_4))) land (__tmp40_4)),((__tmp39_5) land ((lnot (__tmp40_5)))) lor (((lnot (__tmp39_5))) land (__tmp40_5)),((__tmp39_6) land ((lnot (__tmp40_6)))) lor (((lnot (__tmp39_6))) land (__tmp40_6)),((__tmp39_7) land ((lnot (__tmp40_7)))) lor (((lnot (__tmp39_7))) land (__tmp40_7)),((__tmp39_8) land ((lnot (__tmp40_8)))) lor (((lnot (__tmp39_8))) land (__tmp40_8)),((__tmp39_9) land ((lnot (__tmp40_9)))) lor (((lnot (__tmp39_9))) land (__tmp40_9)),((__tmp39_10) land ((lnot (__tmp40_10)))) lor (((lnot (__tmp39_10))) land (__tmp40_10)),((__tmp39_11) land ((lnot (__tmp40_11)))) lor (((lnot (__tmp39_11))) land (__tmp40_11)),((__tmp39_12) land ((lnot (__tmp40_12)))) lor (((lnot (__tmp39_12))) land (__tmp40_12)),((__tmp39_13) land ((lnot (__tmp40_13)))) lor (((lnot (__tmp39_13))) land (__tmp40_13)),((__tmp39_14) land ((lnot (__tmp40_14)))) lor (((lnot (__tmp39_14))) land (__tmp40_14)),((__tmp39_15) land ((lnot (__tmp40_15)))) lor (((lnot (__tmp39_15))) land (__tmp40_15)),((__tmp39_16) land ((lnot (__tmp40_16)))) lor (((lnot (__tmp39_16))) land (__tmp40_16)),((__tmp39_17) land ((lnot (__tmp40_17)))) lor (((lnot (__tmp39_17))) land (__tmp40_17)),((__tmp39_18) land ((lnot (__tmp40_18)))) lor (((lnot (__tmp39_18))) land (__tmp40_18)),((__tmp39_19) land ((lnot (__tmp40_19)))) lor (((lnot (__tmp39_19))) land (__tmp40_19)),((__tmp39_20) land ((lnot (__tmp40_20)))) lor (((lnot (__tmp39_20))) land (__tmp40_20)),((__tmp39_21) land ((lnot (__tmp40_21)))) lor (((lnot (__tmp39_21))) land (__tmp40_21)),((__tmp39_22) land ((lnot (__tmp40_22)))) lor (((lnot (__tmp39_22))) land (__tmp40_22)),((__tmp39_23) land ((lnot (__tmp40_23)))) lor (((lnot (__tmp39_23))) land (__tmp40_23)),((__tmp39_24) land ((lnot (__tmp40_24)))) lor (((lnot (__tmp39_24))) land (__tmp40_24)),((__tmp39_25) land ((lnot (__tmp40_25)))) lor (((lnot (__tmp39_25))) land (__tmp40_25)),((__tmp39_26) land ((lnot (__tmp40_26)))) lor (((lnot (__tmp39_26))) land (__tmp40_26)),((__tmp39_27) land ((lnot (__tmp40_27)))) lor (((lnot (__tmp39_27))) land (__tmp40_27)),((__tmp39_28) land ((lnot (__tmp40_28)))) lor (((lnot (__tmp39_28))) land (__tmp40_28)),((__tmp39_29) land ((lnot (__tmp40_29)))) lor (((lnot (__tmp39_29))) land (__tmp40_29)),((__tmp39_30) land ((lnot (__tmp40_30)))) lor (((lnot (__tmp39_30))) land (__tmp40_30)),((__tmp39_31) land ((lnot (__tmp40_31)))) lor (((lnot (__tmp39_31))) land (__tmp40_31)),((__tmp39_32) land ((lnot (__tmp40_32)))) lor (((lnot (__tmp39_32))) land (__tmp40_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single11_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp41_1,__tmp41_2,__tmp41_3,__tmp41_4,__tmp41_5,__tmp41_6,__tmp41_7,__tmp41_8,__tmp41_9,__tmp41_10,__tmp41_11,__tmp41_12,__tmp41_13,__tmp41_14,__tmp41_15,__tmp41_16,__tmp41_17,__tmp41_18,__tmp41_19,__tmp41_20,__tmp41_21,__tmp41_22,__tmp41_23,__tmp41_24,__tmp41_25,__tmp41_26,__tmp41_27,__tmp41_28,__tmp41_29,__tmp41_30,__tmp41_31,__tmp41_32,__tmp41_33,__tmp41_34,__tmp41_35,__tmp41_36,__tmp41_37,__tmp41_38,__tmp41_39,__tmp41_40,__tmp41_41,__tmp41_42,__tmp41_43,__tmp41_44,__tmp41_45,__tmp41_46,__tmp41_47,__tmp41_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp42_1,__tmp42_2,__tmp42_3,__tmp42_4,__tmp42_5,__tmp42_6,__tmp42_7,__tmp42_8,__tmp42_9,__tmp42_10,__tmp42_11,__tmp42_12,__tmp42_13,__tmp42_14,__tmp42_15,__tmp42_16,__tmp42_17,__tmp42_18,__tmp42_19,__tmp42_20,__tmp42_21,__tmp42_22,__tmp42_23,__tmp42_24,__tmp42_25,__tmp42_26,__tmp42_27,__tmp42_28,__tmp42_29,__tmp42_30,__tmp42_31,__tmp42_32,__tmp42_33,__tmp42_34,__tmp42_35,__tmp42_36,__tmp42_37,__tmp42_38,__tmp42_39,__tmp42_40,__tmp42_41,__tmp42_42,__tmp42_43,__tmp42_44,__tmp42_45,__tmp42_46,__tmp42_47,__tmp42_48) = roundkey11_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp41_1) land ((lnot (__tmp42_1)))) lor (((lnot (__tmp41_1))) land (__tmp42_1)),((__tmp41_2) land ((lnot (__tmp42_2)))) lor (((lnot (__tmp41_2))) land (__tmp42_2)),((__tmp41_3) land ((lnot (__tmp42_3)))) lor (((lnot (__tmp41_3))) land (__tmp42_3)),((__tmp41_4) land ((lnot (__tmp42_4)))) lor (((lnot (__tmp41_4))) land (__tmp42_4)),((__tmp41_5) land ((lnot (__tmp42_5)))) lor (((lnot (__tmp41_5))) land (__tmp42_5)),((__tmp41_6) land ((lnot (__tmp42_6)))) lor (((lnot (__tmp41_6))) land (__tmp42_6)),((__tmp41_7) land ((lnot (__tmp42_7)))) lor (((lnot (__tmp41_7))) land (__tmp42_7)),((__tmp41_8) land ((lnot (__tmp42_8)))) lor (((lnot (__tmp41_8))) land (__tmp42_8)),((__tmp41_9) land ((lnot (__tmp42_9)))) lor (((lnot (__tmp41_9))) land (__tmp42_9)),((__tmp41_10) land ((lnot (__tmp42_10)))) lor (((lnot (__tmp41_10))) land (__tmp42_10)),((__tmp41_11) land ((lnot (__tmp42_11)))) lor (((lnot (__tmp41_11))) land (__tmp42_11)),((__tmp41_12) land ((lnot (__tmp42_12)))) lor (((lnot (__tmp41_12))) land (__tmp42_12)),((__tmp41_13) land ((lnot (__tmp42_13)))) lor (((lnot (__tmp41_13))) land (__tmp42_13)),((__tmp41_14) land ((lnot (__tmp42_14)))) lor (((lnot (__tmp41_14))) land (__tmp42_14)),((__tmp41_15) land ((lnot (__tmp42_15)))) lor (((lnot (__tmp41_15))) land (__tmp42_15)),((__tmp41_16) land ((lnot (__tmp42_16)))) lor (((lnot (__tmp41_16))) land (__tmp42_16)),((__tmp41_17) land ((lnot (__tmp42_17)))) lor (((lnot (__tmp41_17))) land (__tmp42_17)),((__tmp41_18) land ((lnot (__tmp42_18)))) lor (((lnot (__tmp41_18))) land (__tmp42_18)),((__tmp41_19) land ((lnot (__tmp42_19)))) lor (((lnot (__tmp41_19))) land (__tmp42_19)),((__tmp41_20) land ((lnot (__tmp42_20)))) lor (((lnot (__tmp41_20))) land (__tmp42_20)),((__tmp41_21) land ((lnot (__tmp42_21)))) lor (((lnot (__tmp41_21))) land (__tmp42_21)),((__tmp41_22) land ((lnot (__tmp42_22)))) lor (((lnot (__tmp41_22))) land (__tmp42_22)),((__tmp41_23) land ((lnot (__tmp42_23)))) lor (((lnot (__tmp41_23))) land (__tmp42_23)),((__tmp41_24) land ((lnot (__tmp42_24)))) lor (((lnot (__tmp41_24))) land (__tmp42_24)),((__tmp41_25) land ((lnot (__tmp42_25)))) lor (((lnot (__tmp41_25))) land (__tmp42_25)),((__tmp41_26) land ((lnot (__tmp42_26)))) lor (((lnot (__tmp41_26))) land (__tmp42_26)),((__tmp41_27) land ((lnot (__tmp42_27)))) lor (((lnot (__tmp41_27))) land (__tmp42_27)),((__tmp41_28) land ((lnot (__tmp42_28)))) lor (((lnot (__tmp41_28))) land (__tmp42_28)),((__tmp41_29) land ((lnot (__tmp42_29)))) lor (((lnot (__tmp41_29))) land (__tmp42_29)),((__tmp41_30) land ((lnot (__tmp42_30)))) lor (((lnot (__tmp41_30))) land (__tmp42_30)),((__tmp41_31) land ((lnot (__tmp42_31)))) lor (((lnot (__tmp41_31))) land (__tmp42_31)),((__tmp41_32) land ((lnot (__tmp42_32)))) lor (((lnot (__tmp41_32))) land (__tmp42_32)),((__tmp41_33) land ((lnot (__tmp42_33)))) lor (((lnot (__tmp41_33))) land (__tmp42_33)),((__tmp41_34) land ((lnot (__tmp42_34)))) lor (((lnot (__tmp41_34))) land (__tmp42_34)),((__tmp41_35) land ((lnot (__tmp42_35)))) lor (((lnot (__tmp41_35))) land (__tmp42_35)),((__tmp41_36) land ((lnot (__tmp42_36)))) lor (((lnot (__tmp41_36))) land (__tmp42_36)),((__tmp41_37) land ((lnot (__tmp42_37)))) lor (((lnot (__tmp41_37))) land (__tmp42_37)),((__tmp41_38) land ((lnot (__tmp42_38)))) lor (((lnot (__tmp41_38))) land (__tmp42_38)),((__tmp41_39) land ((lnot (__tmp42_39)))) lor (((lnot (__tmp41_39))) land (__tmp42_39)),((__tmp41_40) land ((lnot (__tmp42_40)))) lor (((lnot (__tmp41_40))) land (__tmp42_40)),((__tmp41_41) land ((lnot (__tmp42_41)))) lor (((lnot (__tmp41_41))) land (__tmp42_41)),((__tmp41_42) land ((lnot (__tmp42_42)))) lor (((lnot (__tmp41_42))) land (__tmp42_42)),((__tmp41_43) land ((lnot (__tmp42_43)))) lor (((lnot (__tmp41_43))) land (__tmp42_43)),((__tmp41_44) land ((lnot (__tmp42_44)))) lor (((lnot (__tmp41_44))) land (__tmp42_44)),((__tmp41_45) land ((lnot (__tmp42_45)))) lor (((lnot (__tmp41_45))) land (__tmp42_45)),((__tmp41_46) land ((lnot (__tmp42_46)))) lor (((lnot (__tmp41_46))) land (__tmp42_46)),((__tmp41_47) land ((lnot (__tmp42_47)))) lor (((lnot (__tmp41_47))) land (__tmp42_47)),((__tmp41_48) land ((lnot (__tmp42_48)))) lor (((lnot (__tmp41_48))) land (__tmp42_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp43_1,__tmp43_2,__tmp43_3,__tmp43_4,__tmp43_5,__tmp43_6,__tmp43_7,__tmp43_8,__tmp43_9,__tmp43_10,__tmp43_11,__tmp43_12,__tmp43_13,__tmp43_14,__tmp43_15,__tmp43_16,__tmp43_17,__tmp43_18,__tmp43_19,__tmp43_20,__tmp43_21,__tmp43_22,__tmp43_23,__tmp43_24,__tmp43_25,__tmp43_26,__tmp43_27,__tmp43_28,__tmp43_29,__tmp43_30,__tmp43_31,__tmp43_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp44_1,__tmp44_2,__tmp44_3,__tmp44_4,__tmp44_5,__tmp44_6,__tmp44_7,__tmp44_8,__tmp44_9,__tmp44_10,__tmp44_11,__tmp44_12,__tmp44_13,__tmp44_14,__tmp44_15,__tmp44_16,__tmp44_17,__tmp44_18,__tmp44_19,__tmp44_20,__tmp44_21,__tmp44_22,__tmp44_23,__tmp44_24,__tmp44_25,__tmp44_26,__tmp44_27,__tmp44_28,__tmp44_29,__tmp44_30,__tmp44_31,__tmp44_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp43_1) land ((lnot (__tmp44_1)))) lor (((lnot (__tmp43_1))) land (__tmp44_1)),((__tmp43_2) land ((lnot (__tmp44_2)))) lor (((lnot (__tmp43_2))) land (__tmp44_2)),((__tmp43_3) land ((lnot (__tmp44_3)))) lor (((lnot (__tmp43_3))) land (__tmp44_3)),((__tmp43_4) land ((lnot (__tmp44_4)))) lor (((lnot (__tmp43_4))) land (__tmp44_4)),((__tmp43_5) land ((lnot (__tmp44_5)))) lor (((lnot (__tmp43_5))) land (__tmp44_5)),((__tmp43_6) land ((lnot (__tmp44_6)))) lor (((lnot (__tmp43_6))) land (__tmp44_6)),((__tmp43_7) land ((lnot (__tmp44_7)))) lor (((lnot (__tmp43_7))) land (__tmp44_7)),((__tmp43_8) land ((lnot (__tmp44_8)))) lor (((lnot (__tmp43_8))) land (__tmp44_8)),((__tmp43_9) land ((lnot (__tmp44_9)))) lor (((lnot (__tmp43_9))) land (__tmp44_9)),((__tmp43_10) land ((lnot (__tmp44_10)))) lor (((lnot (__tmp43_10))) land (__tmp44_10)),((__tmp43_11) land ((lnot (__tmp44_11)))) lor (((lnot (__tmp43_11))) land (__tmp44_11)),((__tmp43_12) land ((lnot (__tmp44_12)))) lor (((lnot (__tmp43_12))) land (__tmp44_12)),((__tmp43_13) land ((lnot (__tmp44_13)))) lor (((lnot (__tmp43_13))) land (__tmp44_13)),((__tmp43_14) land ((lnot (__tmp44_14)))) lor (((lnot (__tmp43_14))) land (__tmp44_14)),((__tmp43_15) land ((lnot (__tmp44_15)))) lor (((lnot (__tmp43_15))) land (__tmp44_15)),((__tmp43_16) land ((lnot (__tmp44_16)))) lor (((lnot (__tmp43_16))) land (__tmp44_16)),((__tmp43_17) land ((lnot (__tmp44_17)))) lor (((lnot (__tmp43_17))) land (__tmp44_17)),((__tmp43_18) land ((lnot (__tmp44_18)))) lor (((lnot (__tmp43_18))) land (__tmp44_18)),((__tmp43_19) land ((lnot (__tmp44_19)))) lor (((lnot (__tmp43_19))) land (__tmp44_19)),((__tmp43_20) land ((lnot (__tmp44_20)))) lor (((lnot (__tmp43_20))) land (__tmp44_20)),((__tmp43_21) land ((lnot (__tmp44_21)))) lor (((lnot (__tmp43_21))) land (__tmp44_21)),((__tmp43_22) land ((lnot (__tmp44_22)))) lor (((lnot (__tmp43_22))) land (__tmp44_22)),((__tmp43_23) land ((lnot (__tmp44_23)))) lor (((lnot (__tmp43_23))) land (__tmp44_23)),((__tmp43_24) land ((lnot (__tmp44_24)))) lor (((lnot (__tmp43_24))) land (__tmp44_24)),((__tmp43_25) land ((lnot (__tmp44_25)))) lor (((lnot (__tmp43_25))) land (__tmp44_25)),((__tmp43_26) land ((lnot (__tmp44_26)))) lor (((lnot (__tmp43_26))) land (__tmp44_26)),((__tmp43_27) land ((lnot (__tmp44_27)))) lor (((lnot (__tmp43_27))) land (__tmp44_27)),((__tmp43_28) land ((lnot (__tmp44_28)))) lor (((lnot (__tmp43_28))) land (__tmp44_28)),((__tmp43_29) land ((lnot (__tmp44_29)))) lor (((lnot (__tmp43_29))) land (__tmp44_29)),((__tmp43_30) land ((lnot (__tmp44_30)))) lor (((lnot (__tmp43_30))) land (__tmp44_30)),((__tmp43_31) land ((lnot (__tmp44_31)))) lor (((lnot (__tmp43_31))) land (__tmp44_31)),((__tmp43_32) land ((lnot (__tmp44_32)))) lor (((lnot (__tmp43_32))) land (__tmp44_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single12_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp45_1,__tmp45_2,__tmp45_3,__tmp45_4,__tmp45_5,__tmp45_6,__tmp45_7,__tmp45_8,__tmp45_9,__tmp45_10,__tmp45_11,__tmp45_12,__tmp45_13,__tmp45_14,__tmp45_15,__tmp45_16,__tmp45_17,__tmp45_18,__tmp45_19,__tmp45_20,__tmp45_21,__tmp45_22,__tmp45_23,__tmp45_24,__tmp45_25,__tmp45_26,__tmp45_27,__tmp45_28,__tmp45_29,__tmp45_30,__tmp45_31,__tmp45_32,__tmp45_33,__tmp45_34,__tmp45_35,__tmp45_36,__tmp45_37,__tmp45_38,__tmp45_39,__tmp45_40,__tmp45_41,__tmp45_42,__tmp45_43,__tmp45_44,__tmp45_45,__tmp45_46,__tmp45_47,__tmp45_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp46_1,__tmp46_2,__tmp46_3,__tmp46_4,__tmp46_5,__tmp46_6,__tmp46_7,__tmp46_8,__tmp46_9,__tmp46_10,__tmp46_11,__tmp46_12,__tmp46_13,__tmp46_14,__tmp46_15,__tmp46_16,__tmp46_17,__tmp46_18,__tmp46_19,__tmp46_20,__tmp46_21,__tmp46_22,__tmp46_23,__tmp46_24,__tmp46_25,__tmp46_26,__tmp46_27,__tmp46_28,__tmp46_29,__tmp46_30,__tmp46_31,__tmp46_32,__tmp46_33,__tmp46_34,__tmp46_35,__tmp46_36,__tmp46_37,__tmp46_38,__tmp46_39,__tmp46_40,__tmp46_41,__tmp46_42,__tmp46_43,__tmp46_44,__tmp46_45,__tmp46_46,__tmp46_47,__tmp46_48) = roundkey12_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp45_1) land ((lnot (__tmp46_1)))) lor (((lnot (__tmp45_1))) land (__tmp46_1)),((__tmp45_2) land ((lnot (__tmp46_2)))) lor (((lnot (__tmp45_2))) land (__tmp46_2)),((__tmp45_3) land ((lnot (__tmp46_3)))) lor (((lnot (__tmp45_3))) land (__tmp46_3)),((__tmp45_4) land ((lnot (__tmp46_4)))) lor (((lnot (__tmp45_4))) land (__tmp46_4)),((__tmp45_5) land ((lnot (__tmp46_5)))) lor (((lnot (__tmp45_5))) land (__tmp46_5)),((__tmp45_6) land ((lnot (__tmp46_6)))) lor (((lnot (__tmp45_6))) land (__tmp46_6)),((__tmp45_7) land ((lnot (__tmp46_7)))) lor (((lnot (__tmp45_7))) land (__tmp46_7)),((__tmp45_8) land ((lnot (__tmp46_8)))) lor (((lnot (__tmp45_8))) land (__tmp46_8)),((__tmp45_9) land ((lnot (__tmp46_9)))) lor (((lnot (__tmp45_9))) land (__tmp46_9)),((__tmp45_10) land ((lnot (__tmp46_10)))) lor (((lnot (__tmp45_10))) land (__tmp46_10)),((__tmp45_11) land ((lnot (__tmp46_11)))) lor (((lnot (__tmp45_11))) land (__tmp46_11)),((__tmp45_12) land ((lnot (__tmp46_12)))) lor (((lnot (__tmp45_12))) land (__tmp46_12)),((__tmp45_13) land ((lnot (__tmp46_13)))) lor (((lnot (__tmp45_13))) land (__tmp46_13)),((__tmp45_14) land ((lnot (__tmp46_14)))) lor (((lnot (__tmp45_14))) land (__tmp46_14)),((__tmp45_15) land ((lnot (__tmp46_15)))) lor (((lnot (__tmp45_15))) land (__tmp46_15)),((__tmp45_16) land ((lnot (__tmp46_16)))) lor (((lnot (__tmp45_16))) land (__tmp46_16)),((__tmp45_17) land ((lnot (__tmp46_17)))) lor (((lnot (__tmp45_17))) land (__tmp46_17)),((__tmp45_18) land ((lnot (__tmp46_18)))) lor (((lnot (__tmp45_18))) land (__tmp46_18)),((__tmp45_19) land ((lnot (__tmp46_19)))) lor (((lnot (__tmp45_19))) land (__tmp46_19)),((__tmp45_20) land ((lnot (__tmp46_20)))) lor (((lnot (__tmp45_20))) land (__tmp46_20)),((__tmp45_21) land ((lnot (__tmp46_21)))) lor (((lnot (__tmp45_21))) land (__tmp46_21)),((__tmp45_22) land ((lnot (__tmp46_22)))) lor (((lnot (__tmp45_22))) land (__tmp46_22)),((__tmp45_23) land ((lnot (__tmp46_23)))) lor (((lnot (__tmp45_23))) land (__tmp46_23)),((__tmp45_24) land ((lnot (__tmp46_24)))) lor (((lnot (__tmp45_24))) land (__tmp46_24)),((__tmp45_25) land ((lnot (__tmp46_25)))) lor (((lnot (__tmp45_25))) land (__tmp46_25)),((__tmp45_26) land ((lnot (__tmp46_26)))) lor (((lnot (__tmp45_26))) land (__tmp46_26)),((__tmp45_27) land ((lnot (__tmp46_27)))) lor (((lnot (__tmp45_27))) land (__tmp46_27)),((__tmp45_28) land ((lnot (__tmp46_28)))) lor (((lnot (__tmp45_28))) land (__tmp46_28)),((__tmp45_29) land ((lnot (__tmp46_29)))) lor (((lnot (__tmp45_29))) land (__tmp46_29)),((__tmp45_30) land ((lnot (__tmp46_30)))) lor (((lnot (__tmp45_30))) land (__tmp46_30)),((__tmp45_31) land ((lnot (__tmp46_31)))) lor (((lnot (__tmp45_31))) land (__tmp46_31)),((__tmp45_32) land ((lnot (__tmp46_32)))) lor (((lnot (__tmp45_32))) land (__tmp46_32)),((__tmp45_33) land ((lnot (__tmp46_33)))) lor (((lnot (__tmp45_33))) land (__tmp46_33)),((__tmp45_34) land ((lnot (__tmp46_34)))) lor (((lnot (__tmp45_34))) land (__tmp46_34)),((__tmp45_35) land ((lnot (__tmp46_35)))) lor (((lnot (__tmp45_35))) land (__tmp46_35)),((__tmp45_36) land ((lnot (__tmp46_36)))) lor (((lnot (__tmp45_36))) land (__tmp46_36)),((__tmp45_37) land ((lnot (__tmp46_37)))) lor (((lnot (__tmp45_37))) land (__tmp46_37)),((__tmp45_38) land ((lnot (__tmp46_38)))) lor (((lnot (__tmp45_38))) land (__tmp46_38)),((__tmp45_39) land ((lnot (__tmp46_39)))) lor (((lnot (__tmp45_39))) land (__tmp46_39)),((__tmp45_40) land ((lnot (__tmp46_40)))) lor (((lnot (__tmp45_40))) land (__tmp46_40)),((__tmp45_41) land ((lnot (__tmp46_41)))) lor (((lnot (__tmp45_41))) land (__tmp46_41)),((__tmp45_42) land ((lnot (__tmp46_42)))) lor (((lnot (__tmp45_42))) land (__tmp46_42)),((__tmp45_43) land ((lnot (__tmp46_43)))) lor (((lnot (__tmp45_43))) land (__tmp46_43)),((__tmp45_44) land ((lnot (__tmp46_44)))) lor (((lnot (__tmp45_44))) land (__tmp46_44)),((__tmp45_45) land ((lnot (__tmp46_45)))) lor (((lnot (__tmp45_45))) land (__tmp46_45)),((__tmp45_46) land ((lnot (__tmp46_46)))) lor (((lnot (__tmp45_46))) land (__tmp46_46)),((__tmp45_47) land ((lnot (__tmp46_47)))) lor (((lnot (__tmp45_47))) land (__tmp46_47)),((__tmp45_48) land ((lnot (__tmp46_48)))) lor (((lnot (__tmp45_48))) land (__tmp46_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp47_1,__tmp47_2,__tmp47_3,__tmp47_4,__tmp47_5,__tmp47_6,__tmp47_7,__tmp47_8,__tmp47_9,__tmp47_10,__tmp47_11,__tmp47_12,__tmp47_13,__tmp47_14,__tmp47_15,__tmp47_16,__tmp47_17,__tmp47_18,__tmp47_19,__tmp47_20,__tmp47_21,__tmp47_22,__tmp47_23,__tmp47_24,__tmp47_25,__tmp47_26,__tmp47_27,__tmp47_28,__tmp47_29,__tmp47_30,__tmp47_31,__tmp47_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp48_1,__tmp48_2,__tmp48_3,__tmp48_4,__tmp48_5,__tmp48_6,__tmp48_7,__tmp48_8,__tmp48_9,__tmp48_10,__tmp48_11,__tmp48_12,__tmp48_13,__tmp48_14,__tmp48_15,__tmp48_16,__tmp48_17,__tmp48_18,__tmp48_19,__tmp48_20,__tmp48_21,__tmp48_22,__tmp48_23,__tmp48_24,__tmp48_25,__tmp48_26,__tmp48_27,__tmp48_28,__tmp48_29,__tmp48_30,__tmp48_31,__tmp48_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp47_1) land ((lnot (__tmp48_1)))) lor (((lnot (__tmp47_1))) land (__tmp48_1)),((__tmp47_2) land ((lnot (__tmp48_2)))) lor (((lnot (__tmp47_2))) land (__tmp48_2)),((__tmp47_3) land ((lnot (__tmp48_3)))) lor (((lnot (__tmp47_3))) land (__tmp48_3)),((__tmp47_4) land ((lnot (__tmp48_4)))) lor (((lnot (__tmp47_4))) land (__tmp48_4)),((__tmp47_5) land ((lnot (__tmp48_5)))) lor (((lnot (__tmp47_5))) land (__tmp48_5)),((__tmp47_6) land ((lnot (__tmp48_6)))) lor (((lnot (__tmp47_6))) land (__tmp48_6)),((__tmp47_7) land ((lnot (__tmp48_7)))) lor (((lnot (__tmp47_7))) land (__tmp48_7)),((__tmp47_8) land ((lnot (__tmp48_8)))) lor (((lnot (__tmp47_8))) land (__tmp48_8)),((__tmp47_9) land ((lnot (__tmp48_9)))) lor (((lnot (__tmp47_9))) land (__tmp48_9)),((__tmp47_10) land ((lnot (__tmp48_10)))) lor (((lnot (__tmp47_10))) land (__tmp48_10)),((__tmp47_11) land ((lnot (__tmp48_11)))) lor (((lnot (__tmp47_11))) land (__tmp48_11)),((__tmp47_12) land ((lnot (__tmp48_12)))) lor (((lnot (__tmp47_12))) land (__tmp48_12)),((__tmp47_13) land ((lnot (__tmp48_13)))) lor (((lnot (__tmp47_13))) land (__tmp48_13)),((__tmp47_14) land ((lnot (__tmp48_14)))) lor (((lnot (__tmp47_14))) land (__tmp48_14)),((__tmp47_15) land ((lnot (__tmp48_15)))) lor (((lnot (__tmp47_15))) land (__tmp48_15)),((__tmp47_16) land ((lnot (__tmp48_16)))) lor (((lnot (__tmp47_16))) land (__tmp48_16)),((__tmp47_17) land ((lnot (__tmp48_17)))) lor (((lnot (__tmp47_17))) land (__tmp48_17)),((__tmp47_18) land ((lnot (__tmp48_18)))) lor (((lnot (__tmp47_18))) land (__tmp48_18)),((__tmp47_19) land ((lnot (__tmp48_19)))) lor (((lnot (__tmp47_19))) land (__tmp48_19)),((__tmp47_20) land ((lnot (__tmp48_20)))) lor (((lnot (__tmp47_20))) land (__tmp48_20)),((__tmp47_21) land ((lnot (__tmp48_21)))) lor (((lnot (__tmp47_21))) land (__tmp48_21)),((__tmp47_22) land ((lnot (__tmp48_22)))) lor (((lnot (__tmp47_22))) land (__tmp48_22)),((__tmp47_23) land ((lnot (__tmp48_23)))) lor (((lnot (__tmp47_23))) land (__tmp48_23)),((__tmp47_24) land ((lnot (__tmp48_24)))) lor (((lnot (__tmp47_24))) land (__tmp48_24)),((__tmp47_25) land ((lnot (__tmp48_25)))) lor (((lnot (__tmp47_25))) land (__tmp48_25)),((__tmp47_26) land ((lnot (__tmp48_26)))) lor (((lnot (__tmp47_26))) land (__tmp48_26)),((__tmp47_27) land ((lnot (__tmp48_27)))) lor (((lnot (__tmp47_27))) land (__tmp48_27)),((__tmp47_28) land ((lnot (__tmp48_28)))) lor (((lnot (__tmp47_28))) land (__tmp48_28)),((__tmp47_29) land ((lnot (__tmp48_29)))) lor (((lnot (__tmp47_29))) land (__tmp48_29)),((__tmp47_30) land ((lnot (__tmp48_30)))) lor (((lnot (__tmp47_30))) land (__tmp48_30)),((__tmp47_31) land ((lnot (__tmp48_31)))) lor (((lnot (__tmp47_31))) land (__tmp48_31)),((__tmp47_32) land ((lnot (__tmp48_32)))) lor (((lnot (__tmp47_32))) land (__tmp48_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single13_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp49_1,__tmp49_2,__tmp49_3,__tmp49_4,__tmp49_5,__tmp49_6,__tmp49_7,__tmp49_8,__tmp49_9,__tmp49_10,__tmp49_11,__tmp49_12,__tmp49_13,__tmp49_14,__tmp49_15,__tmp49_16,__tmp49_17,__tmp49_18,__tmp49_19,__tmp49_20,__tmp49_21,__tmp49_22,__tmp49_23,__tmp49_24,__tmp49_25,__tmp49_26,__tmp49_27,__tmp49_28,__tmp49_29,__tmp49_30,__tmp49_31,__tmp49_32,__tmp49_33,__tmp49_34,__tmp49_35,__tmp49_36,__tmp49_37,__tmp49_38,__tmp49_39,__tmp49_40,__tmp49_41,__tmp49_42,__tmp49_43,__tmp49_44,__tmp49_45,__tmp49_46,__tmp49_47,__tmp49_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp50_1,__tmp50_2,__tmp50_3,__tmp50_4,__tmp50_5,__tmp50_6,__tmp50_7,__tmp50_8,__tmp50_9,__tmp50_10,__tmp50_11,__tmp50_12,__tmp50_13,__tmp50_14,__tmp50_15,__tmp50_16,__tmp50_17,__tmp50_18,__tmp50_19,__tmp50_20,__tmp50_21,__tmp50_22,__tmp50_23,__tmp50_24,__tmp50_25,__tmp50_26,__tmp50_27,__tmp50_28,__tmp50_29,__tmp50_30,__tmp50_31,__tmp50_32,__tmp50_33,__tmp50_34,__tmp50_35,__tmp50_36,__tmp50_37,__tmp50_38,__tmp50_39,__tmp50_40,__tmp50_41,__tmp50_42,__tmp50_43,__tmp50_44,__tmp50_45,__tmp50_46,__tmp50_47,__tmp50_48) = roundkey13_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp49_1) land ((lnot (__tmp50_1)))) lor (((lnot (__tmp49_1))) land (__tmp50_1)),((__tmp49_2) land ((lnot (__tmp50_2)))) lor (((lnot (__tmp49_2))) land (__tmp50_2)),((__tmp49_3) land ((lnot (__tmp50_3)))) lor (((lnot (__tmp49_3))) land (__tmp50_3)),((__tmp49_4) land ((lnot (__tmp50_4)))) lor (((lnot (__tmp49_4))) land (__tmp50_4)),((__tmp49_5) land ((lnot (__tmp50_5)))) lor (((lnot (__tmp49_5))) land (__tmp50_5)),((__tmp49_6) land ((lnot (__tmp50_6)))) lor (((lnot (__tmp49_6))) land (__tmp50_6)),((__tmp49_7) land ((lnot (__tmp50_7)))) lor (((lnot (__tmp49_7))) land (__tmp50_7)),((__tmp49_8) land ((lnot (__tmp50_8)))) lor (((lnot (__tmp49_8))) land (__tmp50_8)),((__tmp49_9) land ((lnot (__tmp50_9)))) lor (((lnot (__tmp49_9))) land (__tmp50_9)),((__tmp49_10) land ((lnot (__tmp50_10)))) lor (((lnot (__tmp49_10))) land (__tmp50_10)),((__tmp49_11) land ((lnot (__tmp50_11)))) lor (((lnot (__tmp49_11))) land (__tmp50_11)),((__tmp49_12) land ((lnot (__tmp50_12)))) lor (((lnot (__tmp49_12))) land (__tmp50_12)),((__tmp49_13) land ((lnot (__tmp50_13)))) lor (((lnot (__tmp49_13))) land (__tmp50_13)),((__tmp49_14) land ((lnot (__tmp50_14)))) lor (((lnot (__tmp49_14))) land (__tmp50_14)),((__tmp49_15) land ((lnot (__tmp50_15)))) lor (((lnot (__tmp49_15))) land (__tmp50_15)),((__tmp49_16) land ((lnot (__tmp50_16)))) lor (((lnot (__tmp49_16))) land (__tmp50_16)),((__tmp49_17) land ((lnot (__tmp50_17)))) lor (((lnot (__tmp49_17))) land (__tmp50_17)),((__tmp49_18) land ((lnot (__tmp50_18)))) lor (((lnot (__tmp49_18))) land (__tmp50_18)),((__tmp49_19) land ((lnot (__tmp50_19)))) lor (((lnot (__tmp49_19))) land (__tmp50_19)),((__tmp49_20) land ((lnot (__tmp50_20)))) lor (((lnot (__tmp49_20))) land (__tmp50_20)),((__tmp49_21) land ((lnot (__tmp50_21)))) lor (((lnot (__tmp49_21))) land (__tmp50_21)),((__tmp49_22) land ((lnot (__tmp50_22)))) lor (((lnot (__tmp49_22))) land (__tmp50_22)),((__tmp49_23) land ((lnot (__tmp50_23)))) lor (((lnot (__tmp49_23))) land (__tmp50_23)),((__tmp49_24) land ((lnot (__tmp50_24)))) lor (((lnot (__tmp49_24))) land (__tmp50_24)),((__tmp49_25) land ((lnot (__tmp50_25)))) lor (((lnot (__tmp49_25))) land (__tmp50_25)),((__tmp49_26) land ((lnot (__tmp50_26)))) lor (((lnot (__tmp49_26))) land (__tmp50_26)),((__tmp49_27) land ((lnot (__tmp50_27)))) lor (((lnot (__tmp49_27))) land (__tmp50_27)),((__tmp49_28) land ((lnot (__tmp50_28)))) lor (((lnot (__tmp49_28))) land (__tmp50_28)),((__tmp49_29) land ((lnot (__tmp50_29)))) lor (((lnot (__tmp49_29))) land (__tmp50_29)),((__tmp49_30) land ((lnot (__tmp50_30)))) lor (((lnot (__tmp49_30))) land (__tmp50_30)),((__tmp49_31) land ((lnot (__tmp50_31)))) lor (((lnot (__tmp49_31))) land (__tmp50_31)),((__tmp49_32) land ((lnot (__tmp50_32)))) lor (((lnot (__tmp49_32))) land (__tmp50_32)),((__tmp49_33) land ((lnot (__tmp50_33)))) lor (((lnot (__tmp49_33))) land (__tmp50_33)),((__tmp49_34) land ((lnot (__tmp50_34)))) lor (((lnot (__tmp49_34))) land (__tmp50_34)),((__tmp49_35) land ((lnot (__tmp50_35)))) lor (((lnot (__tmp49_35))) land (__tmp50_35)),((__tmp49_36) land ((lnot (__tmp50_36)))) lor (((lnot (__tmp49_36))) land (__tmp50_36)),((__tmp49_37) land ((lnot (__tmp50_37)))) lor (((lnot (__tmp49_37))) land (__tmp50_37)),((__tmp49_38) land ((lnot (__tmp50_38)))) lor (((lnot (__tmp49_38))) land (__tmp50_38)),((__tmp49_39) land ((lnot (__tmp50_39)))) lor (((lnot (__tmp49_39))) land (__tmp50_39)),((__tmp49_40) land ((lnot (__tmp50_40)))) lor (((lnot (__tmp49_40))) land (__tmp50_40)),((__tmp49_41) land ((lnot (__tmp50_41)))) lor (((lnot (__tmp49_41))) land (__tmp50_41)),((__tmp49_42) land ((lnot (__tmp50_42)))) lor (((lnot (__tmp49_42))) land (__tmp50_42)),((__tmp49_43) land ((lnot (__tmp50_43)))) lor (((lnot (__tmp49_43))) land (__tmp50_43)),((__tmp49_44) land ((lnot (__tmp50_44)))) lor (((lnot (__tmp49_44))) land (__tmp50_44)),((__tmp49_45) land ((lnot (__tmp50_45)))) lor (((lnot (__tmp49_45))) land (__tmp50_45)),((__tmp49_46) land ((lnot (__tmp50_46)))) lor (((lnot (__tmp49_46))) land (__tmp50_46)),((__tmp49_47) land ((lnot (__tmp50_47)))) lor (((lnot (__tmp49_47))) land (__tmp50_47)),((__tmp49_48) land ((lnot (__tmp50_48)))) lor (((lnot (__tmp49_48))) land (__tmp50_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp51_1,__tmp51_2,__tmp51_3,__tmp51_4,__tmp51_5,__tmp51_6,__tmp51_7,__tmp51_8,__tmp51_9,__tmp51_10,__tmp51_11,__tmp51_12,__tmp51_13,__tmp51_14,__tmp51_15,__tmp51_16,__tmp51_17,__tmp51_18,__tmp51_19,__tmp51_20,__tmp51_21,__tmp51_22,__tmp51_23,__tmp51_24,__tmp51_25,__tmp51_26,__tmp51_27,__tmp51_28,__tmp51_29,__tmp51_30,__tmp51_31,__tmp51_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp52_1,__tmp52_2,__tmp52_3,__tmp52_4,__tmp52_5,__tmp52_6,__tmp52_7,__tmp52_8,__tmp52_9,__tmp52_10,__tmp52_11,__tmp52_12,__tmp52_13,__tmp52_14,__tmp52_15,__tmp52_16,__tmp52_17,__tmp52_18,__tmp52_19,__tmp52_20,__tmp52_21,__tmp52_22,__tmp52_23,__tmp52_24,__tmp52_25,__tmp52_26,__tmp52_27,__tmp52_28,__tmp52_29,__tmp52_30,__tmp52_31,__tmp52_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp51_1) land ((lnot (__tmp52_1)))) lor (((lnot (__tmp51_1))) land (__tmp52_1)),((__tmp51_2) land ((lnot (__tmp52_2)))) lor (((lnot (__tmp51_2))) land (__tmp52_2)),((__tmp51_3) land ((lnot (__tmp52_3)))) lor (((lnot (__tmp51_3))) land (__tmp52_3)),((__tmp51_4) land ((lnot (__tmp52_4)))) lor (((lnot (__tmp51_4))) land (__tmp52_4)),((__tmp51_5) land ((lnot (__tmp52_5)))) lor (((lnot (__tmp51_5))) land (__tmp52_5)),((__tmp51_6) land ((lnot (__tmp52_6)))) lor (((lnot (__tmp51_6))) land (__tmp52_6)),((__tmp51_7) land ((lnot (__tmp52_7)))) lor (((lnot (__tmp51_7))) land (__tmp52_7)),((__tmp51_8) land ((lnot (__tmp52_8)))) lor (((lnot (__tmp51_8))) land (__tmp52_8)),((__tmp51_9) land ((lnot (__tmp52_9)))) lor (((lnot (__tmp51_9))) land (__tmp52_9)),((__tmp51_10) land ((lnot (__tmp52_10)))) lor (((lnot (__tmp51_10))) land (__tmp52_10)),((__tmp51_11) land ((lnot (__tmp52_11)))) lor (((lnot (__tmp51_11))) land (__tmp52_11)),((__tmp51_12) land ((lnot (__tmp52_12)))) lor (((lnot (__tmp51_12))) land (__tmp52_12)),((__tmp51_13) land ((lnot (__tmp52_13)))) lor (((lnot (__tmp51_13))) land (__tmp52_13)),((__tmp51_14) land ((lnot (__tmp52_14)))) lor (((lnot (__tmp51_14))) land (__tmp52_14)),((__tmp51_15) land ((lnot (__tmp52_15)))) lor (((lnot (__tmp51_15))) land (__tmp52_15)),((__tmp51_16) land ((lnot (__tmp52_16)))) lor (((lnot (__tmp51_16))) land (__tmp52_16)),((__tmp51_17) land ((lnot (__tmp52_17)))) lor (((lnot (__tmp51_17))) land (__tmp52_17)),((__tmp51_18) land ((lnot (__tmp52_18)))) lor (((lnot (__tmp51_18))) land (__tmp52_18)),((__tmp51_19) land ((lnot (__tmp52_19)))) lor (((lnot (__tmp51_19))) land (__tmp52_19)),((__tmp51_20) land ((lnot (__tmp52_20)))) lor (((lnot (__tmp51_20))) land (__tmp52_20)),((__tmp51_21) land ((lnot (__tmp52_21)))) lor (((lnot (__tmp51_21))) land (__tmp52_21)),((__tmp51_22) land ((lnot (__tmp52_22)))) lor (((lnot (__tmp51_22))) land (__tmp52_22)),((__tmp51_23) land ((lnot (__tmp52_23)))) lor (((lnot (__tmp51_23))) land (__tmp52_23)),((__tmp51_24) land ((lnot (__tmp52_24)))) lor (((lnot (__tmp51_24))) land (__tmp52_24)),((__tmp51_25) land ((lnot (__tmp52_25)))) lor (((lnot (__tmp51_25))) land (__tmp52_25)),((__tmp51_26) land ((lnot (__tmp52_26)))) lor (((lnot (__tmp51_26))) land (__tmp52_26)),((__tmp51_27) land ((lnot (__tmp52_27)))) lor (((lnot (__tmp51_27))) land (__tmp52_27)),((__tmp51_28) land ((lnot (__tmp52_28)))) lor (((lnot (__tmp51_28))) land (__tmp52_28)),((__tmp51_29) land ((lnot (__tmp52_29)))) lor (((lnot (__tmp51_29))) land (__tmp52_29)),((__tmp51_30) land ((lnot (__tmp52_30)))) lor (((lnot (__tmp51_30))) land (__tmp52_30)),((__tmp51_31) land ((lnot (__tmp52_31)))) lor (((lnot (__tmp51_31))) land (__tmp52_31)),((__tmp51_32) land ((lnot (__tmp52_32)))) lor (((lnot (__tmp51_32))) land (__tmp52_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single14_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp53_1,__tmp53_2,__tmp53_3,__tmp53_4,__tmp53_5,__tmp53_6,__tmp53_7,__tmp53_8,__tmp53_9,__tmp53_10,__tmp53_11,__tmp53_12,__tmp53_13,__tmp53_14,__tmp53_15,__tmp53_16,__tmp53_17,__tmp53_18,__tmp53_19,__tmp53_20,__tmp53_21,__tmp53_22,__tmp53_23,__tmp53_24,__tmp53_25,__tmp53_26,__tmp53_27,__tmp53_28,__tmp53_29,__tmp53_30,__tmp53_31,__tmp53_32,__tmp53_33,__tmp53_34,__tmp53_35,__tmp53_36,__tmp53_37,__tmp53_38,__tmp53_39,__tmp53_40,__tmp53_41,__tmp53_42,__tmp53_43,__tmp53_44,__tmp53_45,__tmp53_46,__tmp53_47,__tmp53_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp54_1,__tmp54_2,__tmp54_3,__tmp54_4,__tmp54_5,__tmp54_6,__tmp54_7,__tmp54_8,__tmp54_9,__tmp54_10,__tmp54_11,__tmp54_12,__tmp54_13,__tmp54_14,__tmp54_15,__tmp54_16,__tmp54_17,__tmp54_18,__tmp54_19,__tmp54_20,__tmp54_21,__tmp54_22,__tmp54_23,__tmp54_24,__tmp54_25,__tmp54_26,__tmp54_27,__tmp54_28,__tmp54_29,__tmp54_30,__tmp54_31,__tmp54_32,__tmp54_33,__tmp54_34,__tmp54_35,__tmp54_36,__tmp54_37,__tmp54_38,__tmp54_39,__tmp54_40,__tmp54_41,__tmp54_42,__tmp54_43,__tmp54_44,__tmp54_45,__tmp54_46,__tmp54_47,__tmp54_48) = roundkey14_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp53_1) land ((lnot (__tmp54_1)))) lor (((lnot (__tmp53_1))) land (__tmp54_1)),((__tmp53_2) land ((lnot (__tmp54_2)))) lor (((lnot (__tmp53_2))) land (__tmp54_2)),((__tmp53_3) land ((lnot (__tmp54_3)))) lor (((lnot (__tmp53_3))) land (__tmp54_3)),((__tmp53_4) land ((lnot (__tmp54_4)))) lor (((lnot (__tmp53_4))) land (__tmp54_4)),((__tmp53_5) land ((lnot (__tmp54_5)))) lor (((lnot (__tmp53_5))) land (__tmp54_5)),((__tmp53_6) land ((lnot (__tmp54_6)))) lor (((lnot (__tmp53_6))) land (__tmp54_6)),((__tmp53_7) land ((lnot (__tmp54_7)))) lor (((lnot (__tmp53_7))) land (__tmp54_7)),((__tmp53_8) land ((lnot (__tmp54_8)))) lor (((lnot (__tmp53_8))) land (__tmp54_8)),((__tmp53_9) land ((lnot (__tmp54_9)))) lor (((lnot (__tmp53_9))) land (__tmp54_9)),((__tmp53_10) land ((lnot (__tmp54_10)))) lor (((lnot (__tmp53_10))) land (__tmp54_10)),((__tmp53_11) land ((lnot (__tmp54_11)))) lor (((lnot (__tmp53_11))) land (__tmp54_11)),((__tmp53_12) land ((lnot (__tmp54_12)))) lor (((lnot (__tmp53_12))) land (__tmp54_12)),((__tmp53_13) land ((lnot (__tmp54_13)))) lor (((lnot (__tmp53_13))) land (__tmp54_13)),((__tmp53_14) land ((lnot (__tmp54_14)))) lor (((lnot (__tmp53_14))) land (__tmp54_14)),((__tmp53_15) land ((lnot (__tmp54_15)))) lor (((lnot (__tmp53_15))) land (__tmp54_15)),((__tmp53_16) land ((lnot (__tmp54_16)))) lor (((lnot (__tmp53_16))) land (__tmp54_16)),((__tmp53_17) land ((lnot (__tmp54_17)))) lor (((lnot (__tmp53_17))) land (__tmp54_17)),((__tmp53_18) land ((lnot (__tmp54_18)))) lor (((lnot (__tmp53_18))) land (__tmp54_18)),((__tmp53_19) land ((lnot (__tmp54_19)))) lor (((lnot (__tmp53_19))) land (__tmp54_19)),((__tmp53_20) land ((lnot (__tmp54_20)))) lor (((lnot (__tmp53_20))) land (__tmp54_20)),((__tmp53_21) land ((lnot (__tmp54_21)))) lor (((lnot (__tmp53_21))) land (__tmp54_21)),((__tmp53_22) land ((lnot (__tmp54_22)))) lor (((lnot (__tmp53_22))) land (__tmp54_22)),((__tmp53_23) land ((lnot (__tmp54_23)))) lor (((lnot (__tmp53_23))) land (__tmp54_23)),((__tmp53_24) land ((lnot (__tmp54_24)))) lor (((lnot (__tmp53_24))) land (__tmp54_24)),((__tmp53_25) land ((lnot (__tmp54_25)))) lor (((lnot (__tmp53_25))) land (__tmp54_25)),((__tmp53_26) land ((lnot (__tmp54_26)))) lor (((lnot (__tmp53_26))) land (__tmp54_26)),((__tmp53_27) land ((lnot (__tmp54_27)))) lor (((lnot (__tmp53_27))) land (__tmp54_27)),((__tmp53_28) land ((lnot (__tmp54_28)))) lor (((lnot (__tmp53_28))) land (__tmp54_28)),((__tmp53_29) land ((lnot (__tmp54_29)))) lor (((lnot (__tmp53_29))) land (__tmp54_29)),((__tmp53_30) land ((lnot (__tmp54_30)))) lor (((lnot (__tmp53_30))) land (__tmp54_30)),((__tmp53_31) land ((lnot (__tmp54_31)))) lor (((lnot (__tmp53_31))) land (__tmp54_31)),((__tmp53_32) land ((lnot (__tmp54_32)))) lor (((lnot (__tmp53_32))) land (__tmp54_32)),((__tmp53_33) land ((lnot (__tmp54_33)))) lor (((lnot (__tmp53_33))) land (__tmp54_33)),((__tmp53_34) land ((lnot (__tmp54_34)))) lor (((lnot (__tmp53_34))) land (__tmp54_34)),((__tmp53_35) land ((lnot (__tmp54_35)))) lor (((lnot (__tmp53_35))) land (__tmp54_35)),((__tmp53_36) land ((lnot (__tmp54_36)))) lor (((lnot (__tmp53_36))) land (__tmp54_36)),((__tmp53_37) land ((lnot (__tmp54_37)))) lor (((lnot (__tmp53_37))) land (__tmp54_37)),((__tmp53_38) land ((lnot (__tmp54_38)))) lor (((lnot (__tmp53_38))) land (__tmp54_38)),((__tmp53_39) land ((lnot (__tmp54_39)))) lor (((lnot (__tmp53_39))) land (__tmp54_39)),((__tmp53_40) land ((lnot (__tmp54_40)))) lor (((lnot (__tmp53_40))) land (__tmp54_40)),((__tmp53_41) land ((lnot (__tmp54_41)))) lor (((lnot (__tmp53_41))) land (__tmp54_41)),((__tmp53_42) land ((lnot (__tmp54_42)))) lor (((lnot (__tmp53_42))) land (__tmp54_42)),((__tmp53_43) land ((lnot (__tmp54_43)))) lor (((lnot (__tmp53_43))) land (__tmp54_43)),((__tmp53_44) land ((lnot (__tmp54_44)))) lor (((lnot (__tmp53_44))) land (__tmp54_44)),((__tmp53_45) land ((lnot (__tmp54_45)))) lor (((lnot (__tmp53_45))) land (__tmp54_45)),((__tmp53_46) land ((lnot (__tmp54_46)))) lor (((lnot (__tmp53_46))) land (__tmp54_46)),((__tmp53_47) land ((lnot (__tmp54_47)))) lor (((lnot (__tmp53_47))) land (__tmp54_47)),((__tmp53_48) land ((lnot (__tmp54_48)))) lor (((lnot (__tmp53_48))) land (__tmp54_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp55_1,__tmp55_2,__tmp55_3,__tmp55_4,__tmp55_5,__tmp55_6,__tmp55_7,__tmp55_8,__tmp55_9,__tmp55_10,__tmp55_11,__tmp55_12,__tmp55_13,__tmp55_14,__tmp55_15,__tmp55_16,__tmp55_17,__tmp55_18,__tmp55_19,__tmp55_20,__tmp55_21,__tmp55_22,__tmp55_23,__tmp55_24,__tmp55_25,__tmp55_26,__tmp55_27,__tmp55_28,__tmp55_29,__tmp55_30,__tmp55_31,__tmp55_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp56_1,__tmp56_2,__tmp56_3,__tmp56_4,__tmp56_5,__tmp56_6,__tmp56_7,__tmp56_8,__tmp56_9,__tmp56_10,__tmp56_11,__tmp56_12,__tmp56_13,__tmp56_14,__tmp56_15,__tmp56_16,__tmp56_17,__tmp56_18,__tmp56_19,__tmp56_20,__tmp56_21,__tmp56_22,__tmp56_23,__tmp56_24,__tmp56_25,__tmp56_26,__tmp56_27,__tmp56_28,__tmp56_29,__tmp56_30,__tmp56_31,__tmp56_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp55_1) land ((lnot (__tmp56_1)))) lor (((lnot (__tmp55_1))) land (__tmp56_1)),((__tmp55_2) land ((lnot (__tmp56_2)))) lor (((lnot (__tmp55_2))) land (__tmp56_2)),((__tmp55_3) land ((lnot (__tmp56_3)))) lor (((lnot (__tmp55_3))) land (__tmp56_3)),((__tmp55_4) land ((lnot (__tmp56_4)))) lor (((lnot (__tmp55_4))) land (__tmp56_4)),((__tmp55_5) land ((lnot (__tmp56_5)))) lor (((lnot (__tmp55_5))) land (__tmp56_5)),((__tmp55_6) land ((lnot (__tmp56_6)))) lor (((lnot (__tmp55_6))) land (__tmp56_6)),((__tmp55_7) land ((lnot (__tmp56_7)))) lor (((lnot (__tmp55_7))) land (__tmp56_7)),((__tmp55_8) land ((lnot (__tmp56_8)))) lor (((lnot (__tmp55_8))) land (__tmp56_8)),((__tmp55_9) land ((lnot (__tmp56_9)))) lor (((lnot (__tmp55_9))) land (__tmp56_9)),((__tmp55_10) land ((lnot (__tmp56_10)))) lor (((lnot (__tmp55_10))) land (__tmp56_10)),((__tmp55_11) land ((lnot (__tmp56_11)))) lor (((lnot (__tmp55_11))) land (__tmp56_11)),((__tmp55_12) land ((lnot (__tmp56_12)))) lor (((lnot (__tmp55_12))) land (__tmp56_12)),((__tmp55_13) land ((lnot (__tmp56_13)))) lor (((lnot (__tmp55_13))) land (__tmp56_13)),((__tmp55_14) land ((lnot (__tmp56_14)))) lor (((lnot (__tmp55_14))) land (__tmp56_14)),((__tmp55_15) land ((lnot (__tmp56_15)))) lor (((lnot (__tmp55_15))) land (__tmp56_15)),((__tmp55_16) land ((lnot (__tmp56_16)))) lor (((lnot (__tmp55_16))) land (__tmp56_16)),((__tmp55_17) land ((lnot (__tmp56_17)))) lor (((lnot (__tmp55_17))) land (__tmp56_17)),((__tmp55_18) land ((lnot (__tmp56_18)))) lor (((lnot (__tmp55_18))) land (__tmp56_18)),((__tmp55_19) land ((lnot (__tmp56_19)))) lor (((lnot (__tmp55_19))) land (__tmp56_19)),((__tmp55_20) land ((lnot (__tmp56_20)))) lor (((lnot (__tmp55_20))) land (__tmp56_20)),((__tmp55_21) land ((lnot (__tmp56_21)))) lor (((lnot (__tmp55_21))) land (__tmp56_21)),((__tmp55_22) land ((lnot (__tmp56_22)))) lor (((lnot (__tmp55_22))) land (__tmp56_22)),((__tmp55_23) land ((lnot (__tmp56_23)))) lor (((lnot (__tmp55_23))) land (__tmp56_23)),((__tmp55_24) land ((lnot (__tmp56_24)))) lor (((lnot (__tmp55_24))) land (__tmp56_24)),((__tmp55_25) land ((lnot (__tmp56_25)))) lor (((lnot (__tmp55_25))) land (__tmp56_25)),((__tmp55_26) land ((lnot (__tmp56_26)))) lor (((lnot (__tmp55_26))) land (__tmp56_26)),((__tmp55_27) land ((lnot (__tmp56_27)))) lor (((lnot (__tmp55_27))) land (__tmp56_27)),((__tmp55_28) land ((lnot (__tmp56_28)))) lor (((lnot (__tmp55_28))) land (__tmp56_28)),((__tmp55_29) land ((lnot (__tmp56_29)))) lor (((lnot (__tmp55_29))) land (__tmp56_29)),((__tmp55_30) land ((lnot (__tmp56_30)))) lor (((lnot (__tmp55_30))) land (__tmp56_30)),((__tmp55_31) land ((lnot (__tmp56_31)))) lor (((lnot (__tmp55_31))) land (__tmp56_31)),((__tmp55_32) land ((lnot (__tmp56_32)))) lor (((lnot (__tmp55_32))) land (__tmp56_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single15_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp57_1,__tmp57_2,__tmp57_3,__tmp57_4,__tmp57_5,__tmp57_6,__tmp57_7,__tmp57_8,__tmp57_9,__tmp57_10,__tmp57_11,__tmp57_12,__tmp57_13,__tmp57_14,__tmp57_15,__tmp57_16,__tmp57_17,__tmp57_18,__tmp57_19,__tmp57_20,__tmp57_21,__tmp57_22,__tmp57_23,__tmp57_24,__tmp57_25,__tmp57_26,__tmp57_27,__tmp57_28,__tmp57_29,__tmp57_30,__tmp57_31,__tmp57_32,__tmp57_33,__tmp57_34,__tmp57_35,__tmp57_36,__tmp57_37,__tmp57_38,__tmp57_39,__tmp57_40,__tmp57_41,__tmp57_42,__tmp57_43,__tmp57_44,__tmp57_45,__tmp57_46,__tmp57_47,__tmp57_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp58_1,__tmp58_2,__tmp58_3,__tmp58_4,__tmp58_5,__tmp58_6,__tmp58_7,__tmp58_8,__tmp58_9,__tmp58_10,__tmp58_11,__tmp58_12,__tmp58_13,__tmp58_14,__tmp58_15,__tmp58_16,__tmp58_17,__tmp58_18,__tmp58_19,__tmp58_20,__tmp58_21,__tmp58_22,__tmp58_23,__tmp58_24,__tmp58_25,__tmp58_26,__tmp58_27,__tmp58_28,__tmp58_29,__tmp58_30,__tmp58_31,__tmp58_32,__tmp58_33,__tmp58_34,__tmp58_35,__tmp58_36,__tmp58_37,__tmp58_38,__tmp58_39,__tmp58_40,__tmp58_41,__tmp58_42,__tmp58_43,__tmp58_44,__tmp58_45,__tmp58_46,__tmp58_47,__tmp58_48) = roundkey15_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp57_1) land ((lnot (__tmp58_1)))) lor (((lnot (__tmp57_1))) land (__tmp58_1)),((__tmp57_2) land ((lnot (__tmp58_2)))) lor (((lnot (__tmp57_2))) land (__tmp58_2)),((__tmp57_3) land ((lnot (__tmp58_3)))) lor (((lnot (__tmp57_3))) land (__tmp58_3)),((__tmp57_4) land ((lnot (__tmp58_4)))) lor (((lnot (__tmp57_4))) land (__tmp58_4)),((__tmp57_5) land ((lnot (__tmp58_5)))) lor (((lnot (__tmp57_5))) land (__tmp58_5)),((__tmp57_6) land ((lnot (__tmp58_6)))) lor (((lnot (__tmp57_6))) land (__tmp58_6)),((__tmp57_7) land ((lnot (__tmp58_7)))) lor (((lnot (__tmp57_7))) land (__tmp58_7)),((__tmp57_8) land ((lnot (__tmp58_8)))) lor (((lnot (__tmp57_8))) land (__tmp58_8)),((__tmp57_9) land ((lnot (__tmp58_9)))) lor (((lnot (__tmp57_9))) land (__tmp58_9)),((__tmp57_10) land ((lnot (__tmp58_10)))) lor (((lnot (__tmp57_10))) land (__tmp58_10)),((__tmp57_11) land ((lnot (__tmp58_11)))) lor (((lnot (__tmp57_11))) land (__tmp58_11)),((__tmp57_12) land ((lnot (__tmp58_12)))) lor (((lnot (__tmp57_12))) land (__tmp58_12)),((__tmp57_13) land ((lnot (__tmp58_13)))) lor (((lnot (__tmp57_13))) land (__tmp58_13)),((__tmp57_14) land ((lnot (__tmp58_14)))) lor (((lnot (__tmp57_14))) land (__tmp58_14)),((__tmp57_15) land ((lnot (__tmp58_15)))) lor (((lnot (__tmp57_15))) land (__tmp58_15)),((__tmp57_16) land ((lnot (__tmp58_16)))) lor (((lnot (__tmp57_16))) land (__tmp58_16)),((__tmp57_17) land ((lnot (__tmp58_17)))) lor (((lnot (__tmp57_17))) land (__tmp58_17)),((__tmp57_18) land ((lnot (__tmp58_18)))) lor (((lnot (__tmp57_18))) land (__tmp58_18)),((__tmp57_19) land ((lnot (__tmp58_19)))) lor (((lnot (__tmp57_19))) land (__tmp58_19)),((__tmp57_20) land ((lnot (__tmp58_20)))) lor (((lnot (__tmp57_20))) land (__tmp58_20)),((__tmp57_21) land ((lnot (__tmp58_21)))) lor (((lnot (__tmp57_21))) land (__tmp58_21)),((__tmp57_22) land ((lnot (__tmp58_22)))) lor (((lnot (__tmp57_22))) land (__tmp58_22)),((__tmp57_23) land ((lnot (__tmp58_23)))) lor (((lnot (__tmp57_23))) land (__tmp58_23)),((__tmp57_24) land ((lnot (__tmp58_24)))) lor (((lnot (__tmp57_24))) land (__tmp58_24)),((__tmp57_25) land ((lnot (__tmp58_25)))) lor (((lnot (__tmp57_25))) land (__tmp58_25)),((__tmp57_26) land ((lnot (__tmp58_26)))) lor (((lnot (__tmp57_26))) land (__tmp58_26)),((__tmp57_27) land ((lnot (__tmp58_27)))) lor (((lnot (__tmp57_27))) land (__tmp58_27)),((__tmp57_28) land ((lnot (__tmp58_28)))) lor (((lnot (__tmp57_28))) land (__tmp58_28)),((__tmp57_29) land ((lnot (__tmp58_29)))) lor (((lnot (__tmp57_29))) land (__tmp58_29)),((__tmp57_30) land ((lnot (__tmp58_30)))) lor (((lnot (__tmp57_30))) land (__tmp58_30)),((__tmp57_31) land ((lnot (__tmp58_31)))) lor (((lnot (__tmp57_31))) land (__tmp58_31)),((__tmp57_32) land ((lnot (__tmp58_32)))) lor (((lnot (__tmp57_32))) land (__tmp58_32)),((__tmp57_33) land ((lnot (__tmp58_33)))) lor (((lnot (__tmp57_33))) land (__tmp58_33)),((__tmp57_34) land ((lnot (__tmp58_34)))) lor (((lnot (__tmp57_34))) land (__tmp58_34)),((__tmp57_35) land ((lnot (__tmp58_35)))) lor (((lnot (__tmp57_35))) land (__tmp58_35)),((__tmp57_36) land ((lnot (__tmp58_36)))) lor (((lnot (__tmp57_36))) land (__tmp58_36)),((__tmp57_37) land ((lnot (__tmp58_37)))) lor (((lnot (__tmp57_37))) land (__tmp58_37)),((__tmp57_38) land ((lnot (__tmp58_38)))) lor (((lnot (__tmp57_38))) land (__tmp58_38)),((__tmp57_39) land ((lnot (__tmp58_39)))) lor (((lnot (__tmp57_39))) land (__tmp58_39)),((__tmp57_40) land ((lnot (__tmp58_40)))) lor (((lnot (__tmp57_40))) land (__tmp58_40)),((__tmp57_41) land ((lnot (__tmp58_41)))) lor (((lnot (__tmp57_41))) land (__tmp58_41)),((__tmp57_42) land ((lnot (__tmp58_42)))) lor (((lnot (__tmp57_42))) land (__tmp58_42)),((__tmp57_43) land ((lnot (__tmp58_43)))) lor (((lnot (__tmp57_43))) land (__tmp58_43)),((__tmp57_44) land ((lnot (__tmp58_44)))) lor (((lnot (__tmp57_44))) land (__tmp58_44)),((__tmp57_45) land ((lnot (__tmp58_45)))) lor (((lnot (__tmp57_45))) land (__tmp58_45)),((__tmp57_46) land ((lnot (__tmp58_46)))) lor (((lnot (__tmp57_46))) land (__tmp58_46)),((__tmp57_47) land ((lnot (__tmp58_47)))) lor (((lnot (__tmp57_47))) land (__tmp58_47)),((__tmp57_48) land ((lnot (__tmp58_48)))) lor (((lnot (__tmp57_48))) land (__tmp58_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp59_1,__tmp59_2,__tmp59_3,__tmp59_4,__tmp59_5,__tmp59_6,__tmp59_7,__tmp59_8,__tmp59_9,__tmp59_10,__tmp59_11,__tmp59_12,__tmp59_13,__tmp59_14,__tmp59_15,__tmp59_16,__tmp59_17,__tmp59_18,__tmp59_19,__tmp59_20,__tmp59_21,__tmp59_22,__tmp59_23,__tmp59_24,__tmp59_25,__tmp59_26,__tmp59_27,__tmp59_28,__tmp59_29,__tmp59_30,__tmp59_31,__tmp59_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp60_1,__tmp60_2,__tmp60_3,__tmp60_4,__tmp60_5,__tmp60_6,__tmp60_7,__tmp60_8,__tmp60_9,__tmp60_10,__tmp60_11,__tmp60_12,__tmp60_13,__tmp60_14,__tmp60_15,__tmp60_16,__tmp60_17,__tmp60_18,__tmp60_19,__tmp60_20,__tmp60_21,__tmp60_22,__tmp60_23,__tmp60_24,__tmp60_25,__tmp60_26,__tmp60_27,__tmp60_28,__tmp60_29,__tmp60_30,__tmp60_31,__tmp60_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp59_1) land ((lnot (__tmp60_1)))) lor (((lnot (__tmp59_1))) land (__tmp60_1)),((__tmp59_2) land ((lnot (__tmp60_2)))) lor (((lnot (__tmp59_2))) land (__tmp60_2)),((__tmp59_3) land ((lnot (__tmp60_3)))) lor (((lnot (__tmp59_3))) land (__tmp60_3)),((__tmp59_4) land ((lnot (__tmp60_4)))) lor (((lnot (__tmp59_4))) land (__tmp60_4)),((__tmp59_5) land ((lnot (__tmp60_5)))) lor (((lnot (__tmp59_5))) land (__tmp60_5)),((__tmp59_6) land ((lnot (__tmp60_6)))) lor (((lnot (__tmp59_6))) land (__tmp60_6)),((__tmp59_7) land ((lnot (__tmp60_7)))) lor (((lnot (__tmp59_7))) land (__tmp60_7)),((__tmp59_8) land ((lnot (__tmp60_8)))) lor (((lnot (__tmp59_8))) land (__tmp60_8)),((__tmp59_9) land ((lnot (__tmp60_9)))) lor (((lnot (__tmp59_9))) land (__tmp60_9)),((__tmp59_10) land ((lnot (__tmp60_10)))) lor (((lnot (__tmp59_10))) land (__tmp60_10)),((__tmp59_11) land ((lnot (__tmp60_11)))) lor (((lnot (__tmp59_11))) land (__tmp60_11)),((__tmp59_12) land ((lnot (__tmp60_12)))) lor (((lnot (__tmp59_12))) land (__tmp60_12)),((__tmp59_13) land ((lnot (__tmp60_13)))) lor (((lnot (__tmp59_13))) land (__tmp60_13)),((__tmp59_14) land ((lnot (__tmp60_14)))) lor (((lnot (__tmp59_14))) land (__tmp60_14)),((__tmp59_15) land ((lnot (__tmp60_15)))) lor (((lnot (__tmp59_15))) land (__tmp60_15)),((__tmp59_16) land ((lnot (__tmp60_16)))) lor (((lnot (__tmp59_16))) land (__tmp60_16)),((__tmp59_17) land ((lnot (__tmp60_17)))) lor (((lnot (__tmp59_17))) land (__tmp60_17)),((__tmp59_18) land ((lnot (__tmp60_18)))) lor (((lnot (__tmp59_18))) land (__tmp60_18)),((__tmp59_19) land ((lnot (__tmp60_19)))) lor (((lnot (__tmp59_19))) land (__tmp60_19)),((__tmp59_20) land ((lnot (__tmp60_20)))) lor (((lnot (__tmp59_20))) land (__tmp60_20)),((__tmp59_21) land ((lnot (__tmp60_21)))) lor (((lnot (__tmp59_21))) land (__tmp60_21)),((__tmp59_22) land ((lnot (__tmp60_22)))) lor (((lnot (__tmp59_22))) land (__tmp60_22)),((__tmp59_23) land ((lnot (__tmp60_23)))) lor (((lnot (__tmp59_23))) land (__tmp60_23)),((__tmp59_24) land ((lnot (__tmp60_24)))) lor (((lnot (__tmp59_24))) land (__tmp60_24)),((__tmp59_25) land ((lnot (__tmp60_25)))) lor (((lnot (__tmp59_25))) land (__tmp60_25)),((__tmp59_26) land ((lnot (__tmp60_26)))) lor (((lnot (__tmp59_26))) land (__tmp60_26)),((__tmp59_27) land ((lnot (__tmp60_27)))) lor (((lnot (__tmp59_27))) land (__tmp60_27)),((__tmp59_28) land ((lnot (__tmp60_28)))) lor (((lnot (__tmp59_28))) land (__tmp60_28)),((__tmp59_29) land ((lnot (__tmp60_29)))) lor (((lnot (__tmp59_29))) land (__tmp60_29)),((__tmp59_30) land ((lnot (__tmp60_30)))) lor (((lnot (__tmp59_30))) land (__tmp60_30)),((__tmp59_31) land ((lnot (__tmp60_31)))) lor (((lnot (__tmp59_31))) land (__tmp60_31)),((__tmp59_32) land ((lnot (__tmp60_32)))) lor (((lnot (__tmp59_32))) land (__tmp60_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_single16_ ((left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32),(right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (__tmp61_1,__tmp61_2,__tmp61_3,__tmp61_4,__tmp61_5,__tmp61_6,__tmp61_7,__tmp61_8,__tmp61_9,__tmp61_10,__tmp61_11,__tmp61_12,__tmp61_13,__tmp61_14,__tmp61_15,__tmp61_16,__tmp61_17,__tmp61_18,__tmp61_19,__tmp61_20,__tmp61_21,__tmp61_22,__tmp61_23,__tmp61_24,__tmp61_25,__tmp61_26,__tmp61_27,__tmp61_28,__tmp61_29,__tmp61_30,__tmp61_31,__tmp61_32,__tmp61_33,__tmp61_34,__tmp61_35,__tmp61_36,__tmp61_37,__tmp61_38,__tmp61_39,__tmp61_40,__tmp61_41,__tmp61_42,__tmp61_43,__tmp61_44,__tmp61_45,__tmp61_46,__tmp61_47,__tmp61_48) = expand_ (id ((right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32))) in 
    let (__tmp62_1,__tmp62_2,__tmp62_3,__tmp62_4,__tmp62_5,__tmp62_6,__tmp62_7,__tmp62_8,__tmp62_9,__tmp62_10,__tmp62_11,__tmp62_12,__tmp62_13,__tmp62_14,__tmp62_15,__tmp62_16,__tmp62_17,__tmp62_18,__tmp62_19,__tmp62_20,__tmp62_21,__tmp62_22,__tmp62_23,__tmp62_24,__tmp62_25,__tmp62_26,__tmp62_27,__tmp62_28,__tmp62_29,__tmp62_30,__tmp62_31,__tmp62_32,__tmp62_33,__tmp62_34,__tmp62_35,__tmp62_36,__tmp62_37,__tmp62_38,__tmp62_39,__tmp62_40,__tmp62_41,__tmp62_42,__tmp62_43,__tmp62_44,__tmp62_45,__tmp62_46,__tmp62_47,__tmp62_48) = roundkey16_ (id ((key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64))) in 
    let (s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s6_1,s6_2,s6_3,s6_4,s6_5,s6_6,s7_1,s7_2,s7_3,s7_4,s7_5,s7_6,s8_1,s8_2,s8_3,s8_4,s8_5,s8_6) = (((__tmp61_1) land ((lnot (__tmp62_1)))) lor (((lnot (__tmp61_1))) land (__tmp62_1)),((__tmp61_2) land ((lnot (__tmp62_2)))) lor (((lnot (__tmp61_2))) land (__tmp62_2)),((__tmp61_3) land ((lnot (__tmp62_3)))) lor (((lnot (__tmp61_3))) land (__tmp62_3)),((__tmp61_4) land ((lnot (__tmp62_4)))) lor (((lnot (__tmp61_4))) land (__tmp62_4)),((__tmp61_5) land ((lnot (__tmp62_5)))) lor (((lnot (__tmp61_5))) land (__tmp62_5)),((__tmp61_6) land ((lnot (__tmp62_6)))) lor (((lnot (__tmp61_6))) land (__tmp62_6)),((__tmp61_7) land ((lnot (__tmp62_7)))) lor (((lnot (__tmp61_7))) land (__tmp62_7)),((__tmp61_8) land ((lnot (__tmp62_8)))) lor (((lnot (__tmp61_8))) land (__tmp62_8)),((__tmp61_9) land ((lnot (__tmp62_9)))) lor (((lnot (__tmp61_9))) land (__tmp62_9)),((__tmp61_10) land ((lnot (__tmp62_10)))) lor (((lnot (__tmp61_10))) land (__tmp62_10)),((__tmp61_11) land ((lnot (__tmp62_11)))) lor (((lnot (__tmp61_11))) land (__tmp62_11)),((__tmp61_12) land ((lnot (__tmp62_12)))) lor (((lnot (__tmp61_12))) land (__tmp62_12)),((__tmp61_13) land ((lnot (__tmp62_13)))) lor (((lnot (__tmp61_13))) land (__tmp62_13)),((__tmp61_14) land ((lnot (__tmp62_14)))) lor (((lnot (__tmp61_14))) land (__tmp62_14)),((__tmp61_15) land ((lnot (__tmp62_15)))) lor (((lnot (__tmp61_15))) land (__tmp62_15)),((__tmp61_16) land ((lnot (__tmp62_16)))) lor (((lnot (__tmp61_16))) land (__tmp62_16)),((__tmp61_17) land ((lnot (__tmp62_17)))) lor (((lnot (__tmp61_17))) land (__tmp62_17)),((__tmp61_18) land ((lnot (__tmp62_18)))) lor (((lnot (__tmp61_18))) land (__tmp62_18)),((__tmp61_19) land ((lnot (__tmp62_19)))) lor (((lnot (__tmp61_19))) land (__tmp62_19)),((__tmp61_20) land ((lnot (__tmp62_20)))) lor (((lnot (__tmp61_20))) land (__tmp62_20)),((__tmp61_21) land ((lnot (__tmp62_21)))) lor (((lnot (__tmp61_21))) land (__tmp62_21)),((__tmp61_22) land ((lnot (__tmp62_22)))) lor (((lnot (__tmp61_22))) land (__tmp62_22)),((__tmp61_23) land ((lnot (__tmp62_23)))) lor (((lnot (__tmp61_23))) land (__tmp62_23)),((__tmp61_24) land ((lnot (__tmp62_24)))) lor (((lnot (__tmp61_24))) land (__tmp62_24)),((__tmp61_25) land ((lnot (__tmp62_25)))) lor (((lnot (__tmp61_25))) land (__tmp62_25)),((__tmp61_26) land ((lnot (__tmp62_26)))) lor (((lnot (__tmp61_26))) land (__tmp62_26)),((__tmp61_27) land ((lnot (__tmp62_27)))) lor (((lnot (__tmp61_27))) land (__tmp62_27)),((__tmp61_28) land ((lnot (__tmp62_28)))) lor (((lnot (__tmp61_28))) land (__tmp62_28)),((__tmp61_29) land ((lnot (__tmp62_29)))) lor (((lnot (__tmp61_29))) land (__tmp62_29)),((__tmp61_30) land ((lnot (__tmp62_30)))) lor (((lnot (__tmp61_30))) land (__tmp62_30)),((__tmp61_31) land ((lnot (__tmp62_31)))) lor (((lnot (__tmp61_31))) land (__tmp62_31)),((__tmp61_32) land ((lnot (__tmp62_32)))) lor (((lnot (__tmp61_32))) land (__tmp62_32)),((__tmp61_33) land ((lnot (__tmp62_33)))) lor (((lnot (__tmp61_33))) land (__tmp62_33)),((__tmp61_34) land ((lnot (__tmp62_34)))) lor (((lnot (__tmp61_34))) land (__tmp62_34)),((__tmp61_35) land ((lnot (__tmp62_35)))) lor (((lnot (__tmp61_35))) land (__tmp62_35)),((__tmp61_36) land ((lnot (__tmp62_36)))) lor (((lnot (__tmp61_36))) land (__tmp62_36)),((__tmp61_37) land ((lnot (__tmp62_37)))) lor (((lnot (__tmp61_37))) land (__tmp62_37)),((__tmp61_38) land ((lnot (__tmp62_38)))) lor (((lnot (__tmp61_38))) land (__tmp62_38)),((__tmp61_39) land ((lnot (__tmp62_39)))) lor (((lnot (__tmp61_39))) land (__tmp62_39)),((__tmp61_40) land ((lnot (__tmp62_40)))) lor (((lnot (__tmp61_40))) land (__tmp62_40)),((__tmp61_41) land ((lnot (__tmp62_41)))) lor (((lnot (__tmp61_41))) land (__tmp62_41)),((__tmp61_42) land ((lnot (__tmp62_42)))) lor (((lnot (__tmp61_42))) land (__tmp62_42)),((__tmp61_43) land ((lnot (__tmp62_43)))) lor (((lnot (__tmp61_43))) land (__tmp62_43)),((__tmp61_44) land ((lnot (__tmp62_44)))) lor (((lnot (__tmp61_44))) land (__tmp62_44)),((__tmp61_45) land ((lnot (__tmp62_45)))) lor (((lnot (__tmp61_45))) land (__tmp62_45)),((__tmp61_46) land ((lnot (__tmp62_46)))) lor (((lnot (__tmp61_46))) land (__tmp62_46)),((__tmp61_47) land ((lnot (__tmp62_47)))) lor (((lnot (__tmp61_47))) land (__tmp62_47)),((__tmp61_48) land ((lnot (__tmp62_48)))) lor (((lnot (__tmp61_48))) land (__tmp62_48))) in 
    let (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) = permut_ (convert6 (sbox_1_ (convert5 ((s1_1,s1_2,s1_3,s1_4,s1_5,s1_6))),sbox_2_ (convert5 ((s2_1,s2_2,s2_3,s2_4,s2_5,s2_6))),sbox_3_ (convert5 ((s3_1,s3_2,s3_3,s3_4,s3_5,s3_6))),sbox_4_ (convert5 ((s4_1,s4_2,s4_3,s4_4,s4_5,s4_6))),sbox_5_ (convert5 ((s5_1,s5_2,s5_3,s5_4,s5_5,s5_6))),sbox_6_ (convert5 ((s6_1,s6_2,s6_3,s6_4,s6_5,s6_6))),sbox_7_ (convert5 ((s7_1,s7_2,s7_3,s7_4,s7_5,s7_6))),sbox_8_ (convert5 ((s8_1,s8_2,s8_3,s8_4,s8_5,s8_6))))) in 
    let (__tmp63_1,__tmp63_2,__tmp63_3,__tmp63_4,__tmp63_5,__tmp63_6,__tmp63_7,__tmp63_8,__tmp63_9,__tmp63_10,__tmp63_11,__tmp63_12,__tmp63_13,__tmp63_14,__tmp63_15,__tmp63_16,__tmp63_17,__tmp63_18,__tmp63_19,__tmp63_20,__tmp63_21,__tmp63_22,__tmp63_23,__tmp63_24,__tmp63_25,__tmp63_26,__tmp63_27,__tmp63_28,__tmp63_29,__tmp63_30,__tmp63_31,__tmp63_32) = (left_in_1,left_in_2,left_in_3,left_in_4,left_in_5,left_in_6,left_in_7,left_in_8,left_in_9,left_in_10,left_in_11,left_in_12,left_in_13,left_in_14,left_in_15,left_in_16,left_in_17,left_in_18,left_in_19,left_in_20,left_in_21,left_in_22,left_in_23,left_in_24,left_in_25,left_in_26,left_in_27,left_in_28,left_in_29,left_in_30,left_in_31,left_in_32) in 
    let (__tmp64_1,__tmp64_2,__tmp64_3,__tmp64_4,__tmp64_5,__tmp64_6,__tmp64_7,__tmp64_8,__tmp64_9,__tmp64_10,__tmp64_11,__tmp64_12,__tmp64_13,__tmp64_14,__tmp64_15,__tmp64_16,__tmp64_17,__tmp64_18,__tmp64_19,__tmp64_20,__tmp64_21,__tmp64_22,__tmp64_23,__tmp64_24,__tmp64_25,__tmp64_26,__tmp64_27,__tmp64_28,__tmp64_29,__tmp64_30,__tmp64_31,__tmp64_32) = (c_1,c_2,c_3,c_4,c_5,c_6,c_7,c_8,c_9,c_10,c_11,c_12,c_13,c_14,c_15,c_16,c_17,c_18,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_32) in 
    let (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32) = (right_in_1,right_in_2,right_in_3,right_in_4,right_in_5,right_in_6,right_in_7,right_in_8,right_in_9,right_in_10,right_in_11,right_in_12,right_in_13,right_in_14,right_in_15,right_in_16,right_in_17,right_in_18,right_in_19,right_in_20,right_in_21,right_in_22,right_in_23,right_in_24,right_in_25,right_in_26,right_in_27,right_in_28,right_in_29,right_in_30,right_in_31,right_in_32,((__tmp63_1) land ((lnot (__tmp64_1)))) lor (((lnot (__tmp63_1))) land (__tmp64_1)),((__tmp63_2) land ((lnot (__tmp64_2)))) lor (((lnot (__tmp63_2))) land (__tmp64_2)),((__tmp63_3) land ((lnot (__tmp64_3)))) lor (((lnot (__tmp63_3))) land (__tmp64_3)),((__tmp63_4) land ((lnot (__tmp64_4)))) lor (((lnot (__tmp63_4))) land (__tmp64_4)),((__tmp63_5) land ((lnot (__tmp64_5)))) lor (((lnot (__tmp63_5))) land (__tmp64_5)),((__tmp63_6) land ((lnot (__tmp64_6)))) lor (((lnot (__tmp63_6))) land (__tmp64_6)),((__tmp63_7) land ((lnot (__tmp64_7)))) lor (((lnot (__tmp63_7))) land (__tmp64_7)),((__tmp63_8) land ((lnot (__tmp64_8)))) lor (((lnot (__tmp63_8))) land (__tmp64_8)),((__tmp63_9) land ((lnot (__tmp64_9)))) lor (((lnot (__tmp63_9))) land (__tmp64_9)),((__tmp63_10) land ((lnot (__tmp64_10)))) lor (((lnot (__tmp63_10))) land (__tmp64_10)),((__tmp63_11) land ((lnot (__tmp64_11)))) lor (((lnot (__tmp63_11))) land (__tmp64_11)),((__tmp63_12) land ((lnot (__tmp64_12)))) lor (((lnot (__tmp63_12))) land (__tmp64_12)),((__tmp63_13) land ((lnot (__tmp64_13)))) lor (((lnot (__tmp63_13))) land (__tmp64_13)),((__tmp63_14) land ((lnot (__tmp64_14)))) lor (((lnot (__tmp63_14))) land (__tmp64_14)),((__tmp63_15) land ((lnot (__tmp64_15)))) lor (((lnot (__tmp63_15))) land (__tmp64_15)),((__tmp63_16) land ((lnot (__tmp64_16)))) lor (((lnot (__tmp63_16))) land (__tmp64_16)),((__tmp63_17) land ((lnot (__tmp64_17)))) lor (((lnot (__tmp63_17))) land (__tmp64_17)),((__tmp63_18) land ((lnot (__tmp64_18)))) lor (((lnot (__tmp63_18))) land (__tmp64_18)),((__tmp63_19) land ((lnot (__tmp64_19)))) lor (((lnot (__tmp63_19))) land (__tmp64_19)),((__tmp63_20) land ((lnot (__tmp64_20)))) lor (((lnot (__tmp63_20))) land (__tmp64_20)),((__tmp63_21) land ((lnot (__tmp64_21)))) lor (((lnot (__tmp63_21))) land (__tmp64_21)),((__tmp63_22) land ((lnot (__tmp64_22)))) lor (((lnot (__tmp63_22))) land (__tmp64_22)),((__tmp63_23) land ((lnot (__tmp64_23)))) lor (((lnot (__tmp63_23))) land (__tmp64_23)),((__tmp63_24) land ((lnot (__tmp64_24)))) lor (((lnot (__tmp63_24))) land (__tmp64_24)),((__tmp63_25) land ((lnot (__tmp64_25)))) lor (((lnot (__tmp63_25))) land (__tmp64_25)),((__tmp63_26) land ((lnot (__tmp64_26)))) lor (((lnot (__tmp63_26))) land (__tmp64_26)),((__tmp63_27) land ((lnot (__tmp64_27)))) lor (((lnot (__tmp63_27))) land (__tmp64_27)),((__tmp63_28) land ((lnot (__tmp64_28)))) lor (((lnot (__tmp63_28))) land (__tmp64_28)),((__tmp63_29) land ((lnot (__tmp64_29)))) lor (((lnot (__tmp63_29))) land (__tmp64_29)),((__tmp63_30) land ((lnot (__tmp64_30)))) lor (((lnot (__tmp63_30))) land (__tmp64_30)),((__tmp63_31) land ((lnot (__tmp64_31)))) lor (((lnot (__tmp63_31))) land (__tmp64_31)),((__tmp63_32) land ((lnot (__tmp64_32)))) lor (((lnot (__tmp63_32))) land (__tmp64_32))) in 
    (left_out_1,left_out_2,left_out_3,left_out_4,left_out_5,left_out_6,left_out_7,left_out_8,left_out_9,left_out_10,left_out_11,left_out_12,left_out_13,left_out_14,left_out_15,left_out_16,left_out_17,left_out_18,left_out_19,left_out_20,left_out_21,left_out_22,left_out_23,left_out_24,left_out_25,left_out_26,left_out_27,left_out_28,left_out_29,left_out_30,left_out_31,left_out_32,right_out_1,right_out_2,right_out_3,right_out_4,right_out_5,right_out_6,right_out_7,right_out_8,right_out_9,right_out_10,right_out_11,right_out_12,right_out_13,right_out_14,right_out_15,right_out_16,right_out_17,right_out_18,right_out_19,right_out_20,right_out_21,right_out_22,right_out_23,right_out_24,right_out_25,right_out_26,right_out_27,right_out_28,right_out_29,right_out_30,right_out_31,right_out_32,key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)



let des_ ((plaintext_1,plaintext_2,plaintext_3,plaintext_4,plaintext_5,plaintext_6,plaintext_7,plaintext_8,plaintext_9,plaintext_10,plaintext_11,plaintext_12,plaintext_13,plaintext_14,plaintext_15,plaintext_16,plaintext_17,plaintext_18,plaintext_19,plaintext_20,plaintext_21,plaintext_22,plaintext_23,plaintext_24,plaintext_25,plaintext_26,plaintext_27,plaintext_28,plaintext_29,plaintext_30,plaintext_31,plaintext_32,plaintext_33,plaintext_34,plaintext_35,plaintext_36,plaintext_37,plaintext_38,plaintext_39,plaintext_40,plaintext_41,plaintext_42,plaintext_43,plaintext_44,plaintext_45,plaintext_46,plaintext_47,plaintext_48,plaintext_49,plaintext_50,plaintext_51,plaintext_52,plaintext_53,plaintext_54,plaintext_55,plaintext_56,plaintext_57,plaintext_58,plaintext_59,plaintext_60,plaintext_61,plaintext_62,plaintext_63,plaintext_64),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) = 
    let (left1_1,left1_2,left1_3,left1_4,left1_5,left1_6,left1_7,left1_8,left1_9,left1_10,left1_11,left1_12,left1_13,left1_14,left1_15,left1_16,left1_17,left1_18,left1_19,left1_20,left1_21,left1_22,left1_23,left1_24,left1_25,left1_26,left1_27,left1_28,left1_29,left1_30,left1_31,left1_32,right1_1,right1_2,right1_3,right1_4,right1_5,right1_6,right1_7,right1_8,right1_9,right1_10,right1_11,right1_12,right1_13,right1_14,right1_15,right1_16,right1_17,right1_18,right1_19,right1_20,right1_21,right1_22,right1_23,right1_24,right1_25,right1_26,right1_27,right1_28,right1_29,right1_30,right1_31,right1_32,key_tmp1_1,key_tmp1_2,key_tmp1_3,key_tmp1_4,key_tmp1_5,key_tmp1_6,key_tmp1_7,key_tmp1_8,key_tmp1_9,key_tmp1_10,key_tmp1_11,key_tmp1_12,key_tmp1_13,key_tmp1_14,key_tmp1_15,key_tmp1_16,key_tmp1_17,key_tmp1_18,key_tmp1_19,key_tmp1_20,key_tmp1_21,key_tmp1_22,key_tmp1_23,key_tmp1_24,key_tmp1_25,key_tmp1_26,key_tmp1_27,key_tmp1_28,key_tmp1_29,key_tmp1_30,key_tmp1_31,key_tmp1_32,key_tmp1_33,key_tmp1_34,key_tmp1_35,key_tmp1_36,key_tmp1_37,key_tmp1_38,key_tmp1_39,key_tmp1_40,key_tmp1_41,key_tmp1_42,key_tmp1_43,key_tmp1_44,key_tmp1_45,key_tmp1_46,key_tmp1_47,key_tmp1_48,key_tmp1_49,key_tmp1_50,key_tmp1_51,key_tmp1_52,key_tmp1_53,key_tmp1_54,key_tmp1_55,key_tmp1_56,key_tmp1_57,key_tmp1_58,key_tmp1_59,key_tmp1_60,key_tmp1_61,key_tmp1_62,key_tmp1_63,key_tmp1_64) = convert8 ((init_p_ (id ((plaintext_1,plaintext_2,plaintext_3,plaintext_4,plaintext_5,plaintext_6,plaintext_7,plaintext_8,plaintext_9,plaintext_10,plaintext_11,plaintext_12,plaintext_13,plaintext_14,plaintext_15,plaintext_16,plaintext_17,plaintext_18,plaintext_19,plaintext_20,plaintext_21,plaintext_22,plaintext_23,plaintext_24,plaintext_25,plaintext_26,plaintext_27,plaintext_28,plaintext_29,plaintext_30,plaintext_31,plaintext_32,plaintext_33,plaintext_34,plaintext_35,plaintext_36,plaintext_37,plaintext_38,plaintext_39,plaintext_40,plaintext_41,plaintext_42,plaintext_43,plaintext_44,plaintext_45,plaintext_46,plaintext_47,plaintext_48,plaintext_49,plaintext_50,plaintext_51,plaintext_52,plaintext_53,plaintext_54,plaintext_55,plaintext_56,plaintext_57,plaintext_58,plaintext_59,plaintext_60,plaintext_61,plaintext_62,plaintext_63,plaintext_64))),key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) in 
    let (left2_1,left2_2,left2_3,left2_4,left2_5,left2_6,left2_7,left2_8,left2_9,left2_10,left2_11,left2_12,left2_13,left2_14,left2_15,left2_16,left2_17,left2_18,left2_19,left2_20,left2_21,left2_22,left2_23,left2_24,left2_25,left2_26,left2_27,left2_28,left2_29,left2_30,left2_31,left2_32,right2_1,right2_2,right2_3,right2_4,right2_5,right2_6,right2_7,right2_8,right2_9,right2_10,right2_11,right2_12,right2_13,right2_14,right2_15,right2_16,right2_17,right2_18,right2_19,right2_20,right2_21,right2_22,right2_23,right2_24,right2_25,right2_26,right2_27,right2_28,right2_29,right2_30,right2_31,right2_32,key_tmp2_1,key_tmp2_2,key_tmp2_3,key_tmp2_4,key_tmp2_5,key_tmp2_6,key_tmp2_7,key_tmp2_8,key_tmp2_9,key_tmp2_10,key_tmp2_11,key_tmp2_12,key_tmp2_13,key_tmp2_14,key_tmp2_15,key_tmp2_16,key_tmp2_17,key_tmp2_18,key_tmp2_19,key_tmp2_20,key_tmp2_21,key_tmp2_22,key_tmp2_23,key_tmp2_24,key_tmp2_25,key_tmp2_26,key_tmp2_27,key_tmp2_28,key_tmp2_29,key_tmp2_30,key_tmp2_31,key_tmp2_32,key_tmp2_33,key_tmp2_34,key_tmp2_35,key_tmp2_36,key_tmp2_37,key_tmp2_38,key_tmp2_39,key_tmp2_40,key_tmp2_41,key_tmp2_42,key_tmp2_43,key_tmp2_44,key_tmp2_45,key_tmp2_46,key_tmp2_47,key_tmp2_48,key_tmp2_49,key_tmp2_50,key_tmp2_51,key_tmp2_52,key_tmp2_53,key_tmp2_54,key_tmp2_55,key_tmp2_56,key_tmp2_57,key_tmp2_58,key_tmp2_59,key_tmp2_60,key_tmp2_61,key_tmp2_62,key_tmp2_63,key_tmp2_64) = des_single1_ (id ((left1_1,left1_2,left1_3,left1_4,left1_5,left1_6,left1_7,left1_8,left1_9,left1_10,left1_11,left1_12,left1_13,left1_14,left1_15,left1_16,left1_17,left1_18,left1_19,left1_20,left1_21,left1_22,left1_23,left1_24,left1_25,left1_26,left1_27,left1_28,left1_29,left1_30,left1_31,left1_32),(right1_1,right1_2,right1_3,right1_4,right1_5,right1_6,right1_7,right1_8,right1_9,right1_10,right1_11,right1_12,right1_13,right1_14,right1_15,right1_16,right1_17,right1_18,right1_19,right1_20,right1_21,right1_22,right1_23,right1_24,right1_25,right1_26,right1_27,right1_28,right1_29,right1_30,right1_31,right1_32),(key_tmp1_1,key_tmp1_2,key_tmp1_3,key_tmp1_4,key_tmp1_5,key_tmp1_6,key_tmp1_7,key_tmp1_8,key_tmp1_9,key_tmp1_10,key_tmp1_11,key_tmp1_12,key_tmp1_13,key_tmp1_14,key_tmp1_15,key_tmp1_16,key_tmp1_17,key_tmp1_18,key_tmp1_19,key_tmp1_20,key_tmp1_21,key_tmp1_22,key_tmp1_23,key_tmp1_24,key_tmp1_25,key_tmp1_26,key_tmp1_27,key_tmp1_28,key_tmp1_29,key_tmp1_30,key_tmp1_31,key_tmp1_32,key_tmp1_33,key_tmp1_34,key_tmp1_35,key_tmp1_36,key_tmp1_37,key_tmp1_38,key_tmp1_39,key_tmp1_40,key_tmp1_41,key_tmp1_42,key_tmp1_43,key_tmp1_44,key_tmp1_45,key_tmp1_46,key_tmp1_47,key_tmp1_48,key_tmp1_49,key_tmp1_50,key_tmp1_51,key_tmp1_52,key_tmp1_53,key_tmp1_54,key_tmp1_55,key_tmp1_56,key_tmp1_57,key_tmp1_58,key_tmp1_59,key_tmp1_60,key_tmp1_61,key_tmp1_62,key_tmp1_63,key_tmp1_64))) in 
    let (left3_1,left3_2,left3_3,left3_4,left3_5,left3_6,left3_7,left3_8,left3_9,left3_10,left3_11,left3_12,left3_13,left3_14,left3_15,left3_16,left3_17,left3_18,left3_19,left3_20,left3_21,left3_22,left3_23,left3_24,left3_25,left3_26,left3_27,left3_28,left3_29,left3_30,left3_31,left3_32,right3_1,right3_2,right3_3,right3_4,right3_5,right3_6,right3_7,right3_8,right3_9,right3_10,right3_11,right3_12,right3_13,right3_14,right3_15,right3_16,right3_17,right3_18,right3_19,right3_20,right3_21,right3_22,right3_23,right3_24,right3_25,right3_26,right3_27,right3_28,right3_29,right3_30,right3_31,right3_32,key_tmp3_1,key_tmp3_2,key_tmp3_3,key_tmp3_4,key_tmp3_5,key_tmp3_6,key_tmp3_7,key_tmp3_8,key_tmp3_9,key_tmp3_10,key_tmp3_11,key_tmp3_12,key_tmp3_13,key_tmp3_14,key_tmp3_15,key_tmp3_16,key_tmp3_17,key_tmp3_18,key_tmp3_19,key_tmp3_20,key_tmp3_21,key_tmp3_22,key_tmp3_23,key_tmp3_24,key_tmp3_25,key_tmp3_26,key_tmp3_27,key_tmp3_28,key_tmp3_29,key_tmp3_30,key_tmp3_31,key_tmp3_32,key_tmp3_33,key_tmp3_34,key_tmp3_35,key_tmp3_36,key_tmp3_37,key_tmp3_38,key_tmp3_39,key_tmp3_40,key_tmp3_41,key_tmp3_42,key_tmp3_43,key_tmp3_44,key_tmp3_45,key_tmp3_46,key_tmp3_47,key_tmp3_48,key_tmp3_49,key_tmp3_50,key_tmp3_51,key_tmp3_52,key_tmp3_53,key_tmp3_54,key_tmp3_55,key_tmp3_56,key_tmp3_57,key_tmp3_58,key_tmp3_59,key_tmp3_60,key_tmp3_61,key_tmp3_62,key_tmp3_63,key_tmp3_64) = des_single2_ (id ((left2_1,left2_2,left2_3,left2_4,left2_5,left2_6,left2_7,left2_8,left2_9,left2_10,left2_11,left2_12,left2_13,left2_14,left2_15,left2_16,left2_17,left2_18,left2_19,left2_20,left2_21,left2_22,left2_23,left2_24,left2_25,left2_26,left2_27,left2_28,left2_29,left2_30,left2_31,left2_32),(right2_1,right2_2,right2_3,right2_4,right2_5,right2_6,right2_7,right2_8,right2_9,right2_10,right2_11,right2_12,right2_13,right2_14,right2_15,right2_16,right2_17,right2_18,right2_19,right2_20,right2_21,right2_22,right2_23,right2_24,right2_25,right2_26,right2_27,right2_28,right2_29,right2_30,right2_31,right2_32),(key_tmp2_1,key_tmp2_2,key_tmp2_3,key_tmp2_4,key_tmp2_5,key_tmp2_6,key_tmp2_7,key_tmp2_8,key_tmp2_9,key_tmp2_10,key_tmp2_11,key_tmp2_12,key_tmp2_13,key_tmp2_14,key_tmp2_15,key_tmp2_16,key_tmp2_17,key_tmp2_18,key_tmp2_19,key_tmp2_20,key_tmp2_21,key_tmp2_22,key_tmp2_23,key_tmp2_24,key_tmp2_25,key_tmp2_26,key_tmp2_27,key_tmp2_28,key_tmp2_29,key_tmp2_30,key_tmp2_31,key_tmp2_32,key_tmp2_33,key_tmp2_34,key_tmp2_35,key_tmp2_36,key_tmp2_37,key_tmp2_38,key_tmp2_39,key_tmp2_40,key_tmp2_41,key_tmp2_42,key_tmp2_43,key_tmp2_44,key_tmp2_45,key_tmp2_46,key_tmp2_47,key_tmp2_48,key_tmp2_49,key_tmp2_50,key_tmp2_51,key_tmp2_52,key_tmp2_53,key_tmp2_54,key_tmp2_55,key_tmp2_56,key_tmp2_57,key_tmp2_58,key_tmp2_59,key_tmp2_60,key_tmp2_61,key_tmp2_62,key_tmp2_63,key_tmp2_64))) in 
    let (left4_1,left4_2,left4_3,left4_4,left4_5,left4_6,left4_7,left4_8,left4_9,left4_10,left4_11,left4_12,left4_13,left4_14,left4_15,left4_16,left4_17,left4_18,left4_19,left4_20,left4_21,left4_22,left4_23,left4_24,left4_25,left4_26,left4_27,left4_28,left4_29,left4_30,left4_31,left4_32,right4_1,right4_2,right4_3,right4_4,right4_5,right4_6,right4_7,right4_8,right4_9,right4_10,right4_11,right4_12,right4_13,right4_14,right4_15,right4_16,right4_17,right4_18,right4_19,right4_20,right4_21,right4_22,right4_23,right4_24,right4_25,right4_26,right4_27,right4_28,right4_29,right4_30,right4_31,right4_32,key_tmp4_1,key_tmp4_2,key_tmp4_3,key_tmp4_4,key_tmp4_5,key_tmp4_6,key_tmp4_7,key_tmp4_8,key_tmp4_9,key_tmp4_10,key_tmp4_11,key_tmp4_12,key_tmp4_13,key_tmp4_14,key_tmp4_15,key_tmp4_16,key_tmp4_17,key_tmp4_18,key_tmp4_19,key_tmp4_20,key_tmp4_21,key_tmp4_22,key_tmp4_23,key_tmp4_24,key_tmp4_25,key_tmp4_26,key_tmp4_27,key_tmp4_28,key_tmp4_29,key_tmp4_30,key_tmp4_31,key_tmp4_32,key_tmp4_33,key_tmp4_34,key_tmp4_35,key_tmp4_36,key_tmp4_37,key_tmp4_38,key_tmp4_39,key_tmp4_40,key_tmp4_41,key_tmp4_42,key_tmp4_43,key_tmp4_44,key_tmp4_45,key_tmp4_46,key_tmp4_47,key_tmp4_48,key_tmp4_49,key_tmp4_50,key_tmp4_51,key_tmp4_52,key_tmp4_53,key_tmp4_54,key_tmp4_55,key_tmp4_56,key_tmp4_57,key_tmp4_58,key_tmp4_59,key_tmp4_60,key_tmp4_61,key_tmp4_62,key_tmp4_63,key_tmp4_64) = des_single3_ (id ((left3_1,left3_2,left3_3,left3_4,left3_5,left3_6,left3_7,left3_8,left3_9,left3_10,left3_11,left3_12,left3_13,left3_14,left3_15,left3_16,left3_17,left3_18,left3_19,left3_20,left3_21,left3_22,left3_23,left3_24,left3_25,left3_26,left3_27,left3_28,left3_29,left3_30,left3_31,left3_32),(right3_1,right3_2,right3_3,right3_4,right3_5,right3_6,right3_7,right3_8,right3_9,right3_10,right3_11,right3_12,right3_13,right3_14,right3_15,right3_16,right3_17,right3_18,right3_19,right3_20,right3_21,right3_22,right3_23,right3_24,right3_25,right3_26,right3_27,right3_28,right3_29,right3_30,right3_31,right3_32),(key_tmp3_1,key_tmp3_2,key_tmp3_3,key_tmp3_4,key_tmp3_5,key_tmp3_6,key_tmp3_7,key_tmp3_8,key_tmp3_9,key_tmp3_10,key_tmp3_11,key_tmp3_12,key_tmp3_13,key_tmp3_14,key_tmp3_15,key_tmp3_16,key_tmp3_17,key_tmp3_18,key_tmp3_19,key_tmp3_20,key_tmp3_21,key_tmp3_22,key_tmp3_23,key_tmp3_24,key_tmp3_25,key_tmp3_26,key_tmp3_27,key_tmp3_28,key_tmp3_29,key_tmp3_30,key_tmp3_31,key_tmp3_32,key_tmp3_33,key_tmp3_34,key_tmp3_35,key_tmp3_36,key_tmp3_37,key_tmp3_38,key_tmp3_39,key_tmp3_40,key_tmp3_41,key_tmp3_42,key_tmp3_43,key_tmp3_44,key_tmp3_45,key_tmp3_46,key_tmp3_47,key_tmp3_48,key_tmp3_49,key_tmp3_50,key_tmp3_51,key_tmp3_52,key_tmp3_53,key_tmp3_54,key_tmp3_55,key_tmp3_56,key_tmp3_57,key_tmp3_58,key_tmp3_59,key_tmp3_60,key_tmp3_61,key_tmp3_62,key_tmp3_63,key_tmp3_64))) in 
    let (left5_1,left5_2,left5_3,left5_4,left5_5,left5_6,left5_7,left5_8,left5_9,left5_10,left5_11,left5_12,left5_13,left5_14,left5_15,left5_16,left5_17,left5_18,left5_19,left5_20,left5_21,left5_22,left5_23,left5_24,left5_25,left5_26,left5_27,left5_28,left5_29,left5_30,left5_31,left5_32,right5_1,right5_2,right5_3,right5_4,right5_5,right5_6,right5_7,right5_8,right5_9,right5_10,right5_11,right5_12,right5_13,right5_14,right5_15,right5_16,right5_17,right5_18,right5_19,right5_20,right5_21,right5_22,right5_23,right5_24,right5_25,right5_26,right5_27,right5_28,right5_29,right5_30,right5_31,right5_32,key_tmp5_1,key_tmp5_2,key_tmp5_3,key_tmp5_4,key_tmp5_5,key_tmp5_6,key_tmp5_7,key_tmp5_8,key_tmp5_9,key_tmp5_10,key_tmp5_11,key_tmp5_12,key_tmp5_13,key_tmp5_14,key_tmp5_15,key_tmp5_16,key_tmp5_17,key_tmp5_18,key_tmp5_19,key_tmp5_20,key_tmp5_21,key_tmp5_22,key_tmp5_23,key_tmp5_24,key_tmp5_25,key_tmp5_26,key_tmp5_27,key_tmp5_28,key_tmp5_29,key_tmp5_30,key_tmp5_31,key_tmp5_32,key_tmp5_33,key_tmp5_34,key_tmp5_35,key_tmp5_36,key_tmp5_37,key_tmp5_38,key_tmp5_39,key_tmp5_40,key_tmp5_41,key_tmp5_42,key_tmp5_43,key_tmp5_44,key_tmp5_45,key_tmp5_46,key_tmp5_47,key_tmp5_48,key_tmp5_49,key_tmp5_50,key_tmp5_51,key_tmp5_52,key_tmp5_53,key_tmp5_54,key_tmp5_55,key_tmp5_56,key_tmp5_57,key_tmp5_58,key_tmp5_59,key_tmp5_60,key_tmp5_61,key_tmp5_62,key_tmp5_63,key_tmp5_64) = des_single4_ (id ((left4_1,left4_2,left4_3,left4_4,left4_5,left4_6,left4_7,left4_8,left4_9,left4_10,left4_11,left4_12,left4_13,left4_14,left4_15,left4_16,left4_17,left4_18,left4_19,left4_20,left4_21,left4_22,left4_23,left4_24,left4_25,left4_26,left4_27,left4_28,left4_29,left4_30,left4_31,left4_32),(right4_1,right4_2,right4_3,right4_4,right4_5,right4_6,right4_7,right4_8,right4_9,right4_10,right4_11,right4_12,right4_13,right4_14,right4_15,right4_16,right4_17,right4_18,right4_19,right4_20,right4_21,right4_22,right4_23,right4_24,right4_25,right4_26,right4_27,right4_28,right4_29,right4_30,right4_31,right4_32),(key_tmp4_1,key_tmp4_2,key_tmp4_3,key_tmp4_4,key_tmp4_5,key_tmp4_6,key_tmp4_7,key_tmp4_8,key_tmp4_9,key_tmp4_10,key_tmp4_11,key_tmp4_12,key_tmp4_13,key_tmp4_14,key_tmp4_15,key_tmp4_16,key_tmp4_17,key_tmp4_18,key_tmp4_19,key_tmp4_20,key_tmp4_21,key_tmp4_22,key_tmp4_23,key_tmp4_24,key_tmp4_25,key_tmp4_26,key_tmp4_27,key_tmp4_28,key_tmp4_29,key_tmp4_30,key_tmp4_31,key_tmp4_32,key_tmp4_33,key_tmp4_34,key_tmp4_35,key_tmp4_36,key_tmp4_37,key_tmp4_38,key_tmp4_39,key_tmp4_40,key_tmp4_41,key_tmp4_42,key_tmp4_43,key_tmp4_44,key_tmp4_45,key_tmp4_46,key_tmp4_47,key_tmp4_48,key_tmp4_49,key_tmp4_50,key_tmp4_51,key_tmp4_52,key_tmp4_53,key_tmp4_54,key_tmp4_55,key_tmp4_56,key_tmp4_57,key_tmp4_58,key_tmp4_59,key_tmp4_60,key_tmp4_61,key_tmp4_62,key_tmp4_63,key_tmp4_64))) in 
    let (left6_1,left6_2,left6_3,left6_4,left6_5,left6_6,left6_7,left6_8,left6_9,left6_10,left6_11,left6_12,left6_13,left6_14,left6_15,left6_16,left6_17,left6_18,left6_19,left6_20,left6_21,left6_22,left6_23,left6_24,left6_25,left6_26,left6_27,left6_28,left6_29,left6_30,left6_31,left6_32,right6_1,right6_2,right6_3,right6_4,right6_5,right6_6,right6_7,right6_8,right6_9,right6_10,right6_11,right6_12,right6_13,right6_14,right6_15,right6_16,right6_17,right6_18,right6_19,right6_20,right6_21,right6_22,right6_23,right6_24,right6_25,right6_26,right6_27,right6_28,right6_29,right6_30,right6_31,right6_32,key_tmp6_1,key_tmp6_2,key_tmp6_3,key_tmp6_4,key_tmp6_5,key_tmp6_6,key_tmp6_7,key_tmp6_8,key_tmp6_9,key_tmp6_10,key_tmp6_11,key_tmp6_12,key_tmp6_13,key_tmp6_14,key_tmp6_15,key_tmp6_16,key_tmp6_17,key_tmp6_18,key_tmp6_19,key_tmp6_20,key_tmp6_21,key_tmp6_22,key_tmp6_23,key_tmp6_24,key_tmp6_25,key_tmp6_26,key_tmp6_27,key_tmp6_28,key_tmp6_29,key_tmp6_30,key_tmp6_31,key_tmp6_32,key_tmp6_33,key_tmp6_34,key_tmp6_35,key_tmp6_36,key_tmp6_37,key_tmp6_38,key_tmp6_39,key_tmp6_40,key_tmp6_41,key_tmp6_42,key_tmp6_43,key_tmp6_44,key_tmp6_45,key_tmp6_46,key_tmp6_47,key_tmp6_48,key_tmp6_49,key_tmp6_50,key_tmp6_51,key_tmp6_52,key_tmp6_53,key_tmp6_54,key_tmp6_55,key_tmp6_56,key_tmp6_57,key_tmp6_58,key_tmp6_59,key_tmp6_60,key_tmp6_61,key_tmp6_62,key_tmp6_63,key_tmp6_64) = des_single5_ (id ((left5_1,left5_2,left5_3,left5_4,left5_5,left5_6,left5_7,left5_8,left5_9,left5_10,left5_11,left5_12,left5_13,left5_14,left5_15,left5_16,left5_17,left5_18,left5_19,left5_20,left5_21,left5_22,left5_23,left5_24,left5_25,left5_26,left5_27,left5_28,left5_29,left5_30,left5_31,left5_32),(right5_1,right5_2,right5_3,right5_4,right5_5,right5_6,right5_7,right5_8,right5_9,right5_10,right5_11,right5_12,right5_13,right5_14,right5_15,right5_16,right5_17,right5_18,right5_19,right5_20,right5_21,right5_22,right5_23,right5_24,right5_25,right5_26,right5_27,right5_28,right5_29,right5_30,right5_31,right5_32),(key_tmp5_1,key_tmp5_2,key_tmp5_3,key_tmp5_4,key_tmp5_5,key_tmp5_6,key_tmp5_7,key_tmp5_8,key_tmp5_9,key_tmp5_10,key_tmp5_11,key_tmp5_12,key_tmp5_13,key_tmp5_14,key_tmp5_15,key_tmp5_16,key_tmp5_17,key_tmp5_18,key_tmp5_19,key_tmp5_20,key_tmp5_21,key_tmp5_22,key_tmp5_23,key_tmp5_24,key_tmp5_25,key_tmp5_26,key_tmp5_27,key_tmp5_28,key_tmp5_29,key_tmp5_30,key_tmp5_31,key_tmp5_32,key_tmp5_33,key_tmp5_34,key_tmp5_35,key_tmp5_36,key_tmp5_37,key_tmp5_38,key_tmp5_39,key_tmp5_40,key_tmp5_41,key_tmp5_42,key_tmp5_43,key_tmp5_44,key_tmp5_45,key_tmp5_46,key_tmp5_47,key_tmp5_48,key_tmp5_49,key_tmp5_50,key_tmp5_51,key_tmp5_52,key_tmp5_53,key_tmp5_54,key_tmp5_55,key_tmp5_56,key_tmp5_57,key_tmp5_58,key_tmp5_59,key_tmp5_60,key_tmp5_61,key_tmp5_62,key_tmp5_63,key_tmp5_64))) in 
    let (left7_1,left7_2,left7_3,left7_4,left7_5,left7_6,left7_7,left7_8,left7_9,left7_10,left7_11,left7_12,left7_13,left7_14,left7_15,left7_16,left7_17,left7_18,left7_19,left7_20,left7_21,left7_22,left7_23,left7_24,left7_25,left7_26,left7_27,left7_28,left7_29,left7_30,left7_31,left7_32,right7_1,right7_2,right7_3,right7_4,right7_5,right7_6,right7_7,right7_8,right7_9,right7_10,right7_11,right7_12,right7_13,right7_14,right7_15,right7_16,right7_17,right7_18,right7_19,right7_20,right7_21,right7_22,right7_23,right7_24,right7_25,right7_26,right7_27,right7_28,right7_29,right7_30,right7_31,right7_32,key_tmp7_1,key_tmp7_2,key_tmp7_3,key_tmp7_4,key_tmp7_5,key_tmp7_6,key_tmp7_7,key_tmp7_8,key_tmp7_9,key_tmp7_10,key_tmp7_11,key_tmp7_12,key_tmp7_13,key_tmp7_14,key_tmp7_15,key_tmp7_16,key_tmp7_17,key_tmp7_18,key_tmp7_19,key_tmp7_20,key_tmp7_21,key_tmp7_22,key_tmp7_23,key_tmp7_24,key_tmp7_25,key_tmp7_26,key_tmp7_27,key_tmp7_28,key_tmp7_29,key_tmp7_30,key_tmp7_31,key_tmp7_32,key_tmp7_33,key_tmp7_34,key_tmp7_35,key_tmp7_36,key_tmp7_37,key_tmp7_38,key_tmp7_39,key_tmp7_40,key_tmp7_41,key_tmp7_42,key_tmp7_43,key_tmp7_44,key_tmp7_45,key_tmp7_46,key_tmp7_47,key_tmp7_48,key_tmp7_49,key_tmp7_50,key_tmp7_51,key_tmp7_52,key_tmp7_53,key_tmp7_54,key_tmp7_55,key_tmp7_56,key_tmp7_57,key_tmp7_58,key_tmp7_59,key_tmp7_60,key_tmp7_61,key_tmp7_62,key_tmp7_63,key_tmp7_64) = des_single6_ (id ((left6_1,left6_2,left6_3,left6_4,left6_5,left6_6,left6_7,left6_8,left6_9,left6_10,left6_11,left6_12,left6_13,left6_14,left6_15,left6_16,left6_17,left6_18,left6_19,left6_20,left6_21,left6_22,left6_23,left6_24,left6_25,left6_26,left6_27,left6_28,left6_29,left6_30,left6_31,left6_32),(right6_1,right6_2,right6_3,right6_4,right6_5,right6_6,right6_7,right6_8,right6_9,right6_10,right6_11,right6_12,right6_13,right6_14,right6_15,right6_16,right6_17,right6_18,right6_19,right6_20,right6_21,right6_22,right6_23,right6_24,right6_25,right6_26,right6_27,right6_28,right6_29,right6_30,right6_31,right6_32),(key_tmp6_1,key_tmp6_2,key_tmp6_3,key_tmp6_4,key_tmp6_5,key_tmp6_6,key_tmp6_7,key_tmp6_8,key_tmp6_9,key_tmp6_10,key_tmp6_11,key_tmp6_12,key_tmp6_13,key_tmp6_14,key_tmp6_15,key_tmp6_16,key_tmp6_17,key_tmp6_18,key_tmp6_19,key_tmp6_20,key_tmp6_21,key_tmp6_22,key_tmp6_23,key_tmp6_24,key_tmp6_25,key_tmp6_26,key_tmp6_27,key_tmp6_28,key_tmp6_29,key_tmp6_30,key_tmp6_31,key_tmp6_32,key_tmp6_33,key_tmp6_34,key_tmp6_35,key_tmp6_36,key_tmp6_37,key_tmp6_38,key_tmp6_39,key_tmp6_40,key_tmp6_41,key_tmp6_42,key_tmp6_43,key_tmp6_44,key_tmp6_45,key_tmp6_46,key_tmp6_47,key_tmp6_48,key_tmp6_49,key_tmp6_50,key_tmp6_51,key_tmp6_52,key_tmp6_53,key_tmp6_54,key_tmp6_55,key_tmp6_56,key_tmp6_57,key_tmp6_58,key_tmp6_59,key_tmp6_60,key_tmp6_61,key_tmp6_62,key_tmp6_63,key_tmp6_64))) in 
    let (left8_1,left8_2,left8_3,left8_4,left8_5,left8_6,left8_7,left8_8,left8_9,left8_10,left8_11,left8_12,left8_13,left8_14,left8_15,left8_16,left8_17,left8_18,left8_19,left8_20,left8_21,left8_22,left8_23,left8_24,left8_25,left8_26,left8_27,left8_28,left8_29,left8_30,left8_31,left8_32,right8_1,right8_2,right8_3,right8_4,right8_5,right8_6,right8_7,right8_8,right8_9,right8_10,right8_11,right8_12,right8_13,right8_14,right8_15,right8_16,right8_17,right8_18,right8_19,right8_20,right8_21,right8_22,right8_23,right8_24,right8_25,right8_26,right8_27,right8_28,right8_29,right8_30,right8_31,right8_32,key_tmp8_1,key_tmp8_2,key_tmp8_3,key_tmp8_4,key_tmp8_5,key_tmp8_6,key_tmp8_7,key_tmp8_8,key_tmp8_9,key_tmp8_10,key_tmp8_11,key_tmp8_12,key_tmp8_13,key_tmp8_14,key_tmp8_15,key_tmp8_16,key_tmp8_17,key_tmp8_18,key_tmp8_19,key_tmp8_20,key_tmp8_21,key_tmp8_22,key_tmp8_23,key_tmp8_24,key_tmp8_25,key_tmp8_26,key_tmp8_27,key_tmp8_28,key_tmp8_29,key_tmp8_30,key_tmp8_31,key_tmp8_32,key_tmp8_33,key_tmp8_34,key_tmp8_35,key_tmp8_36,key_tmp8_37,key_tmp8_38,key_tmp8_39,key_tmp8_40,key_tmp8_41,key_tmp8_42,key_tmp8_43,key_tmp8_44,key_tmp8_45,key_tmp8_46,key_tmp8_47,key_tmp8_48,key_tmp8_49,key_tmp8_50,key_tmp8_51,key_tmp8_52,key_tmp8_53,key_tmp8_54,key_tmp8_55,key_tmp8_56,key_tmp8_57,key_tmp8_58,key_tmp8_59,key_tmp8_60,key_tmp8_61,key_tmp8_62,key_tmp8_63,key_tmp8_64) = des_single7_ (id ((left7_1,left7_2,left7_3,left7_4,left7_5,left7_6,left7_7,left7_8,left7_9,left7_10,left7_11,left7_12,left7_13,left7_14,left7_15,left7_16,left7_17,left7_18,left7_19,left7_20,left7_21,left7_22,left7_23,left7_24,left7_25,left7_26,left7_27,left7_28,left7_29,left7_30,left7_31,left7_32),(right7_1,right7_2,right7_3,right7_4,right7_5,right7_6,right7_7,right7_8,right7_9,right7_10,right7_11,right7_12,right7_13,right7_14,right7_15,right7_16,right7_17,right7_18,right7_19,right7_20,right7_21,right7_22,right7_23,right7_24,right7_25,right7_26,right7_27,right7_28,right7_29,right7_30,right7_31,right7_32),(key_tmp7_1,key_tmp7_2,key_tmp7_3,key_tmp7_4,key_tmp7_5,key_tmp7_6,key_tmp7_7,key_tmp7_8,key_tmp7_9,key_tmp7_10,key_tmp7_11,key_tmp7_12,key_tmp7_13,key_tmp7_14,key_tmp7_15,key_tmp7_16,key_tmp7_17,key_tmp7_18,key_tmp7_19,key_tmp7_20,key_tmp7_21,key_tmp7_22,key_tmp7_23,key_tmp7_24,key_tmp7_25,key_tmp7_26,key_tmp7_27,key_tmp7_28,key_tmp7_29,key_tmp7_30,key_tmp7_31,key_tmp7_32,key_tmp7_33,key_tmp7_34,key_tmp7_35,key_tmp7_36,key_tmp7_37,key_tmp7_38,key_tmp7_39,key_tmp7_40,key_tmp7_41,key_tmp7_42,key_tmp7_43,key_tmp7_44,key_tmp7_45,key_tmp7_46,key_tmp7_47,key_tmp7_48,key_tmp7_49,key_tmp7_50,key_tmp7_51,key_tmp7_52,key_tmp7_53,key_tmp7_54,key_tmp7_55,key_tmp7_56,key_tmp7_57,key_tmp7_58,key_tmp7_59,key_tmp7_60,key_tmp7_61,key_tmp7_62,key_tmp7_63,key_tmp7_64))) in 
    let (left9_1,left9_2,left9_3,left9_4,left9_5,left9_6,left9_7,left9_8,left9_9,left9_10,left9_11,left9_12,left9_13,left9_14,left9_15,left9_16,left9_17,left9_18,left9_19,left9_20,left9_21,left9_22,left9_23,left9_24,left9_25,left9_26,left9_27,left9_28,left9_29,left9_30,left9_31,left9_32,right9_1,right9_2,right9_3,right9_4,right9_5,right9_6,right9_7,right9_8,right9_9,right9_10,right9_11,right9_12,right9_13,right9_14,right9_15,right9_16,right9_17,right9_18,right9_19,right9_20,right9_21,right9_22,right9_23,right9_24,right9_25,right9_26,right9_27,right9_28,right9_29,right9_30,right9_31,right9_32,key_tmp9_1,key_tmp9_2,key_tmp9_3,key_tmp9_4,key_tmp9_5,key_tmp9_6,key_tmp9_7,key_tmp9_8,key_tmp9_9,key_tmp9_10,key_tmp9_11,key_tmp9_12,key_tmp9_13,key_tmp9_14,key_tmp9_15,key_tmp9_16,key_tmp9_17,key_tmp9_18,key_tmp9_19,key_tmp9_20,key_tmp9_21,key_tmp9_22,key_tmp9_23,key_tmp9_24,key_tmp9_25,key_tmp9_26,key_tmp9_27,key_tmp9_28,key_tmp9_29,key_tmp9_30,key_tmp9_31,key_tmp9_32,key_tmp9_33,key_tmp9_34,key_tmp9_35,key_tmp9_36,key_tmp9_37,key_tmp9_38,key_tmp9_39,key_tmp9_40,key_tmp9_41,key_tmp9_42,key_tmp9_43,key_tmp9_44,key_tmp9_45,key_tmp9_46,key_tmp9_47,key_tmp9_48,key_tmp9_49,key_tmp9_50,key_tmp9_51,key_tmp9_52,key_tmp9_53,key_tmp9_54,key_tmp9_55,key_tmp9_56,key_tmp9_57,key_tmp9_58,key_tmp9_59,key_tmp9_60,key_tmp9_61,key_tmp9_62,key_tmp9_63,key_tmp9_64) = des_single8_ (id ((left8_1,left8_2,left8_3,left8_4,left8_5,left8_6,left8_7,left8_8,left8_9,left8_10,left8_11,left8_12,left8_13,left8_14,left8_15,left8_16,left8_17,left8_18,left8_19,left8_20,left8_21,left8_22,left8_23,left8_24,left8_25,left8_26,left8_27,left8_28,left8_29,left8_30,left8_31,left8_32),(right8_1,right8_2,right8_3,right8_4,right8_5,right8_6,right8_7,right8_8,right8_9,right8_10,right8_11,right8_12,right8_13,right8_14,right8_15,right8_16,right8_17,right8_18,right8_19,right8_20,right8_21,right8_22,right8_23,right8_24,right8_25,right8_26,right8_27,right8_28,right8_29,right8_30,right8_31,right8_32),(key_tmp8_1,key_tmp8_2,key_tmp8_3,key_tmp8_4,key_tmp8_5,key_tmp8_6,key_tmp8_7,key_tmp8_8,key_tmp8_9,key_tmp8_10,key_tmp8_11,key_tmp8_12,key_tmp8_13,key_tmp8_14,key_tmp8_15,key_tmp8_16,key_tmp8_17,key_tmp8_18,key_tmp8_19,key_tmp8_20,key_tmp8_21,key_tmp8_22,key_tmp8_23,key_tmp8_24,key_tmp8_25,key_tmp8_26,key_tmp8_27,key_tmp8_28,key_tmp8_29,key_tmp8_30,key_tmp8_31,key_tmp8_32,key_tmp8_33,key_tmp8_34,key_tmp8_35,key_tmp8_36,key_tmp8_37,key_tmp8_38,key_tmp8_39,key_tmp8_40,key_tmp8_41,key_tmp8_42,key_tmp8_43,key_tmp8_44,key_tmp8_45,key_tmp8_46,key_tmp8_47,key_tmp8_48,key_tmp8_49,key_tmp8_50,key_tmp8_51,key_tmp8_52,key_tmp8_53,key_tmp8_54,key_tmp8_55,key_tmp8_56,key_tmp8_57,key_tmp8_58,key_tmp8_59,key_tmp8_60,key_tmp8_61,key_tmp8_62,key_tmp8_63,key_tmp8_64))) in 
    let (left10_1,left10_2,left10_3,left10_4,left10_5,left10_6,left10_7,left10_8,left10_9,left10_10,left10_11,left10_12,left10_13,left10_14,left10_15,left10_16,left10_17,left10_18,left10_19,left10_20,left10_21,left10_22,left10_23,left10_24,left10_25,left10_26,left10_27,left10_28,left10_29,left10_30,left10_31,left10_32,right10_1,right10_2,right10_3,right10_4,right10_5,right10_6,right10_7,right10_8,right10_9,right10_10,right10_11,right10_12,right10_13,right10_14,right10_15,right10_16,right10_17,right10_18,right10_19,right10_20,right10_21,right10_22,right10_23,right10_24,right10_25,right10_26,right10_27,right10_28,right10_29,right10_30,right10_31,right10_32,key_tmp10_1,key_tmp10_2,key_tmp10_3,key_tmp10_4,key_tmp10_5,key_tmp10_6,key_tmp10_7,key_tmp10_8,key_tmp10_9,key_tmp10_10,key_tmp10_11,key_tmp10_12,key_tmp10_13,key_tmp10_14,key_tmp10_15,key_tmp10_16,key_tmp10_17,key_tmp10_18,key_tmp10_19,key_tmp10_20,key_tmp10_21,key_tmp10_22,key_tmp10_23,key_tmp10_24,key_tmp10_25,key_tmp10_26,key_tmp10_27,key_tmp10_28,key_tmp10_29,key_tmp10_30,key_tmp10_31,key_tmp10_32,key_tmp10_33,key_tmp10_34,key_tmp10_35,key_tmp10_36,key_tmp10_37,key_tmp10_38,key_tmp10_39,key_tmp10_40,key_tmp10_41,key_tmp10_42,key_tmp10_43,key_tmp10_44,key_tmp10_45,key_tmp10_46,key_tmp10_47,key_tmp10_48,key_tmp10_49,key_tmp10_50,key_tmp10_51,key_tmp10_52,key_tmp10_53,key_tmp10_54,key_tmp10_55,key_tmp10_56,key_tmp10_57,key_tmp10_58,key_tmp10_59,key_tmp10_60,key_tmp10_61,key_tmp10_62,key_tmp10_63,key_tmp10_64) = des_single9_ (id ((left9_1,left9_2,left9_3,left9_4,left9_5,left9_6,left9_7,left9_8,left9_9,left9_10,left9_11,left9_12,left9_13,left9_14,left9_15,left9_16,left9_17,left9_18,left9_19,left9_20,left9_21,left9_22,left9_23,left9_24,left9_25,left9_26,left9_27,left9_28,left9_29,left9_30,left9_31,left9_32),(right9_1,right9_2,right9_3,right9_4,right9_5,right9_6,right9_7,right9_8,right9_9,right9_10,right9_11,right9_12,right9_13,right9_14,right9_15,right9_16,right9_17,right9_18,right9_19,right9_20,right9_21,right9_22,right9_23,right9_24,right9_25,right9_26,right9_27,right9_28,right9_29,right9_30,right9_31,right9_32),(key_tmp9_1,key_tmp9_2,key_tmp9_3,key_tmp9_4,key_tmp9_5,key_tmp9_6,key_tmp9_7,key_tmp9_8,key_tmp9_9,key_tmp9_10,key_tmp9_11,key_tmp9_12,key_tmp9_13,key_tmp9_14,key_tmp9_15,key_tmp9_16,key_tmp9_17,key_tmp9_18,key_tmp9_19,key_tmp9_20,key_tmp9_21,key_tmp9_22,key_tmp9_23,key_tmp9_24,key_tmp9_25,key_tmp9_26,key_tmp9_27,key_tmp9_28,key_tmp9_29,key_tmp9_30,key_tmp9_31,key_tmp9_32,key_tmp9_33,key_tmp9_34,key_tmp9_35,key_tmp9_36,key_tmp9_37,key_tmp9_38,key_tmp9_39,key_tmp9_40,key_tmp9_41,key_tmp9_42,key_tmp9_43,key_tmp9_44,key_tmp9_45,key_tmp9_46,key_tmp9_47,key_tmp9_48,key_tmp9_49,key_tmp9_50,key_tmp9_51,key_tmp9_52,key_tmp9_53,key_tmp9_54,key_tmp9_55,key_tmp9_56,key_tmp9_57,key_tmp9_58,key_tmp9_59,key_tmp9_60,key_tmp9_61,key_tmp9_62,key_tmp9_63,key_tmp9_64))) in 
    let (left11_1,left11_2,left11_3,left11_4,left11_5,left11_6,left11_7,left11_8,left11_9,left11_10,left11_11,left11_12,left11_13,left11_14,left11_15,left11_16,left11_17,left11_18,left11_19,left11_20,left11_21,left11_22,left11_23,left11_24,left11_25,left11_26,left11_27,left11_28,left11_29,left11_30,left11_31,left11_32,right11_1,right11_2,right11_3,right11_4,right11_5,right11_6,right11_7,right11_8,right11_9,right11_10,right11_11,right11_12,right11_13,right11_14,right11_15,right11_16,right11_17,right11_18,right11_19,right11_20,right11_21,right11_22,right11_23,right11_24,right11_25,right11_26,right11_27,right11_28,right11_29,right11_30,right11_31,right11_32,key_tmp11_1,key_tmp11_2,key_tmp11_3,key_tmp11_4,key_tmp11_5,key_tmp11_6,key_tmp11_7,key_tmp11_8,key_tmp11_9,key_tmp11_10,key_tmp11_11,key_tmp11_12,key_tmp11_13,key_tmp11_14,key_tmp11_15,key_tmp11_16,key_tmp11_17,key_tmp11_18,key_tmp11_19,key_tmp11_20,key_tmp11_21,key_tmp11_22,key_tmp11_23,key_tmp11_24,key_tmp11_25,key_tmp11_26,key_tmp11_27,key_tmp11_28,key_tmp11_29,key_tmp11_30,key_tmp11_31,key_tmp11_32,key_tmp11_33,key_tmp11_34,key_tmp11_35,key_tmp11_36,key_tmp11_37,key_tmp11_38,key_tmp11_39,key_tmp11_40,key_tmp11_41,key_tmp11_42,key_tmp11_43,key_tmp11_44,key_tmp11_45,key_tmp11_46,key_tmp11_47,key_tmp11_48,key_tmp11_49,key_tmp11_50,key_tmp11_51,key_tmp11_52,key_tmp11_53,key_tmp11_54,key_tmp11_55,key_tmp11_56,key_tmp11_57,key_tmp11_58,key_tmp11_59,key_tmp11_60,key_tmp11_61,key_tmp11_62,key_tmp11_63,key_tmp11_64) = des_single10_ (id ((left10_1,left10_2,left10_3,left10_4,left10_5,left10_6,left10_7,left10_8,left10_9,left10_10,left10_11,left10_12,left10_13,left10_14,left10_15,left10_16,left10_17,left10_18,left10_19,left10_20,left10_21,left10_22,left10_23,left10_24,left10_25,left10_26,left10_27,left10_28,left10_29,left10_30,left10_31,left10_32),(right10_1,right10_2,right10_3,right10_4,right10_5,right10_6,right10_7,right10_8,right10_9,right10_10,right10_11,right10_12,right10_13,right10_14,right10_15,right10_16,right10_17,right10_18,right10_19,right10_20,right10_21,right10_22,right10_23,right10_24,right10_25,right10_26,right10_27,right10_28,right10_29,right10_30,right10_31,right10_32),(key_tmp10_1,key_tmp10_2,key_tmp10_3,key_tmp10_4,key_tmp10_5,key_tmp10_6,key_tmp10_7,key_tmp10_8,key_tmp10_9,key_tmp10_10,key_tmp10_11,key_tmp10_12,key_tmp10_13,key_tmp10_14,key_tmp10_15,key_tmp10_16,key_tmp10_17,key_tmp10_18,key_tmp10_19,key_tmp10_20,key_tmp10_21,key_tmp10_22,key_tmp10_23,key_tmp10_24,key_tmp10_25,key_tmp10_26,key_tmp10_27,key_tmp10_28,key_tmp10_29,key_tmp10_30,key_tmp10_31,key_tmp10_32,key_tmp10_33,key_tmp10_34,key_tmp10_35,key_tmp10_36,key_tmp10_37,key_tmp10_38,key_tmp10_39,key_tmp10_40,key_tmp10_41,key_tmp10_42,key_tmp10_43,key_tmp10_44,key_tmp10_45,key_tmp10_46,key_tmp10_47,key_tmp10_48,key_tmp10_49,key_tmp10_50,key_tmp10_51,key_tmp10_52,key_tmp10_53,key_tmp10_54,key_tmp10_55,key_tmp10_56,key_tmp10_57,key_tmp10_58,key_tmp10_59,key_tmp10_60,key_tmp10_61,key_tmp10_62,key_tmp10_63,key_tmp10_64))) in 
    let (left12_1,left12_2,left12_3,left12_4,left12_5,left12_6,left12_7,left12_8,left12_9,left12_10,left12_11,left12_12,left12_13,left12_14,left12_15,left12_16,left12_17,left12_18,left12_19,left12_20,left12_21,left12_22,left12_23,left12_24,left12_25,left12_26,left12_27,left12_28,left12_29,left12_30,left12_31,left12_32,right12_1,right12_2,right12_3,right12_4,right12_5,right12_6,right12_7,right12_8,right12_9,right12_10,right12_11,right12_12,right12_13,right12_14,right12_15,right12_16,right12_17,right12_18,right12_19,right12_20,right12_21,right12_22,right12_23,right12_24,right12_25,right12_26,right12_27,right12_28,right12_29,right12_30,right12_31,right12_32,key_tmp12_1,key_tmp12_2,key_tmp12_3,key_tmp12_4,key_tmp12_5,key_tmp12_6,key_tmp12_7,key_tmp12_8,key_tmp12_9,key_tmp12_10,key_tmp12_11,key_tmp12_12,key_tmp12_13,key_tmp12_14,key_tmp12_15,key_tmp12_16,key_tmp12_17,key_tmp12_18,key_tmp12_19,key_tmp12_20,key_tmp12_21,key_tmp12_22,key_tmp12_23,key_tmp12_24,key_tmp12_25,key_tmp12_26,key_tmp12_27,key_tmp12_28,key_tmp12_29,key_tmp12_30,key_tmp12_31,key_tmp12_32,key_tmp12_33,key_tmp12_34,key_tmp12_35,key_tmp12_36,key_tmp12_37,key_tmp12_38,key_tmp12_39,key_tmp12_40,key_tmp12_41,key_tmp12_42,key_tmp12_43,key_tmp12_44,key_tmp12_45,key_tmp12_46,key_tmp12_47,key_tmp12_48,key_tmp12_49,key_tmp12_50,key_tmp12_51,key_tmp12_52,key_tmp12_53,key_tmp12_54,key_tmp12_55,key_tmp12_56,key_tmp12_57,key_tmp12_58,key_tmp12_59,key_tmp12_60,key_tmp12_61,key_tmp12_62,key_tmp12_63,key_tmp12_64) = des_single11_ (id ((left11_1,left11_2,left11_3,left11_4,left11_5,left11_6,left11_7,left11_8,left11_9,left11_10,left11_11,left11_12,left11_13,left11_14,left11_15,left11_16,left11_17,left11_18,left11_19,left11_20,left11_21,left11_22,left11_23,left11_24,left11_25,left11_26,left11_27,left11_28,left11_29,left11_30,left11_31,left11_32),(right11_1,right11_2,right11_3,right11_4,right11_5,right11_6,right11_7,right11_8,right11_9,right11_10,right11_11,right11_12,right11_13,right11_14,right11_15,right11_16,right11_17,right11_18,right11_19,right11_20,right11_21,right11_22,right11_23,right11_24,right11_25,right11_26,right11_27,right11_28,right11_29,right11_30,right11_31,right11_32),(key_tmp11_1,key_tmp11_2,key_tmp11_3,key_tmp11_4,key_tmp11_5,key_tmp11_6,key_tmp11_7,key_tmp11_8,key_tmp11_9,key_tmp11_10,key_tmp11_11,key_tmp11_12,key_tmp11_13,key_tmp11_14,key_tmp11_15,key_tmp11_16,key_tmp11_17,key_tmp11_18,key_tmp11_19,key_tmp11_20,key_tmp11_21,key_tmp11_22,key_tmp11_23,key_tmp11_24,key_tmp11_25,key_tmp11_26,key_tmp11_27,key_tmp11_28,key_tmp11_29,key_tmp11_30,key_tmp11_31,key_tmp11_32,key_tmp11_33,key_tmp11_34,key_tmp11_35,key_tmp11_36,key_tmp11_37,key_tmp11_38,key_tmp11_39,key_tmp11_40,key_tmp11_41,key_tmp11_42,key_tmp11_43,key_tmp11_44,key_tmp11_45,key_tmp11_46,key_tmp11_47,key_tmp11_48,key_tmp11_49,key_tmp11_50,key_tmp11_51,key_tmp11_52,key_tmp11_53,key_tmp11_54,key_tmp11_55,key_tmp11_56,key_tmp11_57,key_tmp11_58,key_tmp11_59,key_tmp11_60,key_tmp11_61,key_tmp11_62,key_tmp11_63,key_tmp11_64))) in 
    let (left13_1,left13_2,left13_3,left13_4,left13_5,left13_6,left13_7,left13_8,left13_9,left13_10,left13_11,left13_12,left13_13,left13_14,left13_15,left13_16,left13_17,left13_18,left13_19,left13_20,left13_21,left13_22,left13_23,left13_24,left13_25,left13_26,left13_27,left13_28,left13_29,left13_30,left13_31,left13_32,right13_1,right13_2,right13_3,right13_4,right13_5,right13_6,right13_7,right13_8,right13_9,right13_10,right13_11,right13_12,right13_13,right13_14,right13_15,right13_16,right13_17,right13_18,right13_19,right13_20,right13_21,right13_22,right13_23,right13_24,right13_25,right13_26,right13_27,right13_28,right13_29,right13_30,right13_31,right13_32,key_tmp13_1,key_tmp13_2,key_tmp13_3,key_tmp13_4,key_tmp13_5,key_tmp13_6,key_tmp13_7,key_tmp13_8,key_tmp13_9,key_tmp13_10,key_tmp13_11,key_tmp13_12,key_tmp13_13,key_tmp13_14,key_tmp13_15,key_tmp13_16,key_tmp13_17,key_tmp13_18,key_tmp13_19,key_tmp13_20,key_tmp13_21,key_tmp13_22,key_tmp13_23,key_tmp13_24,key_tmp13_25,key_tmp13_26,key_tmp13_27,key_tmp13_28,key_tmp13_29,key_tmp13_30,key_tmp13_31,key_tmp13_32,key_tmp13_33,key_tmp13_34,key_tmp13_35,key_tmp13_36,key_tmp13_37,key_tmp13_38,key_tmp13_39,key_tmp13_40,key_tmp13_41,key_tmp13_42,key_tmp13_43,key_tmp13_44,key_tmp13_45,key_tmp13_46,key_tmp13_47,key_tmp13_48,key_tmp13_49,key_tmp13_50,key_tmp13_51,key_tmp13_52,key_tmp13_53,key_tmp13_54,key_tmp13_55,key_tmp13_56,key_tmp13_57,key_tmp13_58,key_tmp13_59,key_tmp13_60,key_tmp13_61,key_tmp13_62,key_tmp13_63,key_tmp13_64) = des_single12_ (id ((left12_1,left12_2,left12_3,left12_4,left12_5,left12_6,left12_7,left12_8,left12_9,left12_10,left12_11,left12_12,left12_13,left12_14,left12_15,left12_16,left12_17,left12_18,left12_19,left12_20,left12_21,left12_22,left12_23,left12_24,left12_25,left12_26,left12_27,left12_28,left12_29,left12_30,left12_31,left12_32),(right12_1,right12_2,right12_3,right12_4,right12_5,right12_6,right12_7,right12_8,right12_9,right12_10,right12_11,right12_12,right12_13,right12_14,right12_15,right12_16,right12_17,right12_18,right12_19,right12_20,right12_21,right12_22,right12_23,right12_24,right12_25,right12_26,right12_27,right12_28,right12_29,right12_30,right12_31,right12_32),(key_tmp12_1,key_tmp12_2,key_tmp12_3,key_tmp12_4,key_tmp12_5,key_tmp12_6,key_tmp12_7,key_tmp12_8,key_tmp12_9,key_tmp12_10,key_tmp12_11,key_tmp12_12,key_tmp12_13,key_tmp12_14,key_tmp12_15,key_tmp12_16,key_tmp12_17,key_tmp12_18,key_tmp12_19,key_tmp12_20,key_tmp12_21,key_tmp12_22,key_tmp12_23,key_tmp12_24,key_tmp12_25,key_tmp12_26,key_tmp12_27,key_tmp12_28,key_tmp12_29,key_tmp12_30,key_tmp12_31,key_tmp12_32,key_tmp12_33,key_tmp12_34,key_tmp12_35,key_tmp12_36,key_tmp12_37,key_tmp12_38,key_tmp12_39,key_tmp12_40,key_tmp12_41,key_tmp12_42,key_tmp12_43,key_tmp12_44,key_tmp12_45,key_tmp12_46,key_tmp12_47,key_tmp12_48,key_tmp12_49,key_tmp12_50,key_tmp12_51,key_tmp12_52,key_tmp12_53,key_tmp12_54,key_tmp12_55,key_tmp12_56,key_tmp12_57,key_tmp12_58,key_tmp12_59,key_tmp12_60,key_tmp12_61,key_tmp12_62,key_tmp12_63,key_tmp12_64))) in 
    let (left14_1,left14_2,left14_3,left14_4,left14_5,left14_6,left14_7,left14_8,left14_9,left14_10,left14_11,left14_12,left14_13,left14_14,left14_15,left14_16,left14_17,left14_18,left14_19,left14_20,left14_21,left14_22,left14_23,left14_24,left14_25,left14_26,left14_27,left14_28,left14_29,left14_30,left14_31,left14_32,right14_1,right14_2,right14_3,right14_4,right14_5,right14_6,right14_7,right14_8,right14_9,right14_10,right14_11,right14_12,right14_13,right14_14,right14_15,right14_16,right14_17,right14_18,right14_19,right14_20,right14_21,right14_22,right14_23,right14_24,right14_25,right14_26,right14_27,right14_28,right14_29,right14_30,right14_31,right14_32,key_tmp14_1,key_tmp14_2,key_tmp14_3,key_tmp14_4,key_tmp14_5,key_tmp14_6,key_tmp14_7,key_tmp14_8,key_tmp14_9,key_tmp14_10,key_tmp14_11,key_tmp14_12,key_tmp14_13,key_tmp14_14,key_tmp14_15,key_tmp14_16,key_tmp14_17,key_tmp14_18,key_tmp14_19,key_tmp14_20,key_tmp14_21,key_tmp14_22,key_tmp14_23,key_tmp14_24,key_tmp14_25,key_tmp14_26,key_tmp14_27,key_tmp14_28,key_tmp14_29,key_tmp14_30,key_tmp14_31,key_tmp14_32,key_tmp14_33,key_tmp14_34,key_tmp14_35,key_tmp14_36,key_tmp14_37,key_tmp14_38,key_tmp14_39,key_tmp14_40,key_tmp14_41,key_tmp14_42,key_tmp14_43,key_tmp14_44,key_tmp14_45,key_tmp14_46,key_tmp14_47,key_tmp14_48,key_tmp14_49,key_tmp14_50,key_tmp14_51,key_tmp14_52,key_tmp14_53,key_tmp14_54,key_tmp14_55,key_tmp14_56,key_tmp14_57,key_tmp14_58,key_tmp14_59,key_tmp14_60,key_tmp14_61,key_tmp14_62,key_tmp14_63,key_tmp14_64) = des_single13_ (id ((left13_1,left13_2,left13_3,left13_4,left13_5,left13_6,left13_7,left13_8,left13_9,left13_10,left13_11,left13_12,left13_13,left13_14,left13_15,left13_16,left13_17,left13_18,left13_19,left13_20,left13_21,left13_22,left13_23,left13_24,left13_25,left13_26,left13_27,left13_28,left13_29,left13_30,left13_31,left13_32),(right13_1,right13_2,right13_3,right13_4,right13_5,right13_6,right13_7,right13_8,right13_9,right13_10,right13_11,right13_12,right13_13,right13_14,right13_15,right13_16,right13_17,right13_18,right13_19,right13_20,right13_21,right13_22,right13_23,right13_24,right13_25,right13_26,right13_27,right13_28,right13_29,right13_30,right13_31,right13_32),(key_tmp13_1,key_tmp13_2,key_tmp13_3,key_tmp13_4,key_tmp13_5,key_tmp13_6,key_tmp13_7,key_tmp13_8,key_tmp13_9,key_tmp13_10,key_tmp13_11,key_tmp13_12,key_tmp13_13,key_tmp13_14,key_tmp13_15,key_tmp13_16,key_tmp13_17,key_tmp13_18,key_tmp13_19,key_tmp13_20,key_tmp13_21,key_tmp13_22,key_tmp13_23,key_tmp13_24,key_tmp13_25,key_tmp13_26,key_tmp13_27,key_tmp13_28,key_tmp13_29,key_tmp13_30,key_tmp13_31,key_tmp13_32,key_tmp13_33,key_tmp13_34,key_tmp13_35,key_tmp13_36,key_tmp13_37,key_tmp13_38,key_tmp13_39,key_tmp13_40,key_tmp13_41,key_tmp13_42,key_tmp13_43,key_tmp13_44,key_tmp13_45,key_tmp13_46,key_tmp13_47,key_tmp13_48,key_tmp13_49,key_tmp13_50,key_tmp13_51,key_tmp13_52,key_tmp13_53,key_tmp13_54,key_tmp13_55,key_tmp13_56,key_tmp13_57,key_tmp13_58,key_tmp13_59,key_tmp13_60,key_tmp13_61,key_tmp13_62,key_tmp13_63,key_tmp13_64))) in 
    let (left15_1,left15_2,left15_3,left15_4,left15_5,left15_6,left15_7,left15_8,left15_9,left15_10,left15_11,left15_12,left15_13,left15_14,left15_15,left15_16,left15_17,left15_18,left15_19,left15_20,left15_21,left15_22,left15_23,left15_24,left15_25,left15_26,left15_27,left15_28,left15_29,left15_30,left15_31,left15_32,right15_1,right15_2,right15_3,right15_4,right15_5,right15_6,right15_7,right15_8,right15_9,right15_10,right15_11,right15_12,right15_13,right15_14,right15_15,right15_16,right15_17,right15_18,right15_19,right15_20,right15_21,right15_22,right15_23,right15_24,right15_25,right15_26,right15_27,right15_28,right15_29,right15_30,right15_31,right15_32,key_tmp15_1,key_tmp15_2,key_tmp15_3,key_tmp15_4,key_tmp15_5,key_tmp15_6,key_tmp15_7,key_tmp15_8,key_tmp15_9,key_tmp15_10,key_tmp15_11,key_tmp15_12,key_tmp15_13,key_tmp15_14,key_tmp15_15,key_tmp15_16,key_tmp15_17,key_tmp15_18,key_tmp15_19,key_tmp15_20,key_tmp15_21,key_tmp15_22,key_tmp15_23,key_tmp15_24,key_tmp15_25,key_tmp15_26,key_tmp15_27,key_tmp15_28,key_tmp15_29,key_tmp15_30,key_tmp15_31,key_tmp15_32,key_tmp15_33,key_tmp15_34,key_tmp15_35,key_tmp15_36,key_tmp15_37,key_tmp15_38,key_tmp15_39,key_tmp15_40,key_tmp15_41,key_tmp15_42,key_tmp15_43,key_tmp15_44,key_tmp15_45,key_tmp15_46,key_tmp15_47,key_tmp15_48,key_tmp15_49,key_tmp15_50,key_tmp15_51,key_tmp15_52,key_tmp15_53,key_tmp15_54,key_tmp15_55,key_tmp15_56,key_tmp15_57,key_tmp15_58,key_tmp15_59,key_tmp15_60,key_tmp15_61,key_tmp15_62,key_tmp15_63,key_tmp15_64) = des_single14_ (id ((left14_1,left14_2,left14_3,left14_4,left14_5,left14_6,left14_7,left14_8,left14_9,left14_10,left14_11,left14_12,left14_13,left14_14,left14_15,left14_16,left14_17,left14_18,left14_19,left14_20,left14_21,left14_22,left14_23,left14_24,left14_25,left14_26,left14_27,left14_28,left14_29,left14_30,left14_31,left14_32),(right14_1,right14_2,right14_3,right14_4,right14_5,right14_6,right14_7,right14_8,right14_9,right14_10,right14_11,right14_12,right14_13,right14_14,right14_15,right14_16,right14_17,right14_18,right14_19,right14_20,right14_21,right14_22,right14_23,right14_24,right14_25,right14_26,right14_27,right14_28,right14_29,right14_30,right14_31,right14_32),(key_tmp14_1,key_tmp14_2,key_tmp14_3,key_tmp14_4,key_tmp14_5,key_tmp14_6,key_tmp14_7,key_tmp14_8,key_tmp14_9,key_tmp14_10,key_tmp14_11,key_tmp14_12,key_tmp14_13,key_tmp14_14,key_tmp14_15,key_tmp14_16,key_tmp14_17,key_tmp14_18,key_tmp14_19,key_tmp14_20,key_tmp14_21,key_tmp14_22,key_tmp14_23,key_tmp14_24,key_tmp14_25,key_tmp14_26,key_tmp14_27,key_tmp14_28,key_tmp14_29,key_tmp14_30,key_tmp14_31,key_tmp14_32,key_tmp14_33,key_tmp14_34,key_tmp14_35,key_tmp14_36,key_tmp14_37,key_tmp14_38,key_tmp14_39,key_tmp14_40,key_tmp14_41,key_tmp14_42,key_tmp14_43,key_tmp14_44,key_tmp14_45,key_tmp14_46,key_tmp14_47,key_tmp14_48,key_tmp14_49,key_tmp14_50,key_tmp14_51,key_tmp14_52,key_tmp14_53,key_tmp14_54,key_tmp14_55,key_tmp14_56,key_tmp14_57,key_tmp14_58,key_tmp14_59,key_tmp14_60,key_tmp14_61,key_tmp14_62,key_tmp14_63,key_tmp14_64))) in 
    let (left16_1,left16_2,left16_3,left16_4,left16_5,left16_6,left16_7,left16_8,left16_9,left16_10,left16_11,left16_12,left16_13,left16_14,left16_15,left16_16,left16_17,left16_18,left16_19,left16_20,left16_21,left16_22,left16_23,left16_24,left16_25,left16_26,left16_27,left16_28,left16_29,left16_30,left16_31,left16_32,right16_1,right16_2,right16_3,right16_4,right16_5,right16_6,right16_7,right16_8,right16_9,right16_10,right16_11,right16_12,right16_13,right16_14,right16_15,right16_16,right16_17,right16_18,right16_19,right16_20,right16_21,right16_22,right16_23,right16_24,right16_25,right16_26,right16_27,right16_28,right16_29,right16_30,right16_31,right16_32,key_tmp16_1,key_tmp16_2,key_tmp16_3,key_tmp16_4,key_tmp16_5,key_tmp16_6,key_tmp16_7,key_tmp16_8,key_tmp16_9,key_tmp16_10,key_tmp16_11,key_tmp16_12,key_tmp16_13,key_tmp16_14,key_tmp16_15,key_tmp16_16,key_tmp16_17,key_tmp16_18,key_tmp16_19,key_tmp16_20,key_tmp16_21,key_tmp16_22,key_tmp16_23,key_tmp16_24,key_tmp16_25,key_tmp16_26,key_tmp16_27,key_tmp16_28,key_tmp16_29,key_tmp16_30,key_tmp16_31,key_tmp16_32,key_tmp16_33,key_tmp16_34,key_tmp16_35,key_tmp16_36,key_tmp16_37,key_tmp16_38,key_tmp16_39,key_tmp16_40,key_tmp16_41,key_tmp16_42,key_tmp16_43,key_tmp16_44,key_tmp16_45,key_tmp16_46,key_tmp16_47,key_tmp16_48,key_tmp16_49,key_tmp16_50,key_tmp16_51,key_tmp16_52,key_tmp16_53,key_tmp16_54,key_tmp16_55,key_tmp16_56,key_tmp16_57,key_tmp16_58,key_tmp16_59,key_tmp16_60,key_tmp16_61,key_tmp16_62,key_tmp16_63,key_tmp16_64) = des_single15_ (id ((left15_1,left15_2,left15_3,left15_4,left15_5,left15_6,left15_7,left15_8,left15_9,left15_10,left15_11,left15_12,left15_13,left15_14,left15_15,left15_16,left15_17,left15_18,left15_19,left15_20,left15_21,left15_22,left15_23,left15_24,left15_25,left15_26,left15_27,left15_28,left15_29,left15_30,left15_31,left15_32),(right15_1,right15_2,right15_3,right15_4,right15_5,right15_6,right15_7,right15_8,right15_9,right15_10,right15_11,right15_12,right15_13,right15_14,right15_15,right15_16,right15_17,right15_18,right15_19,right15_20,right15_21,right15_22,right15_23,right15_24,right15_25,right15_26,right15_27,right15_28,right15_29,right15_30,right15_31,right15_32),(key_tmp15_1,key_tmp15_2,key_tmp15_3,key_tmp15_4,key_tmp15_5,key_tmp15_6,key_tmp15_7,key_tmp15_8,key_tmp15_9,key_tmp15_10,key_tmp15_11,key_tmp15_12,key_tmp15_13,key_tmp15_14,key_tmp15_15,key_tmp15_16,key_tmp15_17,key_tmp15_18,key_tmp15_19,key_tmp15_20,key_tmp15_21,key_tmp15_22,key_tmp15_23,key_tmp15_24,key_tmp15_25,key_tmp15_26,key_tmp15_27,key_tmp15_28,key_tmp15_29,key_tmp15_30,key_tmp15_31,key_tmp15_32,key_tmp15_33,key_tmp15_34,key_tmp15_35,key_tmp15_36,key_tmp15_37,key_tmp15_38,key_tmp15_39,key_tmp15_40,key_tmp15_41,key_tmp15_42,key_tmp15_43,key_tmp15_44,key_tmp15_45,key_tmp15_46,key_tmp15_47,key_tmp15_48,key_tmp15_49,key_tmp15_50,key_tmp15_51,key_tmp15_52,key_tmp15_53,key_tmp15_54,key_tmp15_55,key_tmp15_56,key_tmp15_57,key_tmp15_58,key_tmp15_59,key_tmp15_60,key_tmp15_61,key_tmp15_62,key_tmp15_63,key_tmp15_64))) in 
    let (left17_1,left17_2,left17_3,left17_4,left17_5,left17_6,left17_7,left17_8,left17_9,left17_10,left17_11,left17_12,left17_13,left17_14,left17_15,left17_16,left17_17,left17_18,left17_19,left17_20,left17_21,left17_22,left17_23,left17_24,left17_25,left17_26,left17_27,left17_28,left17_29,left17_30,left17_31,left17_32,right17_1,right17_2,right17_3,right17_4,right17_5,right17_6,right17_7,right17_8,right17_9,right17_10,right17_11,right17_12,right17_13,right17_14,right17_15,right17_16,right17_17,right17_18,right17_19,right17_20,right17_21,right17_22,right17_23,right17_24,right17_25,right17_26,right17_27,right17_28,right17_29,right17_30,right17_31,right17_32,key_tmp17_1,key_tmp17_2,key_tmp17_3,key_tmp17_4,key_tmp17_5,key_tmp17_6,key_tmp17_7,key_tmp17_8,key_tmp17_9,key_tmp17_10,key_tmp17_11,key_tmp17_12,key_tmp17_13,key_tmp17_14,key_tmp17_15,key_tmp17_16,key_tmp17_17,key_tmp17_18,key_tmp17_19,key_tmp17_20,key_tmp17_21,key_tmp17_22,key_tmp17_23,key_tmp17_24,key_tmp17_25,key_tmp17_26,key_tmp17_27,key_tmp17_28,key_tmp17_29,key_tmp17_30,key_tmp17_31,key_tmp17_32,key_tmp17_33,key_tmp17_34,key_tmp17_35,key_tmp17_36,key_tmp17_37,key_tmp17_38,key_tmp17_39,key_tmp17_40,key_tmp17_41,key_tmp17_42,key_tmp17_43,key_tmp17_44,key_tmp17_45,key_tmp17_46,key_tmp17_47,key_tmp17_48,key_tmp17_49,key_tmp17_50,key_tmp17_51,key_tmp17_52,key_tmp17_53,key_tmp17_54,key_tmp17_55,key_tmp17_56,key_tmp17_57,key_tmp17_58,key_tmp17_59,key_tmp17_60,key_tmp17_61,key_tmp17_62,key_tmp17_63,key_tmp17_64) = des_single16_ (id ((left16_1,left16_2,left16_3,left16_4,left16_5,left16_6,left16_7,left16_8,left16_9,left16_10,left16_11,left16_12,left16_13,left16_14,left16_15,left16_16,left16_17,left16_18,left16_19,left16_20,left16_21,left16_22,left16_23,left16_24,left16_25,left16_26,left16_27,left16_28,left16_29,left16_30,left16_31,left16_32),(right16_1,right16_2,right16_3,right16_4,right16_5,right16_6,right16_7,right16_8,right16_9,right16_10,right16_11,right16_12,right16_13,right16_14,right16_15,right16_16,right16_17,right16_18,right16_19,right16_20,right16_21,right16_22,right16_23,right16_24,right16_25,right16_26,right16_27,right16_28,right16_29,right16_30,right16_31,right16_32),(key_tmp16_1,key_tmp16_2,key_tmp16_3,key_tmp16_4,key_tmp16_5,key_tmp16_6,key_tmp16_7,key_tmp16_8,key_tmp16_9,key_tmp16_10,key_tmp16_11,key_tmp16_12,key_tmp16_13,key_tmp16_14,key_tmp16_15,key_tmp16_16,key_tmp16_17,key_tmp16_18,key_tmp16_19,key_tmp16_20,key_tmp16_21,key_tmp16_22,key_tmp16_23,key_tmp16_24,key_tmp16_25,key_tmp16_26,key_tmp16_27,key_tmp16_28,key_tmp16_29,key_tmp16_30,key_tmp16_31,key_tmp16_32,key_tmp16_33,key_tmp16_34,key_tmp16_35,key_tmp16_36,key_tmp16_37,key_tmp16_38,key_tmp16_39,key_tmp16_40,key_tmp16_41,key_tmp16_42,key_tmp16_43,key_tmp16_44,key_tmp16_45,key_tmp16_46,key_tmp16_47,key_tmp16_48,key_tmp16_49,key_tmp16_50,key_tmp16_51,key_tmp16_52,key_tmp16_53,key_tmp16_54,key_tmp16_55,key_tmp16_56,key_tmp16_57,key_tmp16_58,key_tmp16_59,key_tmp16_60,key_tmp16_61,key_tmp16_62,key_tmp16_63,key_tmp16_64))) in 
    let (ciphered_1,ciphered_2,ciphered_3,ciphered_4,ciphered_5,ciphered_6,ciphered_7,ciphered_8,ciphered_9,ciphered_10,ciphered_11,ciphered_12,ciphered_13,ciphered_14,ciphered_15,ciphered_16,ciphered_17,ciphered_18,ciphered_19,ciphered_20,ciphered_21,ciphered_22,ciphered_23,ciphered_24,ciphered_25,ciphered_26,ciphered_27,ciphered_28,ciphered_29,ciphered_30,ciphered_31,ciphered_32,ciphered_33,ciphered_34,ciphered_35,ciphered_36,ciphered_37,ciphered_38,ciphered_39,ciphered_40,ciphered_41,ciphered_42,ciphered_43,ciphered_44,ciphered_45,ciphered_46,ciphered_47,ciphered_48,ciphered_49,ciphered_50,ciphered_51,ciphered_52,ciphered_53,ciphered_54,ciphered_55,ciphered_56,ciphered_57,ciphered_58,ciphered_59,ciphered_60,ciphered_61,ciphered_62,ciphered_63,ciphered_64) = final_p_ (convert7 ((right17_1,right17_2,right17_3,right17_4,right17_5,right17_6,right17_7,right17_8,right17_9,right17_10,right17_11,right17_12,right17_13,right17_14,right17_15,right17_16,right17_17,right17_18,right17_19,right17_20,right17_21,right17_22,right17_23,right17_24,right17_25,right17_26,right17_27,right17_28,right17_29,right17_30,right17_31,right17_32),(left17_1,left17_2,left17_3,left17_4,left17_5,left17_6,left17_7,left17_8,left17_9,left17_10,left17_11,left17_12,left17_13,left17_14,left17_15,left17_16,left17_17,left17_18,left17_19,left17_20,left17_21,left17_22,left17_23,left17_24,left17_25,left17_26,left17_27,left17_28,left17_29,left17_30,left17_31,left17_32))) in 
    (ciphered_1,ciphered_2,ciphered_3,ciphered_4,ciphered_5,ciphered_6,ciphered_7,ciphered_8,ciphered_9,ciphered_10,ciphered_11,ciphered_12,ciphered_13,ciphered_14,ciphered_15,ciphered_16,ciphered_17,ciphered_18,ciphered_19,ciphered_20,ciphered_21,ciphered_22,ciphered_23,ciphered_24,ciphered_25,ciphered_26,ciphered_27,ciphered_28,ciphered_29,ciphered_30,ciphered_31,ciphered_32,ciphered_33,ciphered_34,ciphered_35,ciphered_36,ciphered_37,ciphered_38,ciphered_39,ciphered_40,ciphered_41,ciphered_42,ciphered_43,ciphered_44,ciphered_45,ciphered_46,ciphered_47,ciphered_48,ciphered_49,ciphered_50,ciphered_51,ciphered_52,ciphered_53,ciphered_54,ciphered_55,ciphered_56,ciphered_57,ciphered_58,ciphered_59,ciphered_60,ciphered_61,ciphered_62,ciphered_63,ciphered_64)


let main plaintext_stream key_stream = 
  let cpt = ref 64 in
  let stack_ciphered_ = ref [| |] in
  Stream.from
    (fun _ -> 
    if !cpt < 63 then let ret = (!stack_ciphered_.(!cpt)) in
                          incr cpt;
                          Some ret
    else
      try
        let plaintext_ = Array.make 63 Int64.zero in
        for i = 0 to 62 do
          plaintext_.(i) <- Stream.next plaintext_stream
        done;
        let plaintext_' = convert_ortho 64 plaintext_ in
        let (plaintext_1,plaintext_2,plaintext_3,plaintext_4,plaintext_5,plaintext_6,plaintext_7,plaintext_8,plaintext_9,plaintext_10,plaintext_11,plaintext_12,plaintext_13,plaintext_14,plaintext_15,plaintext_16,plaintext_17,plaintext_18,plaintext_19,plaintext_20,plaintext_21,plaintext_22,plaintext_23,plaintext_24,plaintext_25,plaintext_26,plaintext_27,plaintext_28,plaintext_29,plaintext_30,plaintext_31,plaintext_32,plaintext_33,plaintext_34,plaintext_35,plaintext_36,plaintext_37,plaintext_38,plaintext_39,plaintext_40,plaintext_41,plaintext_42,plaintext_43,plaintext_44,plaintext_45,plaintext_46,plaintext_47,plaintext_48,plaintext_49,plaintext_50,plaintext_51,plaintext_52,plaintext_53,plaintext_54,plaintext_55,plaintext_56,plaintext_57,plaintext_58,plaintext_59,plaintext_60,plaintext_61,plaintext_62,plaintext_63,plaintext_64) = (plaintext_'.(63),plaintext_'.(62),plaintext_'.(61),plaintext_'.(60),plaintext_'.(59),plaintext_'.(58),plaintext_'.(57),plaintext_'.(56),plaintext_'.(55),plaintext_'.(54),plaintext_'.(53),plaintext_'.(52),plaintext_'.(51),plaintext_'.(50),plaintext_'.(49),plaintext_'.(48),plaintext_'.(47),plaintext_'.(46),plaintext_'.(45),plaintext_'.(44),plaintext_'.(43),plaintext_'.(42),plaintext_'.(41),plaintext_'.(40),plaintext_'.(39),plaintext_'.(38),plaintext_'.(37),plaintext_'.(36),plaintext_'.(35),plaintext_'.(34),plaintext_'.(33),plaintext_'.(32),plaintext_'.(31),plaintext_'.(30),plaintext_'.(29),plaintext_'.(28),plaintext_'.(27),plaintext_'.(26),plaintext_'.(25),plaintext_'.(24),plaintext_'.(23),plaintext_'.(22),plaintext_'.(21),plaintext_'.(20),plaintext_'.(19),plaintext_'.(18),plaintext_'.(17),plaintext_'.(16),plaintext_'.(15),plaintext_'.(14),plaintext_'.(13),plaintext_'.(12),plaintext_'.(11),plaintext_'.(10),plaintext_'.(9),plaintext_'.(8),plaintext_'.(7),plaintext_'.(6),plaintext_'.(5),plaintext_'.(4),plaintext_'.(3),plaintext_'.(2),plaintext_'.(1),plaintext_'.(0)) in

        let key_ = Array.make 63 Int64.zero in
        for i = 0 to 62 do
          key_.(i) <- Stream.next key_stream
        done;
        let key_' = convert_ortho 64 key_ in
        let (key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64) = (key_'.(63),key_'.(62),key_'.(61),key_'.(60),key_'.(59),key_'.(58),key_'.(57),key_'.(56),key_'.(55),key_'.(54),key_'.(53),key_'.(52),key_'.(51),key_'.(50),key_'.(49),key_'.(48),key_'.(47),key_'.(46),key_'.(45),key_'.(44),key_'.(43),key_'.(42),key_'.(41),key_'.(40),key_'.(39),key_'.(38),key_'.(37),key_'.(36),key_'.(35),key_'.(34),key_'.(33),key_'.(32),key_'.(31),key_'.(30),key_'.(29),key_'.(28),key_'.(27),key_'.(26),key_'.(25),key_'.(24),key_'.(23),key_'.(22),key_'.(21),key_'.(20),key_'.(19),key_'.(18),key_'.(17),key_'.(16),key_'.(15),key_'.(14),key_'.(13),key_'.(12),key_'.(11),key_'.(10),key_'.(9),key_'.(8),key_'.(7),key_'.(6),key_'.(5),key_'.(4),key_'.(3),key_'.(2),key_'.(1),key_'.(0)) in
        let (ret1,ret2,ret3,ret4,ret5,ret6,ret7,ret8,ret9,ret10,ret11,ret12,ret13,ret14,ret15,ret16,ret17,ret18,ret19,ret20,ret21,ret22,ret23,ret24,ret25,ret26,ret27,ret28,ret29,ret30,ret31,ret32,ret33,ret34,ret35,ret36,ret37,ret38,ret39,ret40,ret41,ret42,ret43,ret44,ret45,ret46,ret47,ret48,ret49,ret50,ret51,ret52,ret53,ret54,ret55,ret56,ret57,ret58,ret59,ret60,ret61,ret62,ret63,ret64) = des_((plaintext_1,plaintext_2,plaintext_3,plaintext_4,plaintext_5,plaintext_6,plaintext_7,plaintext_8,plaintext_9,plaintext_10,plaintext_11,plaintext_12,plaintext_13,plaintext_14,plaintext_15,plaintext_16,plaintext_17,plaintext_18,plaintext_19,plaintext_20,plaintext_21,plaintext_22,plaintext_23,plaintext_24,plaintext_25,plaintext_26,plaintext_27,plaintext_28,plaintext_29,plaintext_30,plaintext_31,plaintext_32,plaintext_33,plaintext_34,plaintext_35,plaintext_36,plaintext_37,plaintext_38,plaintext_39,plaintext_40,plaintext_41,plaintext_42,plaintext_43,plaintext_44,plaintext_45,plaintext_46,plaintext_47,plaintext_48,plaintext_49,plaintext_50,plaintext_51,plaintext_52,plaintext_53,plaintext_54,plaintext_55,plaintext_56,plaintext_57,plaintext_58,plaintext_59,plaintext_60,plaintext_61,plaintext_62,plaintext_63,plaintext_64),(key_1,key_2,key_3,key_4,key_5,key_6,key_7,key_8,key_9,key_10,key_11,key_12,key_13,key_14,key_15,key_16,key_17,key_18,key_19,key_20,key_21,key_22,key_23,key_24,key_25,key_26,key_27,key_28,key_29,key_30,key_31,key_32,key_33,key_34,key_35,key_36,key_37,key_38,key_39,key_40,key_41,key_42,key_43,key_44,key_45,key_46,key_47,key_48,key_49,key_50,key_51,key_52,key_53,key_54,key_55,key_56,key_57,key_58,key_59,key_60,key_61,key_62,key_63,key_64)) in
        let ciphered_ = Array.make 64 0 in
        ciphered_.(0) <- ret64;
        ciphered_.(1) <- ret63;
        ciphered_.(2) <- ret62;
        ciphered_.(3) <- ret61;
        ciphered_.(4) <- ret60;
        ciphered_.(5) <- ret59;
        ciphered_.(6) <- ret58;
        ciphered_.(7) <- ret57;
        ciphered_.(8) <- ret56;
        ciphered_.(9) <- ret55;
        ciphered_.(10) <- ret54;
        ciphered_.(11) <- ret53;
        ciphered_.(12) <- ret52;
        ciphered_.(13) <- ret51;
        ciphered_.(14) <- ret50;
        ciphered_.(15) <- ret49;
        ciphered_.(16) <- ret48;
        ciphered_.(17) <- ret47;
        ciphered_.(18) <- ret46;
        ciphered_.(19) <- ret45;
        ciphered_.(20) <- ret44;
        ciphered_.(21) <- ret43;
        ciphered_.(22) <- ret42;
        ciphered_.(23) <- ret41;
        ciphered_.(24) <- ret40;
        ciphered_.(25) <- ret39;
        ciphered_.(26) <- ret38;
        ciphered_.(27) <- ret37;
        ciphered_.(28) <- ret36;
        ciphered_.(29) <- ret35;
        ciphered_.(30) <- ret34;
        ciphered_.(31) <- ret33;
        ciphered_.(32) <- ret32;
        ciphered_.(33) <- ret31;
        ciphered_.(34) <- ret30;
        ciphered_.(35) <- ret29;
        ciphered_.(36) <- ret28;
        ciphered_.(37) <- ret27;
        ciphered_.(38) <- ret26;
        ciphered_.(39) <- ret25;
        ciphered_.(40) <- ret24;
        ciphered_.(41) <- ret23;
        ciphered_.(42) <- ret22;
        ciphered_.(43) <- ret21;
        ciphered_.(44) <- ret20;
        ciphered_.(45) <- ret19;
        ciphered_.(46) <- ret18;
        ciphered_.(47) <- ret17;
        ciphered_.(48) <- ret16;
        ciphered_.(49) <- ret15;
        ciphered_.(50) <- ret14;
        ciphered_.(51) <- ret13;
        ciphered_.(52) <- ret12;
        ciphered_.(53) <- ret11;
        ciphered_.(54) <- ret10;
        ciphered_.(55) <- ret9;
        ciphered_.(56) <- ret8;
        ciphered_.(57) <- ret7;
        ciphered_.(58) <- ret6;
        ciphered_.(59) <- ret5;
        ciphered_.(60) <- ret4;
        ciphered_.(61) <- ret3;
        ciphered_.(62) <- ret2;
        ciphered_.(63) <- ret1;
        stack_ciphered_ := convert_unortho ciphered_;

        cpt := 0;
        let return = Some (!stack_ciphered_.(!cpt)) in 
        incr cpt;
        return
      with Stream.Failure -> None)
