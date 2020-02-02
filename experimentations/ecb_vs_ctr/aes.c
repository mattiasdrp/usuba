/* This code was generated by Usuba.
   See https://github.com/DadaIsCrazy/usuba.
   From the file "samples/usuba/aes_mslice.ua" (included below). */

#include <stdint.h>

/* Do NOT change the order of those define/include */

#ifndef BITS_PER_REG
#define BITS_PER_REG 128
#endif
/* including the architecture specific .h */
#include "SSE.h"

/* auxiliary functions */
void SubBytes__H16 (/*inputs*/ DATATYPE U0__,DATATYPE U1__,DATATYPE U2__,DATATYPE U3__,DATATYPE U4__,DATATYPE U5__,DATATYPE U6__,DATATYPE U7__, /*outputs*/ DATATYPE* S0__,DATATYPE* S1__,DATATYPE* S2__,DATATYPE* S3__,DATATYPE* S4__,DATATYPE* S5__,DATATYPE* S6__,DATATYPE* S7__) {

  // Variables declaration
  DATATYPE _tmp1_;
  DATATYPE _tmp2_;
  DATATYPE _tmp3_;
  DATATYPE _tmp4_;
  DATATYPE t0__;
  DATATYPE t1__;
  DATATYPE t10__;
  DATATYPE t11__;
  DATATYPE t12__;
  DATATYPE t13__;
  DATATYPE t14__;
  DATATYPE t15__;
  DATATYPE t16__;
  DATATYPE t17__;
  DATATYPE t18__;
  DATATYPE t19__;
  DATATYPE t2__;
  DATATYPE t20__;
  DATATYPE t21__;
  DATATYPE t22__;
  DATATYPE t23__;
  DATATYPE t24__;
  DATATYPE t25__;
  DATATYPE t26__;
  DATATYPE t27__;
  DATATYPE t28__;
  DATATYPE t29__;
  DATATYPE t3__;
  DATATYPE t30__;
  DATATYPE t31__;
  DATATYPE t32__;
  DATATYPE t33__;
  DATATYPE t34__;
  DATATYPE t35__;
  DATATYPE t36__;
  DATATYPE t37__;
  DATATYPE t38__;
  DATATYPE t39__;
  DATATYPE t4__;
  DATATYPE t40__;
  DATATYPE t41__;
  DATATYPE t42__;
  DATATYPE t43__;
  DATATYPE t44__;
  DATATYPE t45__;
  DATATYPE t5__;
  DATATYPE t6__;
  DATATYPE t7__;
  DATATYPE t8__;
  DATATYPE t9__;
  DATATYPE tc1__;
  DATATYPE tc10__;
  DATATYPE tc11__;
  DATATYPE tc12__;
  DATATYPE tc13__;
  DATATYPE tc14__;
  DATATYPE tc16__;
  DATATYPE tc17__;
  DATATYPE tc18__;
  DATATYPE tc2__;
  DATATYPE tc20__;
  DATATYPE tc21__;
  DATATYPE tc26__;
  DATATYPE tc3__;
  DATATYPE tc4__;
  DATATYPE tc5__;
  DATATYPE tc6__;
  DATATYPE tc7__;
  DATATYPE tc8__;
  DATATYPE tc9__;
  DATATYPE y1__;
  DATATYPE y10__;
  DATATYPE y11__;
  DATATYPE y12__;
  DATATYPE y13__;
  DATATYPE y14__;
  DATATYPE y15__;
  DATATYPE y16__;
  DATATYPE y17__;
  DATATYPE y18__;
  DATATYPE y19__;
  DATATYPE y2__;
  DATATYPE y20__;
  DATATYPE y21__;
  DATATYPE y3__;
  DATATYPE y4__;
  DATATYPE y5__;
  DATATYPE y6__;
  DATATYPE y7__;
  DATATYPE y8__;
  DATATYPE y9__;
  DATATYPE z0__;
  DATATYPE z1__;
  DATATYPE z10__;
  DATATYPE z11__;
  DATATYPE z12__;
  DATATYPE z13__;
  DATATYPE z14__;
  DATATYPE z15__;
  DATATYPE z16__;
  DATATYPE z17__;
  DATATYPE z2__;
  DATATYPE z3__;
  DATATYPE z4__;
  DATATYPE z5__;
  DATATYPE z6__;
  DATATYPE z7__;
  DATATYPE z8__;
  DATATYPE z9__;

  // Instructions (body)
  y14__ = XOR(U3__,U5__);
  y13__ = XOR(U0__,U6__);
  y9__ = XOR(U0__,U3__);
  y8__ = XOR(U0__,U5__);
  t0__ = XOR(U1__,U2__);
  y12__ = XOR(y13__,y14__);
  y1__ = XOR(t0__,U7__);
  t1__ = XOR(U4__,y12__);
  y4__ = XOR(y1__,U3__);
  y2__ = XOR(y1__,U0__);
  y5__ = XOR(y1__,U6__);
  y15__ = XOR(t1__,U5__);
  y20__ = XOR(t1__,U1__);
  t5__ = AND(y4__,U7__);
  y3__ = XOR(y5__,y8__);
  t8__ = AND(y5__,y1__);
  y6__ = XOR(y15__,U7__);
  y10__ = XOR(y15__,t0__);
  t2__ = AND(y12__,y15__);
  y11__ = XOR(y20__,y9__);
  t3__ = AND(y3__,y6__);
  y19__ = XOR(y10__,y8__);
  t15__ = AND(y8__,y10__);
  t6__ = XOR(t5__,t2__);
  y7__ = XOR(U7__,y11__);
  y17__ = XOR(y10__,y11__);
  y16__ = XOR(t0__,y11__);
  t12__ = AND(y9__,y11__);
  t4__ = XOR(t3__,t2__);
  t10__ = AND(y2__,y7__);
  t13__ = AND(y14__,y17__);
  y21__ = XOR(y13__,y16__);
  y18__ = XOR(U0__,y16__);
  t7__ = AND(y13__,y16__);
  t16__ = XOR(t15__,t12__);
  t17__ = XOR(t4__,y20__);
  t14__ = XOR(t13__,t12__);
  t9__ = XOR(t8__,t7__);
  t11__ = XOR(t10__,t7__);
  t18__ = XOR(t6__,t16__);
  t21__ = XOR(t17__,t14__);
  t19__ = XOR(t9__,t14__);
  t20__ = XOR(t11__,t16__);
  t22__ = XOR(t18__,y19__);
  t23__ = XOR(t19__,y21__);
  t24__ = XOR(t20__,y18__);
  t25__ = XOR(t21__,t22__);
  t26__ = AND(t21__,t23__);
  t30__ = XOR(t23__,t24__);
  t27__ = XOR(t24__,t26__);
  t31__ = XOR(t22__,t26__);
  t28__ = AND(t25__,t27__);
  t32__ = AND(t31__,t30__);
  t29__ = XOR(t28__,t22__);
  t33__ = XOR(t32__,t24__);
  z5__ = AND(t29__,y7__);
  z14__ = AND(t29__,y2__);
  t34__ = XOR(t23__,t33__);
  t35__ = XOR(t27__,t33__);
  t42__ = XOR(t29__,t33__);
  z2__ = AND(t33__,U7__);
  z11__ = AND(t33__,y4__);
  t36__ = AND(t24__,t35__);
  z6__ = AND(t42__,y11__);
  z15__ = AND(t42__,y9__);
  t37__ = XOR(t36__,t34__);
  t38__ = XOR(t27__,t36__);
  t44__ = XOR(t33__,t37__);
  z1__ = AND(t37__,y6__);
  z10__ = AND(t37__,y3__);
  t39__ = AND(t29__,t38__);
  z0__ = AND(t44__,y15__);
  z9__ = AND(t44__,y12__);
  t40__ = XOR(t25__,t39__);
  tc4__ = XOR(z0__,z2__);
  tc5__ = XOR(z1__,z0__);
  t41__ = XOR(t40__,t37__);
  t43__ = XOR(t29__,t40__);
  z4__ = AND(t40__,y1__);
  z13__ = AND(t40__,y5__);
  t45__ = XOR(t42__,t41__);
  z8__ = AND(t41__,y10__);
  z17__ = AND(t41__,y8__);
  z3__ = AND(t43__,y16__);
  z12__ = AND(t43__,y13__);
  z7__ = AND(t45__,y17__);
  z16__ = AND(t45__,y14__);
  tc6__ = XOR(z3__,z4__);
  tc12__ = XOR(z3__,z5__);
  tc7__ = XOR(z12__,tc4__);
  tc1__ = XOR(z15__,z16__);
  tc8__ = XOR(z7__,tc6__);
  tc11__ = XOR(tc6__,tc5__);
  tc14__ = XOR(tc4__,tc12__);
  tc9__ = XOR(z8__,tc7__);
  tc2__ = XOR(z10__,tc1__);
  tc13__ = XOR(z13__,tc1__);
  tc16__ = XOR(z6__,tc8__);
  tc10__ = XOR(tc8__,tc9__);
  tc3__ = XOR(z9__,tc2__);
  tc21__ = XOR(tc2__,z11__);
  tc18__ = XOR(tc13__,tc14__);
  tc20__ = XOR(z15__,tc16__);
  tc17__ = XOR(z14__,tc10__);
  *S3__ = XOR(tc3__,tc11__);
  *S0__ = XOR(tc3__,tc16__);
  _tmp1_ = XOR(z12__,tc18__);
  _tmp2_ = XOR(tc10__,tc18__);
  tc26__ = XOR(tc17__,tc20__);
  *S5__ = XOR(tc21__,tc17__);
  *S4__ = XOR(tc14__,*S3__);
  _tmp3_ = XOR(*S3__,tc16__);
  *S7__ = NOT(_tmp1_);
  *S6__ = NOT(_tmp2_);
  _tmp4_ = XOR(tc26__,z17__);
  *S1__ = NOT(_tmp3_);
  *S2__ = NOT(_tmp4_);

}

/* main function */
void AES__ (/*inputs*/ DATATYPE plain__[8],DATATYPE key__[11][8], /*outputs*/ DATATYPE cipher__[8]) {

  // Variables declaration
  DATATYPE MixColumn__H16_1_RL32__H16_1__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_2__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_3__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_4__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_5__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_6__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_7__tmp163_;
  DATATYPE MixColumn__H16_1_RL32__H16_8__tmp163_;
  DATATYPE MixColumn__H16_1_RL64__H16_1__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_2__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_3__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_4__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_5__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_6__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_7__tmp164_;
  DATATYPE MixColumn__H16_1_RL64__H16_8__tmp164_;
  DATATYPE MixColumn__H16_1__tmp16_;
  DATATYPE MixColumn__H16_1__tmp18_;
  DATATYPE MixColumn__H16_1__tmp20_;
  DATATYPE MixColumn__H16_1__tmp26_;
  DATATYPE MixColumn__H16_1__tmp28_;
  DATATYPE MixColumn__H16_1__tmp30_;
  DATATYPE MixColumn__H16_1__tmp35_;
  DATATYPE MixColumn__H16_1__tmp37_;
  DATATYPE MixColumn__H16_1__tmp43_;
  DATATYPE MixColumn__H16_1__tmp45_;
  DATATYPE MixColumn__H16_1__tmp47_;
  DATATYPE MixColumn__H16_1__tmp53_;
  DATATYPE MixColumn__H16_1__tmp55_;
  DATATYPE MixColumn__H16_1__tmp57_;
  DATATYPE MixColumn__H16_1__tmp62_;
  DATATYPE MixColumn__H16_1__tmp64_;
  DATATYPE MixColumn__H16_1__tmp69_;
  DATATYPE MixColumn__H16_1__tmp71_;
  DATATYPE MixColumn__H16_1__tmp76_;
  DATATYPE ShiftRows__H16_1__tmp155_;
  DATATYPE ShiftRows__H16_1__tmp156_;
  DATATYPE ShiftRows__H16_1__tmp157_;
  DATATYPE ShiftRows__H16_1__tmp158_;
  DATATYPE ShiftRows__H16_1__tmp159_;
  DATATYPE ShiftRows__H16_1__tmp160_;
  DATATYPE ShiftRows__H16_1__tmp161_;
  DATATYPE ShiftRows__H16_1__tmp162_;
  DATATYPE _tmp80_[8];
  DATATYPE _tmp81_[8];
  DATATYPE _tmp82_[8];
  DATATYPE _tmp83_[8];
  DATATYPE tmp__[8];

  // Instructions (body)
  tmp__[0] = XOR(plain__[0],key__[0][0]);
  tmp__[1] = XOR(plain__[1],key__[0][1]);
  tmp__[2] = XOR(plain__[2],key__[0][2]);
  tmp__[3] = XOR(plain__[3],key__[0][3]);
  tmp__[4] = XOR(plain__[4],key__[0][4]);
  tmp__[5] = XOR(plain__[5],key__[0][5]);
  tmp__[6] = XOR(plain__[6],key__[0][6]);
  tmp__[7] = XOR(plain__[7],key__[0][7]);
  for (int i__ = 1; i__ <= 9; i__++) {
    SubBytes__H16(tmp__[0],tmp__[1],tmp__[2],tmp__[3],tmp__[4],tmp__[5],tmp__[6],tmp__[7],&_tmp80_[0],&_tmp80_[1],&_tmp80_[2],&_tmp80_[3],&_tmp80_[4],&_tmp80_[5],&_tmp80_[6],&_tmp80_[7]);
    ShiftRows__H16_1__tmp155_ = PERMUT_16(_tmp80_[0],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp156_ = PERMUT_16(_tmp80_[1],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp157_ = PERMUT_16(_tmp80_[2],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp158_ = PERMUT_16(_tmp80_[3],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp159_ = PERMUT_16(_tmp80_[4],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp160_ = PERMUT_16(_tmp80_[5],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp161_ = PERMUT_16(_tmp80_[6],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    ShiftRows__H16_1__tmp162_ = PERMUT_16(_tmp80_[7],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
    _tmp81_[0] = ShiftRows__H16_1__tmp155_;
    _tmp81_[1] = ShiftRows__H16_1__tmp156_;
    _tmp81_[2] = ShiftRows__H16_1__tmp157_;
    _tmp81_[3] = ShiftRows__H16_1__tmp158_;
    _tmp81_[4] = ShiftRows__H16_1__tmp159_;
    _tmp81_[5] = ShiftRows__H16_1__tmp160_;
    _tmp81_[6] = ShiftRows__H16_1__tmp161_;
    _tmp81_[7] = ShiftRows__H16_1__tmp162_;
    MixColumn__H16_1_RL32__H16_1__tmp163_ = PERMUT_16(_tmp81_[0],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_8__tmp163_ = PERMUT_16(_tmp81_[1],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_7__tmp163_ = PERMUT_16(_tmp81_[2],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_6__tmp163_ = PERMUT_16(_tmp81_[3],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_5__tmp163_ = PERMUT_16(_tmp81_[4],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_4__tmp163_ = PERMUT_16(_tmp81_[5],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_3__tmp163_ = PERMUT_16(_tmp81_[6],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1_RL32__H16_2__tmp163_ = PERMUT_16(_tmp81_[7],1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12);
    MixColumn__H16_1__tmp16_ = XOR(_tmp81_[0],MixColumn__H16_1_RL32__H16_1__tmp163_);
    MixColumn__H16_1__tmp71_ = XOR(_tmp81_[1],MixColumn__H16_1_RL32__H16_8__tmp163_);
    MixColumn__H16_1__tmp64_ = XOR(_tmp81_[2],MixColumn__H16_1_RL32__H16_7__tmp163_);
    MixColumn__H16_1__tmp57_ = XOR(_tmp81_[3],MixColumn__H16_1_RL32__H16_6__tmp163_);
    MixColumn__H16_1__tmp47_ = XOR(_tmp81_[4],MixColumn__H16_1_RL32__H16_5__tmp163_);
    MixColumn__H16_1__tmp37_ = XOR(_tmp81_[5],MixColumn__H16_1_RL32__H16_4__tmp163_);
    MixColumn__H16_1__tmp30_ = XOR(_tmp81_[6],MixColumn__H16_1_RL32__H16_3__tmp163_);
    MixColumn__H16_1__tmp20_ = XOR(_tmp81_[7],MixColumn__H16_1_RL32__H16_2__tmp163_);
    MixColumn__H16_1__tmp18_ = XOR(MixColumn__H16_1__tmp16_,MixColumn__H16_1_RL32__H16_2__tmp163_);
    MixColumn__H16_1_RL64__H16_8__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp16_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1_RL64__H16_7__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp71_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1__tmp76_ = XOR(MixColumn__H16_1__tmp71_,MixColumn__H16_1_RL32__H16_1__tmp163_);
    MixColumn__H16_1_RL64__H16_6__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp64_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1_RL64__H16_5__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp57_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1_RL64__H16_4__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp47_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1_RL64__H16_3__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp37_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1_RL64__H16_2__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp30_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1_RL64__H16_1__tmp164_ = PERMUT_16(MixColumn__H16_1__tmp20_,2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13);
    MixColumn__H16_1__tmp26_ = XOR(MixColumn__H16_1__tmp20_,MixColumn__H16_1__tmp16_);
    MixColumn__H16_1__tmp35_ = XOR(MixColumn__H16_1__tmp30_,MixColumn__H16_1_RL32__H16_4__tmp163_);
    MixColumn__H16_1__tmp43_ = XOR(MixColumn__H16_1__tmp37_,MixColumn__H16_1__tmp16_);
    MixColumn__H16_1__tmp53_ = XOR(MixColumn__H16_1__tmp47_,MixColumn__H16_1__tmp16_);
    MixColumn__H16_1__tmp62_ = XOR(MixColumn__H16_1__tmp57_,MixColumn__H16_1_RL32__H16_7__tmp163_);
    MixColumn__H16_1__tmp69_ = XOR(MixColumn__H16_1__tmp64_,MixColumn__H16_1_RL32__H16_8__tmp163_);
    _tmp82_[0] = XOR(MixColumn__H16_1__tmp76_,MixColumn__H16_1_RL64__H16_8__tmp164_);
    _tmp82_[7] = XOR(MixColumn__H16_1__tmp18_,MixColumn__H16_1_RL64__H16_1__tmp164_);
    MixColumn__H16_1__tmp28_ = XOR(MixColumn__H16_1__tmp26_,MixColumn__H16_1_RL32__H16_3__tmp163_);
    _tmp82_[5] = XOR(MixColumn__H16_1__tmp35_,MixColumn__H16_1_RL64__H16_3__tmp164_);
    MixColumn__H16_1__tmp45_ = XOR(MixColumn__H16_1__tmp43_,MixColumn__H16_1_RL32__H16_5__tmp163_);
    MixColumn__H16_1__tmp55_ = XOR(MixColumn__H16_1__tmp53_,MixColumn__H16_1_RL32__H16_6__tmp163_);
    _tmp82_[2] = XOR(MixColumn__H16_1__tmp62_,MixColumn__H16_1_RL64__H16_6__tmp164_);
    _tmp82_[1] = XOR(MixColumn__H16_1__tmp69_,MixColumn__H16_1_RL64__H16_7__tmp164_);
    tmp__[0] = XOR(_tmp82_[0],key__[i__][0]);
    tmp__[7] = XOR(_tmp82_[7],key__[i__][7]);
    _tmp82_[6] = XOR(MixColumn__H16_1__tmp28_,MixColumn__H16_1_RL64__H16_2__tmp164_);
    tmp__[5] = XOR(_tmp82_[5],key__[i__][5]);
    _tmp82_[4] = XOR(MixColumn__H16_1__tmp45_,MixColumn__H16_1_RL64__H16_4__tmp164_);
    _tmp82_[3] = XOR(MixColumn__H16_1__tmp55_,MixColumn__H16_1_RL64__H16_5__tmp164_);
    tmp__[2] = XOR(_tmp82_[2],key__[i__][2]);
    tmp__[1] = XOR(_tmp82_[1],key__[i__][1]);
    tmp__[6] = XOR(_tmp82_[6],key__[i__][6]);
    tmp__[4] = XOR(_tmp82_[4],key__[i__][4]);
    tmp__[3] = XOR(_tmp82_[3],key__[i__][3]);
  }
  SubBytes__H16(tmp__[0],tmp__[1],tmp__[2],tmp__[3],tmp__[4],tmp__[5],tmp__[6],tmp__[7],&_tmp83_[0],&_tmp83_[1],&_tmp83_[2],&_tmp83_[3],&_tmp83_[4],&_tmp83_[5],&_tmp83_[6],&_tmp83_[7]);
  ShiftRows__H16_1__tmp155_ = PERMUT_16(_tmp83_[0],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp156_ = PERMUT_16(_tmp83_[1],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp157_ = PERMUT_16(_tmp83_[2],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp158_ = PERMUT_16(_tmp83_[3],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp159_ = PERMUT_16(_tmp83_[4],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp160_ = PERMUT_16(_tmp83_[5],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp161_ = PERMUT_16(_tmp83_[6],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  ShiftRows__H16_1__tmp162_ = PERMUT_16(_tmp83_[7],0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11);
  cipher__[0] = XOR(ShiftRows__H16_1__tmp155_,key__[10][0]);
  cipher__[1] = XOR(ShiftRows__H16_1__tmp156_,key__[10][1]);
  cipher__[2] = XOR(ShiftRows__H16_1__tmp157_,key__[10][2]);
  cipher__[3] = XOR(ShiftRows__H16_1__tmp158_,key__[10][3]);
  cipher__[4] = XOR(ShiftRows__H16_1__tmp159_,key__[10][4]);
  cipher__[5] = XOR(ShiftRows__H16_1__tmp160_,key__[10][5]);
  cipher__[6] = XOR(ShiftRows__H16_1__tmp161_,key__[10][6]);
  cipher__[7] = XOR(ShiftRows__H16_1__tmp162_,key__[10][7]);

}

/* Additional functions */


/* **************************************************************** */
/*                            Usuba source                          */
/*                                                                  */
/*

 _no_inline table SubBytes(input :  v8 :: base)
  returns output :  v8 :: base
{
  99, 124, 119, 123, 242, 107, 111, 197, 48, 1, 103, 43, 254, 215, 171, 118, 202, 130, 201, 125, 250, 89, 71, 240, 173, 212, 162, 175, 156, 164, 114, 192, 183, 253, 147, 38, 54, 63, 247, 204, 52, 165, 229, 241, 113, 216, 49, 21, 4, 199, 35, 195, 24, 150, 5, 154, 7, 18, 128, 226, 235, 39, 178, 117, 9, 131, 44, 26, 27, 110, 90, 160, 82, 59, 214, 179, 41, 227, 47, 132, 83, 209, 0, 237, 32, 252, 177, 91, 106, 203, 190, 57, 74, 76, 88, 207, 208, 239, 170, 251, 67, 77, 51, 133, 69, 249, 2, 127, 80, 60, 159, 168, 81, 163, 64, 143, 146, 157, 56, 245, 188, 182, 218, 33, 16, 255, 243, 210, 205, 12, 19, 236, 95, 151, 68, 23, 196, 167, 126, 61, 100, 93, 25, 115, 96, 129, 79, 220, 34, 42, 144, 136, 70, 238, 184, 20, 222, 94, 11, 219, 224, 50, 58, 10, 73, 6, 36, 92, 194, 211, 172, 98, 145, 149, 228, 121, 231, 200, 55, 109, 141, 213, 78, 169, 108, 86, 244, 234, 101, 122, 174, 8, 186, 120, 37, 46, 28, 166, 180, 198, 232, 221, 116, 31, 75, 189, 139, 138, 112, 62, 181, 102, 72, 3, 246, 14, 97, 53, 87, 185, 134, 193, 29, 158, 225, 248, 152, 17, 105, 217, 142, 148, 155, 30, 135, 233, 206, 85, 40, 223, 140, 161, 137, 13, 191, 230, 66, 104, 65, 153, 45, 15, 176, 84, 187, 22
}


 node ShiftRows(inputSR :  u16x8 :: base)
  returns out :  u16x8 :: base
vars

let
_unroll forall i in [0,7] {
(out[i]) = Shuffle(inputSR[i],[0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11])
}
tel

 node RL32(input :  u16 :: base)
  returns out :  u16 :: base
vars

let
(out) = Shuffle(input,[1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12])
tel

 node RL64(input :  u16 :: base)
  returns out :  u16 :: base
vars

let
(out) = Shuffle(input,[2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13])
tel

 node MixColumn(a :  u16x8 :: base)
  returns b :  u16x8 :: base
vars

let
(b[(7 - 0)]) = (((a[(7 - 7)] ^ RL32(a[(7 - 7)])) ^ RL32(a[(7 - 0)])) ^ RL64((a[(7 - 0)] ^ RL32(a[(7 - 0)]))));
(b[(7 - 1)]) = ((((a[(7 - 0)] ^ RL32(a[(7 - 0)])) ^ (a[(7 - 7)] ^ RL32(a[(7 - 7)]))) ^ RL32(a[(7 - 1)])) ^ RL64((a[(7 - 1)] ^ RL32(a[(7 - 1)]))));
(b[(7 - 2)]) = (((a[(7 - 1)] ^ RL32(a[(7 - 1)])) ^ RL32(a[(7 - 2)])) ^ RL64((a[(7 - 2)] ^ RL32(a[(7 - 2)]))));
(b[(7 - 3)]) = ((((a[(7 - 2)] ^ RL32(a[(7 - 2)])) ^ (a[(7 - 7)] ^ RL32(a[(7 - 7)]))) ^ RL32(a[(7 - 3)])) ^ RL64((a[(7 - 3)] ^ RL32(a[(7 - 3)]))));
(b[(7 - 4)]) = ((((a[(7 - 3)] ^ RL32(a[(7 - 3)])) ^ (a[(7 - 7)] ^ RL32(a[(7 - 7)]))) ^ RL32(a[(7 - 4)])) ^ RL64((a[(7 - 4)] ^ RL32(a[(7 - 4)]))));
(b[(7 - 5)]) = (((a[(7 - 4)] ^ RL32(a[(7 - 4)])) ^ RL32(a[(7 - 5)])) ^ RL64((a[(7 - 5)] ^ RL32(a[(7 - 5)]))));
(b[(7 - 6)]) = (((a[(7 - 5)] ^ RL32(a[(7 - 5)])) ^ RL32(a[(7 - 6)])) ^ RL64((a[(7 - 6)] ^ RL32(a[(7 - 6)]))));
(b[(7 - 7)]) = (((a[(7 - 6)] ^ RL32(a[(7 - 6)])) ^ RL32(a[(7 - 7)])) ^ RL64((a[(7 - 7)] ^ RL32(a[(7 - 7)]))))
tel

 node AES(plain :  u16x8 :: base,key :  u16x8[11] :: base)
  returns cipher :  u16x8 :: base
vars
  tmp :  u16x8[10] :: base
let
(tmp[0]) = (plain ^ key[0]);
forall i in [1,9] {
(tmp[i]) = (MixColumn(ShiftRows(SubBytes(tmp[(i - 1)]))) ^ key[i])
};
(cipher) = (ShiftRows(SubBytes(tmp[9])) ^ key[10])
tel

*/
 