/* This code was generated by Usuba.
   See https://github.com/DadaIsCrazy/usuba.
   From the file "nist/pyjamask/usuba/ua/pyjamask_vslice.ua" (included below). */

#include <stdint.h>

/* Do NOT change the order of those define/include */

#ifndef BITS_PER_REG
#define BITS_PER_REG 32
#endif
/* including the architecture specific .h */
#include "MASKED_UA.h"

/* auxiliary functions */
void SubBytes__V32 (/*inputs*/ DATATYPE s0[MASKING_ORDER],DATATYPE s1[MASKING_ORDER],DATATYPE s2[MASKING_ORDER],DATATYPE s3[MASKING_ORDER], /*outputs*/ DATATYPE ret[4][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _shadow_s01_[MASKING_ORDER];
  DATATYPE _shadow_s03_[MASKING_ORDER];
  DATATYPE _shadow_s14_[MASKING_ORDER];
  DATATYPE _shadow_s17_;
  DATATYPE _shadow_s25_;
  DATATYPE _shadow_s26_;
  DATATYPE _shadow_s32_[MASKING_ORDER];
  DATATYPE _shadow_s38_[MASKING_ORDER];
  DATATYPE _tmp1_[MASKING_ORDER];
  DATATYPE _tmp2_[MASKING_ORDER];
  DATATYPE _tmp3_[MASKING_ORDER];
  DATATYPE _tmp4_[MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s01_[_mask_idx] = XOR(s0[_mask_idx],s3[_mask_idx]);
  }
  MASKED_AND(_tmp1_,_shadow_s01_,s1);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s32_[_mask_idx] = XOR(s3[_mask_idx],_tmp1_[_mask_idx]);
  }
  MASKED_AND(_tmp2_,s1,s2);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s03_[_mask_idx] = XOR(_shadow_s01_[_mask_idx],_tmp2_[_mask_idx]);
    ret[0][_mask_idx] = _shadow_s03_[_mask_idx];
  }
  MASKED_AND(_tmp3_,s2,_shadow_s32_);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s14_[_mask_idx] = XOR(s1[_mask_idx],_tmp3_[_mask_idx]);
    _shadow_s17_ = XOR(_shadow_s14_[_mask_idx],_shadow_s03_[_mask_idx]);
    ret[1][_mask_idx] = _shadow_s17_;
  }
  MASKED_AND(_tmp4_,_shadow_s03_,_shadow_s32_);
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s25_ = XOR(s2[_mask_idx],_tmp4_[_mask_idx]);
    _shadow_s26_ = XOR(_shadow_s25_,_shadow_s14_[_mask_idx]);
    ret[3][_mask_idx] = _shadow_s26_;
  }
  _shadow_s38_[0] = NOT(_shadow_s32_[0]);
  for (int _mask_idx = 1; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    _shadow_s38_[_mask_idx] = _shadow_s32_[_mask_idx];
  }
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    ret[2][_mask_idx] = _shadow_s38_[_mask_idx];
  }

}

void AddRoundKey__V32 (/*inputs*/ DATATYPE i__[4][MASKING_ORDER],DATATYPE k__[4][MASKING_ORDER], /*outputs*/ DATATYPE o__[4][MASKING_ORDER]) {

  // Variables declaration
  ;

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    o__[0][_mask_idx] = XOR(i__[0][_mask_idx],k__[0][_mask_idx]);
    o__[1][_mask_idx] = XOR(i__[1][_mask_idx],k__[1][_mask_idx]);
    o__[2][_mask_idx] = XOR(i__[2][_mask_idx],k__[2][_mask_idx]);
    o__[3][_mask_idx] = XOR(i__[3][_mask_idx],k__[3][_mask_idx]);
  }

}

void mat_mult__V32 (/*inputs*/ DATATYPE col__[MASKING_ORDER],DATATYPE vec__[MASKING_ORDER], /*outputs*/ DATATYPE res__[MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp5_;
  DATATYPE _tmp6_;
  DATATYPE mask__[MASKING_ORDER];
  DATATYPE mat_col__[33][MASKING_ORDER];
  DATATYPE res_tmp__[MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    mat_col__[0][_mask_idx] = col__[_mask_idx];
  }
  res_tmp__[0] = LIFT_32(0);
  for (int _mask_idx = 1; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    res_tmp__[_mask_idx] = LIFT_32(0);
  }
  for (int i__ = 0; i__ <= 31; i__++) {
    for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
      _tmp5_ = L_SHIFT(vec__[_mask_idx],i__,32);
      mask__[_mask_idx] = RA_SHIFT(_tmp5_,31,32);
      _tmp6_ = AND(mask__[_mask_idx],mat_col__[i__][0]);
      res_tmp__[_mask_idx] = XOR(res_tmp__[_mask_idx],_tmp6_);
      mat_col__[(i__ + 1)][_mask_idx] = R_ROTATE(mat_col__[i__][_mask_idx],1,32);
    }
  }
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    res__[_mask_idx] = res_tmp__[_mask_idx];
  }

}

void MixRows__V32 (/*inputs*/ DATATYPE input__[4][MASKING_ORDER], /*outputs*/ DATATYPE output__[4][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE M__[4][MASKING_ORDER];

  // Instructions (body)
  M__[0][0] = LIFT_32(2743472261);
  for (int _mask_idx = 1; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    M__[0][_mask_idx] = LIFT_32(0);
    M__[1][_mask_idx] = LIFT_32(0);
    M__[2][_mask_idx] = LIFT_32(0);
    M__[3][_mask_idx] = LIFT_32(0);
  }
  M__[1][0] = LIFT_32(1665232929);
  M__[2][0] = LIFT_32(1764553344);
  M__[3][0] = LIFT_32(1218791443);
  for (int i__ = 0; i__ <= 3; i__++) {
    mat_mult__V32(M__[i__],input__[i__],output__[i__]);
  }

}

/* main function */
void pyjamask__ (/*inputs*/ DATATYPE plaintext__[4][MASKING_ORDER],DATATYPE key__[15][4][MASKING_ORDER], /*outputs*/ DATATYPE ciphertext__[4][MASKING_ORDER]) {

  // Variables declaration
  DATATYPE _tmp11_[4][MASKING_ORDER];
  DATATYPE _tmp12_[4][MASKING_ORDER];
  DATATYPE round__[4][MASKING_ORDER];

  // Instructions (body)
  for (int _mask_idx = 0; _mask_idx <= (MASKING_ORDER - 1); _mask_idx++) {
    round__[0][_mask_idx] = plaintext__[0][_mask_idx];
    round__[1][_mask_idx] = plaintext__[1][_mask_idx];
    round__[2][_mask_idx] = plaintext__[2][_mask_idx];
    round__[3][_mask_idx] = plaintext__[3][_mask_idx];
  }
  for (int i__ = 0; i__ <= 13; i__++) {
    AddRoundKey__V32(round__,key__[i__],_tmp11_);
    SubBytes__V32(_tmp11_[0],_tmp11_[1],_tmp11_[2],_tmp11_[3],_tmp12_);
    MixRows__V32(_tmp12_,round__);
  }
  AddRoundKey__V32(round__,key__[14],ciphertext__);

}

/* Additional functions */
uint32_t bench_speed() {
  /* inputs */
  DATATYPE plaintext__[4][MASKING_ORDER][MASKING_ORDER] = { 0 };
  DATATYPE key__[15][4][MASKING_ORDER][MASKING_ORDER] = { 0 };
  /* outputs */
  DATATYPE ciphertext__[4][MASKING_ORDER][MASKING_ORDER] = { 0 };
  /* fun call */
  pyjamask__(plaintext__, key__,ciphertext__);

  /* Returning the number of encrypted bytes */
  return 0;
}

/* **************************************************************** */
/*                            Usuba source                          */
/*                                                                  */
/*

 table SubBytes(i :  v4 :: base)
  returns o :  v4 :: base
{
  2, 13, 3, 9, 7, 11, 10, 6, 14, 0, 15, 4, 8, 5, 1, 12
}


 node AddRoundKey(i :  u32x4 :: base,k :  u32x4 :: base)
  returns o :  u32x4 :: base
vars

let
  (o) = (i ^ k)
tel

 node mat_mult(col : const u32 :: base,vec :  u32 :: base)
  returns res :  u32 :: base
vars
  mat_col :  u32[33] :: base,
  res_tmp :  u32[33] :: base,
  mask :  u32[32] :: base
let
  (mat_col[0]) = col;
  (res_tmp[0]) = 0;
  forall i in [0,31] {
    (mask[i]) = ((vec << i) >>! 31);
    (res_tmp[(i + 1)]) = (res_tmp[i] ^ (mask[i] & mat_col[i]));
    (mat_col[(i + 1)]) = (mat_col[i] >>> 1)
  };
  (res) = res_tmp[32]
tel

 node MixRows(input :  u32x4 :: base)
  returns output :  u32x4 :: base
vars
  M : const u32[4] :: base
let
  (M) = (2743472261,1665232929,1764553344,1218791443);
  forall i in [0,3] {
    (output[i]) = mat_mult(M[i],input[i])
  }
tel

 node pyjamask(plaintext :  u32x4 :: base,key :  u32x4[15] :: base)
  returns ciphertext :  u32x4 :: base
vars
  round :  u32x4[15] :: base
let
  (round[0]) = plaintext;
  forall i in [0,13] {
    (round[(i + 1)]) = MixRows(SubBytes(AddRoundKey(round[i],key[i])))
  };
  (ciphertext) = AddRoundKey(round[14],key[14])
tel

*/
 