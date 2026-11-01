From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "lib/crypto/chacha-block-generic.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _b : ident := $"b".
Definition _chacha_block_generic : ident := $"chacha_block_generic".
Definition _chacha_permute : ident := $"chacha_permute".
Definition _chacha_state : ident := $"chacha_state".
Definition _chacha_zeroize_state : ident := $"chacha_zeroize_state".
Definition _count : ident := $"count".
Definition _hchacha_block_generic : ident := $"hchacha_block_generic".
Definition _i : ident := $"i".
Definition _main : ident := $"main".
Definition _memset : ident := $"memset".
Definition _memzero_explicit : ident := $"memzero_explicit".
Definition _nrounds : ident := $"nrounds".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _permuted_state : ident := $"permuted_state".
Definition _put_unaligned_le32 : ident := $"put_unaligned_le32".
Definition _rol32 : ident := $"rol32".
Definition _s : ident := $"s".
Definition _shift : ident := $"shift".
Definition _state : ident := $"state".
Definition _v : ident := $"v".
Definition _word : ident := $"word".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'100 : ident := 227%positive.
Definition _t'101 : ident := 228%positive.
Definition _t'102 : ident := 229%positive.
Definition _t'103 : ident := 230%positive.
Definition _t'104 : ident := 231%positive.
Definition _t'105 : ident := 232%positive.
Definition _t'106 : ident := 233%positive.
Definition _t'107 : ident := 234%positive.
Definition _t'108 : ident := 235%positive.
Definition _t'109 : ident := 236%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'110 : ident := 237%positive.
Definition _t'111 : ident := 238%positive.
Definition _t'112 : ident := 239%positive.
Definition _t'113 : ident := 240%positive.
Definition _t'114 : ident := 241%positive.
Definition _t'115 : ident := 242%positive.
Definition _t'116 : ident := 243%positive.
Definition _t'117 : ident := 244%positive.
Definition _t'118 : ident := 245%positive.
Definition _t'119 : ident := 246%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'120 : ident := 247%positive.
Definition _t'121 : ident := 248%positive.
Definition _t'122 : ident := 249%positive.
Definition _t'123 : ident := 250%positive.
Definition _t'124 : ident := 251%positive.
Definition _t'125 : ident := 252%positive.
Definition _t'126 : ident := 253%positive.
Definition _t'127 : ident := 254%positive.
Definition _t'128 : ident := 255%positive.
Definition _t'129 : ident := 256%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'130 : ident := 257%positive.
Definition _t'131 : ident := 258%positive.
Definition _t'132 : ident := 259%positive.
Definition _t'133 : ident := 260%positive.
Definition _t'134 : ident := 261%positive.
Definition _t'135 : ident := 262%positive.
Definition _t'136 : ident := 263%positive.
Definition _t'137 : ident := 264%positive.
Definition _t'138 : ident := 265%positive.
Definition _t'139 : ident := 266%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'140 : ident := 267%positive.
Definition _t'141 : ident := 268%positive.
Definition _t'142 : ident := 269%positive.
Definition _t'143 : ident := 270%positive.
Definition _t'144 : ident := 271%positive.
Definition _t'145 : ident := 272%positive.
Definition _t'146 : ident := 273%positive.
Definition _t'147 : ident := 274%positive.
Definition _t'148 : ident := 275%positive.
Definition _t'149 : ident := 276%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'150 : ident := 277%positive.
Definition _t'151 : ident := 278%positive.
Definition _t'152 : ident := 279%positive.
Definition _t'153 : ident := 280%positive.
Definition _t'154 : ident := 281%positive.
Definition _t'155 : ident := 282%positive.
Definition _t'156 : ident := 283%positive.
Definition _t'157 : ident := 284%positive.
Definition _t'158 : ident := 285%positive.
Definition _t'159 : ident := 286%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'160 : ident := 287%positive.
Definition _t'161 : ident := 288%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'55 : ident := 182%positive.
Definition _t'56 : ident := 183%positive.
Definition _t'57 : ident := 184%positive.
Definition _t'58 : ident := 185%positive.
Definition _t'59 : ident := 186%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'60 : ident := 187%positive.
Definition _t'61 : ident := 188%positive.
Definition _t'62 : ident := 189%positive.
Definition _t'63 : ident := 190%positive.
Definition _t'64 : ident := 191%positive.
Definition _t'65 : ident := 192%positive.
Definition _t'66 : ident := 193%positive.
Definition _t'67 : ident := 194%positive.
Definition _t'68 : ident := 195%positive.
Definition _t'69 : ident := 196%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'70 : ident := 197%positive.
Definition _t'71 : ident := 198%positive.
Definition _t'72 : ident := 199%positive.
Definition _t'73 : ident := 200%positive.
Definition _t'74 : ident := 201%positive.
Definition _t'75 : ident := 202%positive.
Definition _t'76 : ident := 203%positive.
Definition _t'77 : ident := 204%positive.
Definition _t'78 : ident := 205%positive.
Definition _t'79 : ident := 206%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'80 : ident := 207%positive.
Definition _t'81 : ident := 208%positive.
Definition _t'82 : ident := 209%positive.
Definition _t'83 : ident := 210%positive.
Definition _t'84 : ident := 211%positive.
Definition _t'85 : ident := 212%positive.
Definition _t'86 : ident := 213%positive.
Definition _t'87 : ident := 214%positive.
Definition _t'88 : ident := 215%positive.
Definition _t'89 : ident := 216%positive.
Definition _t'9 : ident := 136%positive.
Definition _t'90 : ident := 217%positive.
Definition _t'91 : ident := 218%positive.
Definition _t'92 : ident := 219%positive.
Definition _t'93 : ident := 220%positive.
Definition _t'94 : ident := 221%positive.
Definition _t'95 : ident := 222%positive.
Definition _t'96 : ident := 223%positive.
Definition _t'97 : ident := 224%positive.
Definition _t'98 : ident := 225%positive.
Definition _t'99 : ident := 226%positive.

Definition f_memzero_explicit := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tvoid)) :: (_count, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                  (tptr tvoid) cc_default))
  ((Etempvar _s (tptr tvoid)) :: (Econst_int (Int.repr 0) tint) ::
   (Etempvar _count tulong) :: nil))
|}.

Definition f_rol32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_word, tuint) :: (_shift, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshl (Etempvar _word tuint)
                   (Ebinop Oand (Etempvar _shift tuint)
                     (Econst_int (Int.repr 31) tint) tuint) tuint)
                 (Ebinop Oshr (Etempvar _word tuint)
                   (Ebinop Oand (Eunop Oneg (Etempvar _shift tuint) tuint)
                     (Econst_int (Int.repr 31) tint) tuint) tuint) tuint)))
|}.

Definition f_put_unaligned_le32 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: (_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Etempvar _p (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _b (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ecast (Etempvar _v tuint) tuchar))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _b (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 8) tint)
            tuint) tuchar))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 16) tint)
              tuint) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 24) tint)
              tuint) tuchar))))))
|}.

Definition f_chacha_zeroize_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil) tvoid
                            cc_default))
  ((Etempvar _state (tptr (Tstruct _chacha_state noattr))) ::
   (Esizeof (Tstruct _chacha_state noattr) tulong) :: nil))
|}.

Definition f_chacha_permute := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) ::
                (_nrounds, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, (tptr tuint)) :: (_i, tint) :: (_t'33, tuint) ::
               (_t'32, tuint) :: (_t'31, tuint) :: (_t'30, tuint) ::
               (_t'29, tuint) :: (_t'28, tuint) :: (_t'27, tuint) ::
               (_t'26, tuint) :: (_t'25, tuint) :: (_t'24, tuint) ::
               (_t'23, tuint) :: (_t'22, tuint) :: (_t'21, tuint) ::
               (_t'20, tuint) :: (_t'19, tuint) :: (_t'18, tuint) ::
               (_t'17, tuint) :: (_t'16, tuint) :: (_t'15, tuint) ::
               (_t'14, tuint) :: (_t'13, tuint) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tint) :: (_t'161, tuint) ::
               (_t'160, tuint) :: (_t'159, tuint) :: (_t'158, tuint) ::
               (_t'157, tuint) :: (_t'156, tuint) :: (_t'155, tuint) ::
               (_t'154, tuint) :: (_t'153, tuint) :: (_t'152, tuint) ::
               (_t'151, tuint) :: (_t'150, tuint) :: (_t'149, tuint) ::
               (_t'148, tuint) :: (_t'147, tuint) :: (_t'146, tuint) ::
               (_t'145, tuint) :: (_t'144, tuint) :: (_t'143, tuint) ::
               (_t'142, tuint) :: (_t'141, tuint) :: (_t'140, tuint) ::
               (_t'139, tuint) :: (_t'138, tuint) :: (_t'137, tuint) ::
               (_t'136, tuint) :: (_t'135, tuint) :: (_t'134, tuint) ::
               (_t'133, tuint) :: (_t'132, tuint) :: (_t'131, tuint) ::
               (_t'130, tuint) :: (_t'129, tuint) :: (_t'128, tuint) ::
               (_t'127, tuint) :: (_t'126, tuint) :: (_t'125, tuint) ::
               (_t'124, tuint) :: (_t'123, tuint) :: (_t'122, tuint) ::
               (_t'121, tuint) :: (_t'120, tuint) :: (_t'119, tuint) ::
               (_t'118, tuint) :: (_t'117, tuint) :: (_t'116, tuint) ::
               (_t'115, tuint) :: (_t'114, tuint) :: (_t'113, tuint) ::
               (_t'112, tuint) :: (_t'111, tuint) :: (_t'110, tuint) ::
               (_t'109, tuint) :: (_t'108, tuint) :: (_t'107, tuint) ::
               (_t'106, tuint) :: (_t'105, tuint) :: (_t'104, tuint) ::
               (_t'103, tuint) :: (_t'102, tuint) :: (_t'101, tuint) ::
               (_t'100, tuint) :: (_t'99, tuint) :: (_t'98, tuint) ::
               (_t'97, tuint) :: (_t'96, tuint) :: (_t'95, tuint) ::
               (_t'94, tuint) :: (_t'93, tuint) :: (_t'92, tuint) ::
               (_t'91, tuint) :: (_t'90, tuint) :: (_t'89, tuint) ::
               (_t'88, tuint) :: (_t'87, tuint) :: (_t'86, tuint) ::
               (_t'85, tuint) :: (_t'84, tuint) :: (_t'83, tuint) ::
               (_t'82, tuint) :: (_t'81, tuint) :: (_t'80, tuint) ::
               (_t'79, tuint) :: (_t'78, tuint) :: (_t'77, tuint) ::
               (_t'76, tuint) :: (_t'75, tuint) :: (_t'74, tuint) ::
               (_t'73, tuint) :: (_t'72, tuint) :: (_t'71, tuint) ::
               (_t'70, tuint) :: (_t'69, tuint) :: (_t'68, tuint) ::
               (_t'67, tuint) :: (_t'66, tuint) :: (_t'65, tuint) ::
               (_t'64, tuint) :: (_t'63, tuint) :: (_t'62, tuint) ::
               (_t'61, tuint) :: (_t'60, tuint) :: (_t'59, tuint) ::
               (_t'58, tuint) :: (_t'57, tuint) :: (_t'56, tuint) ::
               (_t'55, tuint) :: (_t'54, tuint) :: (_t'53, tuint) ::
               (_t'52, tuint) :: (_t'51, tuint) :: (_t'50, tuint) ::
               (_t'49, tuint) :: (_t'48, tuint) :: (_t'47, tuint) ::
               (_t'46, tuint) :: (_t'45, tuint) :: (_t'44, tuint) ::
               (_t'43, tuint) :: (_t'42, tuint) :: (_t'41, tuint) ::
               (_t'40, tuint) :: (_t'39, tuint) :: (_t'38, tuint) ::
               (_t'37, tuint) :: (_t'36, tuint) :: (_t'35, tuint) ::
               (_t'34, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Efield
      (Ederef (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
        (Tstruct _chacha_state noattr)) _x (tarray tuint 16)))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _nrounds tint)
                   (Econst_int (Int.repr 20) tint) tint)
      (Sset _t'1
        (Ecast
          (Ebinop One (Etempvar _nrounds tint)
            (Econst_int (Int.repr 12) tint) tint) tbool))
      (Sset _t'1 (Econst_int (Int.repr 0) tint)))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Etempvar _nrounds tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'160
                (Ederef
                  (Ebinop Oadd (Etempvar _x (tptr tuint))
                    (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _t'161
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                      (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                      (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                  (Ebinop Oadd (Etempvar _t'160 tuint)
                    (Etempvar _t'161 tuint) tuint))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'158
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                        (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'159
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Scall (Some _t'2)
                      (Evar _rol32 (Tfunction (tuint :: tuint :: nil) tuint
                                     cc_default))
                      ((Ebinop Oxor (Etempvar _t'158 tuint)
                         (Etempvar _t'159 tuint) tuint) ::
                       (Econst_int (Int.repr 16) tint) :: nil))))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                      (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint)
                  (Etempvar _t'2 tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'156
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'157
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tuint))
                          (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tuint))
                          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
                      (Ebinop Oadd (Etempvar _t'156 tuint)
                        (Etempvar _t'157 tuint) tuint))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'154
                        (Ederef
                          (Ebinop Oadd (Etempvar _x (tptr tuint))
                            (Econst_int (Int.repr 13) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _t'155
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tuint))
                              (Econst_int (Int.repr 1) tint) (tptr tuint))
                            tuint))
                        (Scall (Some _t'3)
                          (Evar _rol32 (Tfunction (tuint :: tuint :: nil)
                                         tuint cc_default))
                          ((Ebinop Oxor (Etempvar _t'154 tuint)
                             (Etempvar _t'155 tuint) tuint) ::
                           (Econst_int (Int.repr 16) tint) :: nil))))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tuint))
                          (Econst_int (Int.repr 13) tint) (tptr tuint))
                        tuint) (Etempvar _t'3 tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'152
                        (Ederef
                          (Ebinop Oadd (Etempvar _x (tptr tuint))
                            (Econst_int (Int.repr 2) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _t'153
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tuint))
                              (Econst_int (Int.repr 6) tint) (tptr tuint))
                            tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tuint))
                              (Econst_int (Int.repr 2) tint) (tptr tuint))
                            tuint)
                          (Ebinop Oadd (Etempvar _t'152 tuint)
                            (Etempvar _t'153 tuint) tuint))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'150
                            (Ederef
                              (Ebinop Oadd (Etempvar _x (tptr tuint))
                                (Econst_int (Int.repr 14) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _t'151
                              (Ederef
                                (Ebinop Oadd (Etempvar _x (tptr tuint))
                                  (Econst_int (Int.repr 2) tint)
                                  (tptr tuint)) tuint))
                            (Scall (Some _t'4)
                              (Evar _rol32 (Tfunction (tuint :: tuint :: nil)
                                             tuint cc_default))
                              ((Ebinop Oxor (Etempvar _t'150 tuint)
                                 (Etempvar _t'151 tuint) tuint) ::
                               (Econst_int (Int.repr 16) tint) :: nil))))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tuint))
                              (Econst_int (Int.repr 14) tint) (tptr tuint))
                            tuint) (Etempvar _t'4 tuint)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'148
                            (Ederef
                              (Ebinop Oadd (Etempvar _x (tptr tuint))
                                (Econst_int (Int.repr 3) tint) (tptr tuint))
                              tuint))
                          (Ssequence
                            (Sset _t'149
                              (Ederef
                                (Ebinop Oadd (Etempvar _x (tptr tuint))
                                  (Econst_int (Int.repr 7) tint)
                                  (tptr tuint)) tuint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _x (tptr tuint))
                                  (Econst_int (Int.repr 3) tint)
                                  (tptr tuint)) tuint)
                              (Ebinop Oadd (Etempvar _t'148 tuint)
                                (Etempvar _t'149 tuint) tuint))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'146
                                (Ederef
                                  (Ebinop Oadd (Etempvar _x (tptr tuint))
                                    (Econst_int (Int.repr 15) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _t'147
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                                (Scall (Some _t'5)
                                  (Evar _rol32 (Tfunction
                                                 (tuint :: tuint :: nil)
                                                 tuint cc_default))
                                  ((Ebinop Oxor (Etempvar _t'146 tuint)
                                     (Etempvar _t'147 tuint) tuint) ::
                                   (Econst_int (Int.repr 16) tint) :: nil))))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _x (tptr tuint))
                                  (Econst_int (Int.repr 15) tint)
                                  (tptr tuint)) tuint) (Etempvar _t'5 tuint)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'144
                                (Ederef
                                  (Ebinop Oadd (Etempvar _x (tptr tuint))
                                    (Econst_int (Int.repr 8) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _t'145
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                                      (Econst_int (Int.repr 12) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                                      (Econst_int (Int.repr 8) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Oadd (Etempvar _t'144 tuint)
                                    (Etempvar _t'145 tuint) tuint))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'142
                                    (Ederef
                                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                                        (Econst_int (Int.repr 4) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _t'143
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _x (tptr tuint))
                                          (Econst_int (Int.repr 8) tint)
                                          (tptr tuint)) tuint))
                                    (Scall (Some _t'6)
                                      (Evar _rol32 (Tfunction
                                                     (tuint :: tuint :: nil)
                                                     tuint cc_default))
                                      ((Ebinop Oxor (Etempvar _t'142 tuint)
                                         (Etempvar _t'143 tuint) tuint) ::
                                       (Econst_int (Int.repr 12) tint) ::
                                       nil))))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _x (tptr tuint))
                                      (Econst_int (Int.repr 4) tint)
                                      (tptr tuint)) tuint)
                                  (Etempvar _t'6 tuint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'140
                                    (Ederef
                                      (Ebinop Oadd (Etempvar _x (tptr tuint))
                                        (Econst_int (Int.repr 9) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _t'141
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _x (tptr tuint))
                                          (Econst_int (Int.repr 13) tint)
                                          (tptr tuint)) tuint))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _x (tptr tuint))
                                          (Econst_int (Int.repr 9) tint)
                                          (tptr tuint)) tuint)
                                      (Ebinop Oadd (Etempvar _t'140 tuint)
                                        (Etempvar _t'141 tuint) tuint))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'138
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _x (tptr tuint))
                                            (Econst_int (Int.repr 5) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _t'139
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _x (tptr tuint))
                                              (Econst_int (Int.repr 9) tint)
                                              (tptr tuint)) tuint))
                                        (Scall (Some _t'7)
                                          (Evar _rol32 (Tfunction
                                                         (tuint :: tuint ::
                                                          nil) tuint
                                                         cc_default))
                                          ((Ebinop Oxor
                                             (Etempvar _t'138 tuint)
                                             (Etempvar _t'139 tuint) tuint) ::
                                           (Econst_int (Int.repr 12) tint) ::
                                           nil))))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _x (tptr tuint))
                                          (Econst_int (Int.repr 5) tint)
                                          (tptr tuint)) tuint)
                                      (Etempvar _t'7 tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'136
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _x (tptr tuint))
                                            (Econst_int (Int.repr 10) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _t'137
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _x (tptr tuint))
                                              (Econst_int (Int.repr 14) tint)
                                              (tptr tuint)) tuint))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _x (tptr tuint))
                                              (Econst_int (Int.repr 10) tint)
                                              (tptr tuint)) tuint)
                                          (Ebinop Oadd
                                            (Etempvar _t'136 tuint)
                                            (Etempvar _t'137 tuint) tuint))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'134
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _x (tptr tuint))
                                                (Econst_int (Int.repr 6) tint)
                                                (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _t'135
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _x (tptr tuint))
                                                  (Econst_int (Int.repr 10) tint)
                                                  (tptr tuint)) tuint))
                                            (Scall (Some _t'8)
                                              (Evar _rol32 (Tfunction
                                                             (tuint ::
                                                              tuint :: nil)
                                                             tuint
                                                             cc_default))
                                              ((Ebinop Oxor
                                                 (Etempvar _t'134 tuint)
                                                 (Etempvar _t'135 tuint)
                                                 tuint) ::
                                               (Econst_int (Int.repr 12) tint) ::
                                               nil))))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _x (tptr tuint))
                                              (Econst_int (Int.repr 6) tint)
                                              (tptr tuint)) tuint)
                                          (Etempvar _t'8 tuint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'132
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _x (tptr tuint))
                                                (Econst_int (Int.repr 11) tint)
                                                (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _t'133
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _x (tptr tuint))
                                                  (Econst_int (Int.repr 15) tint)
                                                  (tptr tuint)) tuint))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _x (tptr tuint))
                                                  (Econst_int (Int.repr 11) tint)
                                                  (tptr tuint)) tuint)
                                              (Ebinop Oadd
                                                (Etempvar _t'132 tuint)
                                                (Etempvar _t'133 tuint)
                                                tuint))))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'130
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _x (tptr tuint))
                                                    (Econst_int (Int.repr 7) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'131
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _x (tptr tuint))
                                                      (Econst_int (Int.repr 11) tint)
                                                      (tptr tuint)) tuint))
                                                (Scall (Some _t'9)
                                                  (Evar _rol32 (Tfunction
                                                                 (tuint ::
                                                                  tuint ::
                                                                  nil) tuint
                                                                 cc_default))
                                                  ((Ebinop Oxor
                                                     (Etempvar _t'130 tuint)
                                                     (Etempvar _t'131 tuint)
                                                     tuint) ::
                                                   (Econst_int (Int.repr 12) tint) ::
                                                   nil))))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _x (tptr tuint))
                                                  (Econst_int (Int.repr 7) tint)
                                                  (tptr tuint)) tuint)
                                              (Etempvar _t'9 tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'128
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _x (tptr tuint))
                                                    (Econst_int (Int.repr 0) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'129
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _x (tptr tuint))
                                                      (Econst_int (Int.repr 4) tint)
                                                      (tptr tuint)) tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _x (tptr tuint))
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'128 tuint)
                                                    (Etempvar _t'129 tuint)
                                                    tuint))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'126
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _x (tptr tuint))
                                                        (Econst_int (Int.repr 12) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'127
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _x (tptr tuint))
                                                          (Econst_int (Int.repr 0) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Scall (Some _t'10)
                                                      (Evar _rol32 (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                      ((Ebinop Oxor
                                                         (Etempvar _t'126 tuint)
                                                         (Etempvar _t'127 tuint)
                                                         tuint) ::
                                                       (Econst_int (Int.repr 8) tint) ::
                                                       nil))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _x (tptr tuint))
                                                      (Econst_int (Int.repr 12) tint)
                                                      (tptr tuint)) tuint)
                                                  (Etempvar _t'10 tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'124
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _x (tptr tuint))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'125
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _x (tptr tuint))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _x (tptr tuint))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'124 tuint)
                                                        (Etempvar _t'125 tuint)
                                                        tuint))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'122
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _x (tptr tuint))
                                                            (Econst_int (Int.repr 13) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'123
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _x (tptr tuint))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'11)
                                                          (Evar _rol32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'122 tuint)
                                                             (Etempvar _t'123 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 8) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _x (tptr tuint))
                                                          (Econst_int (Int.repr 13) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'11 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'120
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _x (tptr tuint))
                                                            (Econst_int (Int.repr 2) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'121
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _x (tptr tuint))
                                                              (Econst_int (Int.repr 6) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _x (tptr tuint))
                                                              (Econst_int (Int.repr 2) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'120 tuint)
                                                            (Etempvar _t'121 tuint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'118
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _x (tptr tuint))
                                                                (Econst_int (Int.repr 14) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'119
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _x (tptr tuint))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'12)
                                                              (Evar _rol32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'118 tuint)
                                                                 (Etempvar _t'119 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 8) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _x (tptr tuint))
                                                              (Econst_int (Int.repr 14) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'12 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'116
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _x (tptr tuint))
                                                                (Econst_int (Int.repr 3) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'117
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _x (tptr tuint))
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _x (tptr tuint))
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'116 tuint)
                                                                (Etempvar _t'117 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'114
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'115
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'13)
                                                                  (Evar _rol32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'114 tuint)
                                                                    (Etempvar _t'115 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 8) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Etempvar _x (tptr tuint))
                                                                  (Econst_int (Int.repr 15) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'13 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'112
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'113
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'112 tuint)
                                                                    (Etempvar _t'113 tuint)
                                                                    tuint))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'110
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'111
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'14)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'110 tuint)
                                                                    (Etempvar _t'111 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'14 tuint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'108
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'109
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'108 tuint)
                                                                    (Etempvar _t'109 tuint)
                                                                    tuint))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'106
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'107
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'15)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'106 tuint)
                                                                    (Etempvar _t'107 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'15 tuint)))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'104
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'105
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'104 tuint)
                                                                    (Etempvar _t'105 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'102
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'103
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'16)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'102 tuint)
                                                                    (Etempvar _t'103 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'16 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'100
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'101
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'100 tuint)
                                                                    (Etempvar _t'101 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'98
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'99
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'17)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'98 tuint)
                                                                    (Etempvar _t'99 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'17 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'96
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'97
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'96 tuint)
                                                                    (Etempvar _t'97 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'94
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'95
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'18)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'94 tuint)
                                                                    (Etempvar _t'95 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'18 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'92
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'93
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'92 tuint)
                                                                    (Etempvar _t'93 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'90
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'91
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'19)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'90 tuint)
                                                                    (Etempvar _t'91 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'19 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'88
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'89
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'88 tuint)
                                                                    (Etempvar _t'89 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'86
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'87
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'20)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'86 tuint)
                                                                    (Etempvar _t'87 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'20 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'84
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'85
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'84 tuint)
                                                                    (Etempvar _t'85 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'82
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'83
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'21)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'82 tuint)
                                                                    (Etempvar _t'83 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'21 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'80
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'81
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'80 tuint)
                                                                    (Etempvar _t'81 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'78
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'79
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'22)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'78 tuint)
                                                                    (Etempvar _t'79 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'22 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'76
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'77
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'76 tuint)
                                                                    (Etempvar _t'77 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'74
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'75
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'23)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'74 tuint)
                                                                    (Etempvar _t'75 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'23 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'72
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'73
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'72 tuint)
                                                                    (Etempvar _t'73 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'70
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'71
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'24)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'70 tuint)
                                                                    (Etempvar _t'71 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'24 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'68
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'69
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'68 tuint)
                                                                    (Etempvar _t'69 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'66
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'67
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'25)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'66 tuint)
                                                                    (Etempvar _t'67 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'25 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'64
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'65
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'64 tuint)
                                                                    (Etempvar _t'65 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'62
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'63
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'26)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'62 tuint)
                                                                    (Etempvar _t'63 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'26 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'61
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'60 tuint)
                                                                    (Etempvar _t'61 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'27)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'58 tuint)
                                                                    (Etempvar _t'59 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'27 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'56
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'57
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'56 tuint)
                                                                    (Etempvar _t'57 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'28)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'54 tuint)
                                                                    (Etempvar _t'55 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'28 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'52
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'53
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'52 tuint)
                                                                    (Etempvar _t'53 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'50
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'51
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'29)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'50 tuint)
                                                                    (Etempvar _t'51 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'29 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'48
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'49
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'48 tuint)
                                                                    (Etempvar _t'49 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'46
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'47
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'30)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'46 tuint)
                                                                    (Etempvar _t'47 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'30 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'44
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'45
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 tuint)
                                                                    (Etempvar _t'45 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'43
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'31)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'42 tuint)
                                                                    (Etempvar _t'43 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'31 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'40 tuint)
                                                                    (Etempvar _t'41 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'32)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'38 tuint)
                                                                    (Etempvar _t'39 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'32 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'36 tuint)
                                                                    (Etempvar _t'37 tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'33)
                                                                    (Evar _rol32 
                                                                    (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Ebinop Oxor
                                                                    (Etempvar _t'34 tuint)
                                                                    (Etempvar _t'35 tuint)
                                                                    tuint) ::
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _x (tptr tuint))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'33 tuint)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 2) tint)
            tint))))))
|}.

Definition f_chacha_block_generic := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) ::
                (_out, (tptr tuchar)) :: (_nrounds, tint) :: nil);
  fn_vars := ((_permuted_state, (Tstruct _chacha_state noattr)) :: nil);
  fn_temps := ((_i, tint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                    (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                (Etempvar _i tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield (Evar _permuted_state (Tstruct _chacha_state noattr))
                  _x (tarray tuint 16)) (Etempvar _i tint) (tptr tuint))
              tuint) (Etempvar _t'4 tuint))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _chacha_permute (Tfunction
                              ((tptr (Tstruct _chacha_state noattr)) ::
                               tint :: nil) tvoid cc_default))
      ((Eaddrof (Evar _permuted_state (Tstruct _chacha_state noattr))
         (tptr (Tstruct _chacha_state noattr))) ::
       (Etempvar _nrounds tint) :: nil))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Ebinop Odiv (Esizeof (tarray tuint 16) tulong)
                             (Esizeof tuint tulong) tulong) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Evar _permuted_state (Tstruct _chacha_state noattr))
                      _x (tarray tuint 16)) (Etempvar _i tint) (tptr tuint))
                  tuint))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                          (Tstruct _chacha_state noattr)) _x
                        (tarray tuint 16)) (Etempvar _i tint) (tptr tuint))
                    tuint))
                (Scall None
                  (Evar _put_unaligned_le32 (Tfunction
                                              (tuint :: (tptr tvoid) :: nil)
                                              tvoid cc_default))
                  ((Ebinop Oadd (Etempvar _t'2 tuint) (Etempvar _t'3 tuint)
                     tuint) ::
                   (Ebinop Oadd (Etempvar _out (tptr tuchar))
                     (Ebinop Omul (Etempvar _i tint) (Esizeof tuint tulong)
                       tulong) (tptr tuchar)) :: nil)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                    (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                    (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint)
            (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
        (Scall None
          (Evar _chacha_zeroize_state (Tfunction
                                        ((tptr (Tstruct _chacha_state noattr)) ::
                                         nil) tvoid cc_default))
          ((Eaddrof (Evar _permuted_state (Tstruct _chacha_state noattr))
             (tptr (Tstruct _chacha_state noattr))) :: nil))))))
|}.

Definition f_hchacha_block_generic := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_state, (tptr (Tstruct _chacha_state noattr))) ::
                (_out, (tptr tuint)) :: (_nrounds, tint) :: nil);
  fn_vars := ((_permuted_state, (Tstruct _chacha_state noattr)) :: nil);
  fn_temps := ((_i, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _chacha_state noattr)))
                    (Tstruct _chacha_state noattr)) _x (tarray tuint 16))
                (Etempvar _i tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield (Evar _permuted_state (Tstruct _chacha_state noattr))
                  _x (tarray tuint 16)) (Etempvar _i tint) (tptr tuint))
              tuint) (Etempvar _t'3 tuint))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _chacha_permute (Tfunction
                              ((tptr (Tstruct _chacha_state noattr)) ::
                               tint :: nil) tvoid cc_default))
      ((Eaddrof (Evar _permuted_state (Tstruct _chacha_state noattr))
         (tptr (Tstruct _chacha_state noattr))) ::
       (Etempvar _nrounds tint) :: nil))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 4) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Evar _permuted_state (Tstruct _chacha_state noattr))
                        _x (tarray tuint 16)) (Etempvar _i tint)
                      (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _out (tptr tuint))
                      (Etempvar _i tint) (tptr tuint)) tuint)
                  (Etempvar _t'2 tuint)))
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Evar _permuted_state (Tstruct _chacha_state noattr))
                        _x (tarray tuint 16))
                      (Ebinop Oadd (Econst_int (Int.repr 12) tint)
                        (Etempvar _i tint) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _out (tptr tuint))
                      (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                        (Etempvar _i tint) tint) (tptr tuint)) tuint)
                  (Etempvar _t'1 tuint)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Scall None
        (Evar _chacha_zeroize_state (Tfunction
                                      ((tptr (Tstruct _chacha_state noattr)) ::
                                       nil) tvoid cc_default))
        ((Eaddrof (Evar _permuted_state (Tstruct _chacha_state noattr))
           (tptr (Tstruct _chacha_state noattr))) :: nil)))))
|}.

Definition composites : list composite_definition :=
(Composite _chacha_state Struct
   (Member_plain _x (tarray tuint 16) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tulong :: nil) (tptr tvoid) cc_default)) ::
 (_memzero_explicit, Gfun(Internal f_memzero_explicit)) ::
 (_rol32, Gfun(Internal f_rol32)) ::
 (_put_unaligned_le32, Gfun(Internal f_put_unaligned_le32)) ::
 (_chacha_zeroize_state, Gfun(Internal f_chacha_zeroize_state)) ::
 (_chacha_permute, Gfun(Internal f_chacha_permute)) ::
 (_chacha_block_generic, Gfun(Internal f_chacha_block_generic)) ::
 (_hchacha_block_generic, Gfun(Internal f_hchacha_block_generic)) :: nil).

Definition public_idents : list ident :=
(_hchacha_block_generic :: _chacha_block_generic :: _memset ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


