(* blake2s_compress_generic: the body of the while loop over the blocks (Clight of src/blake2s/code.v, verbatim). *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.blake2s.code.

Definition b2s_step_stmt : statement :=
(Ssequence
      (Scall None
        (Evar _blake2s_increment_counter (Tfunction
                                           ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                            tuint :: nil) tvoid cc_default))
        ((Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _inc tuint) :: nil))
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
                (Scall (Some _t'2)
                  (Evar _get_unaligned_le32 (Tfunction ((tptr tvoid) :: nil)
                                              tuint cc_default))
                  ((Ebinop Oadd (Etempvar _data (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _m (tarray tuint 16))
                      (Etempvar _i tint) (tptr tuint)) tuint)
                  (Etempvar _t'2 tuint))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 8) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'202
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                            (Tstruct _blake2s_ctx noattr)) _h
                          (tarray tuint 8)) (Etempvar _i tint) (tptr tuint))
                      tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _v (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint)
                    (Etempvar _t'202 tuint))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _v (tarray tuint 16))
                  (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr 1779033703) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _v (tarray tuint 16))
                    (Econst_int (Int.repr 9) tint) (tptr tuint)) tuint)
                (Econst_int (Int.repr (-1150833019)) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _v (tarray tuint 16))
                      (Econst_int (Int.repr 10) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 1013904242) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _v (tarray tuint 16))
                        (Econst_int (Int.repr 11) tint) (tptr tuint)) tuint)
                    (Econst_int (Int.repr (-1521486534)) tint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'201
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                (Tstruct _blake2s_ctx noattr)) _t
                              (tarray tuint 2))
                            (Econst_int (Int.repr 0) tint) (tptr tuint))
                          tuint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _v (tarray tuint 16))
                            (Econst_int (Int.repr 12) tint) (tptr tuint))
                          tuint)
                        (Ebinop Oxor (Econst_int (Int.repr 1359893119) tint)
                          (Etempvar _t'201 tuint) tuint)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'200
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                  (Tstruct _blake2s_ctx noattr)) _t
                                (tarray tuint 2))
                              (Econst_int (Int.repr 1) tint) (tptr tuint))
                            tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _v (tarray tuint 16))
                              (Econst_int (Int.repr 13) tint) (tptr tuint))
                            tuint)
                          (Ebinop Oxor
                            (Econst_int (Int.repr (-1694144372)) tint)
                            (Etempvar _t'200 tuint) tuint)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'199
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                    (Tstruct _blake2s_ctx noattr)) _f
                                  (tarray tuint 2))
                                (Econst_int (Int.repr 0) tint) (tptr tuint))
                              tuint))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _v (tarray tuint 16))
                                (Econst_int (Int.repr 14) tint) (tptr tuint))
                              tuint)
                            (Ebinop Oxor
                              (Econst_int (Int.repr 528734635) tint)
                              (Etempvar _t'199 tuint) tuint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'198
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                      (Tstruct _blake2s_ctx noattr)) _f
                                    (tarray tuint 2))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _v (tarray tuint 16))
                                  (Econst_int (Int.repr 15) tint)
                                  (tptr tuint)) tuint)
                              (Ebinop Oxor
                                (Econst_int (Int.repr 1541459225) tint)
                                (Etempvar _t'198 tuint) tuint)))
                          (Ssequence
                            (Ssequence
                              (Sset _r (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                                 (Econst_int (Int.repr 10) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'194
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _v (tarray tuint 16))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _t'195
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _v (tarray tuint 16))
                                                  (Econst_int (Int.repr 4) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _t'196
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                        (Etempvar _r tint)
                                                        (tptr (tarray tuchar 16)))
                                                      (tarray tuchar 16))
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 2) tint)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 0) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar))
                                              (Ssequence
                                                (Sset _t'197
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _m (tarray tuint 16))
                                                      (Etempvar _t'196 tuchar)
                                                      (tptr tuint)) tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'194 tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'195 tuint)
                                                      (Etempvar _t'197 tuint)
                                                      tuint) tuint))))))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'192
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 12) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'193
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tuint)) tuint))
                                                (Scall (Some _t'3)
                                                  (Evar _ror32 (Tfunction
                                                                 (tuint ::
                                                                  tuint ::
                                                                  nil) tuint
                                                                 cc_default))
                                                  ((Ebinop Oxor
                                                     (Etempvar _t'192 tuint)
                                                     (Etempvar _t'193 tuint)
                                                     tuint) ::
                                                   (Econst_int (Int.repr 16) tint) ::
                                                   nil))))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _v (tarray tuint 16))
                                                  (Econst_int (Int.repr 12) tint)
                                                  (tptr tuint)) tuint)
                                              (Etempvar _t'3 tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'190
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 8) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'191
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 12) tint)
                                                      (tptr tuint)) tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 8) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'190 tuint)
                                                    (Etempvar _t'191 tuint)
                                                    tuint))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'188
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 4) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'189
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 8) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Scall (Some _t'4)
                                                      (Evar _ror32 (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                      ((Ebinop Oxor
                                                         (Etempvar _t'188 tuint)
                                                         (Etempvar _t'189 tuint)
                                                         tuint) ::
                                                       (Econst_int (Int.repr 12) tint) ::
                                                       nil))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 4) tint)
                                                      (tptr tuint)) tuint)
                                                  (Etempvar _t'4 tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'184
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'185
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 4) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'186
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                (Etempvar _r tint)
                                                                (tptr (tarray tuchar 16)))
                                                              (tarray tuchar 16))
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 2) tint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'187
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _m (tarray tuint 16))
                                                              (Etempvar _t'186 tuchar)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'184 tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'185 tuint)
                                                              (Etempvar _t'187 tuint)
                                                              tuint) tuint))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'182
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 12) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'183
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'5)
                                                          (Evar _ror32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'182 tuint)
                                                             (Etempvar _t'183 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 8) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 12) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'5 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'180
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 8) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'181
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 12) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 8) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'180 tuint)
                                                            (Etempvar _t'181 tuint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'178
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 4) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'179
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'6)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'178 tuint)
                                                               (Etempvar _t'179 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 7) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 4) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'6 tuint))))))))))
                                      Sbreak)
                                    (Ssequence
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'174
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _v (tarray tuint 16))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _t'175
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 5) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'176
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                          (Etempvar _r tint)
                                                          (tptr (tarray tuchar 16)))
                                                        (tarray tuchar 16))
                                                      (Ebinop Oadd
                                                        (Ebinop Omul
                                                          (Econst_int (Int.repr 2) tint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tint)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint) (tptr tuchar))
                                                    tuchar))
                                                (Ssequence
                                                  (Sset _t'177
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _m (tarray tuint 16))
                                                        (Etempvar _t'176 tuchar)
                                                        (tptr tuint)) tuint))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'174 tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'175 tuint)
                                                        (Etempvar _t'177 tuint)
                                                        tuint) tuint))))))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'172
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 13) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'173
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint)) tuint))
                                                  (Scall (Some _t'7)
                                                    (Evar _ror32 (Tfunction
                                                                   (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                   tuint
                                                                   cc_default))
                                                    ((Ebinop Oxor
                                                       (Etempvar _t'172 tuint)
                                                       (Etempvar _t'173 tuint)
                                                       tuint) ::
                                                     (Econst_int (Int.repr 16) tint) ::
                                                     nil))))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 13) tint)
                                                    (tptr tuint)) tuint)
                                                (Etempvar _t'7 tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'170
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 9) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'171
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 13) tint)
                                                        (tptr tuint)) tuint))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 9) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'170 tuint)
                                                      (Etempvar _t'171 tuint)
                                                      tuint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'168
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'169
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 9) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Scall (Some _t'8)
                                                        (Evar _ror32 
                                                        (Tfunction
                                                          (tuint :: tuint ::
                                                           nil) tuint
                                                          cc_default))
                                                        ((Ebinop Oxor
                                                           (Etempvar _t'168 tuint)
                                                           (Etempvar _t'169 tuint)
                                                           tuint) ::
                                                         (Econst_int (Int.repr 12) tint) ::
                                                         nil))))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 5) tint)
                                                        (tptr tuint)) tuint)
                                                    (Etempvar _t'8 tuint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'164
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'165
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 5) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'166
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                  (Etempvar _r tint)
                                                                  (tptr (tarray tuchar 16)))
                                                                (tarray tuchar 16))
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'167
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _m (tarray tuint 16))
                                                                (Etempvar _t'166 tuchar)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'164 tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'165 tuint)
                                                                (Etempvar _t'167 tuint)
                                                                tuint) tuint))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'162
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 13) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'163
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'9)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'162 tuint)
                                                               (Etempvar _t'163 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 8) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 13) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'9 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'160
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 9) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'161
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 13) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 9) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'160 tuint)
                                                              (Etempvar _t'161 tuint)
                                                              tuint))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'158
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 5) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'159
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 9) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'10)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'158 tuint)
                                                                 (Etempvar _t'159 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 7) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 5) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'10 tuint))))))))))
                                        Sbreak)
                                      (Ssequence
                                        (Sloop
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'154
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 2) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'155
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 6) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'156
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                            (Etempvar _r tint)
                                                            (tptr (tarray tuchar 16)))
                                                          (tarray tuchar 16))
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 2) tint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tint)
                                                          (Econst_int (Int.repr 0) tint)
                                                          tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _t'157
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _m (tarray tuint 16))
                                                          (Etempvar _t'156 tuchar)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 2) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'154 tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'155 tuint)
                                                          (Etempvar _t'157 tuint)
                                                          tuint) tuint))))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'152
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 14) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'153
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 2) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Scall (Some _t'11)
                                                      (Evar _ror32 (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                      ((Ebinop Oxor
                                                         (Etempvar _t'152 tuint)
                                                         (Etempvar _t'153 tuint)
                                                         tuint) ::
                                                       (Econst_int (Int.repr 16) tint) ::
                                                       nil))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 14) tint)
                                                      (tptr tuint)) tuint)
                                                  (Etempvar _t'11 tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'150
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 10) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'151
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 14) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 10) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'150 tuint)
                                                        (Etempvar _t'151 tuint)
                                                        tuint))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'148
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 6) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'149
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 10) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'12)
                                                          (Evar _ror32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'148 tuint)
                                                             (Etempvar _t'149 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 12) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 6) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'12 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'144
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 2) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'145
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 6) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'146
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                  (tarray tuchar 16))
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'147
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _m (tarray tuint 16))
                                                                  (Etempvar _t'146 tuchar)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'144 tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'145 tuint)
                                                                  (Etempvar _t'147 tuint)
                                                                  tuint)
                                                                tuint))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'142
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 14) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'143
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'13)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'142 tuint)
                                                                 (Etempvar _t'143 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 8) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 14) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'13 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'140
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 10) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'141
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 14) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 10) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'140 tuint)
                                                                (Etempvar _t'141 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'138
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 6) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'139
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Scall (Some _t'14)
                                                                (Evar _ror32 
                                                                (Tfunction
                                                                  (tuint ::
                                                                   tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Ebinop Oxor
                                                                   (Etempvar _t'138 tuint)
                                                                   (Etempvar _t'139 tuint)
                                                                   tuint) ::
                                                                 (Econst_int (Int.repr 7) tint) ::
                                                                 nil))))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 6) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Etempvar _t'14 tuint))))))))))
                                          Sbreak)
                                        (Ssequence
                                          (Sloop
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'134
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 3) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'135
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 7) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'136
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                              (Etempvar _r tint)
                                                              (tptr (tarray tuchar 16)))
                                                            (tarray tuchar 16))
                                                          (Ebinop Oadd
                                                            (Ebinop Omul
                                                              (Econst_int (Int.repr 2) tint)
                                                              (Econst_int (Int.repr 3) tint)
                                                              tint)
                                                            (Econst_int (Int.repr 0) tint)
                                                            tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _t'137
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _m (tarray tuint 16))
                                                            (Etempvar _t'136 tuchar)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'134 tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'135 tuint)
                                                            (Etempvar _t'137 tuint)
                                                            tuint) tuint))))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'132
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 15) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'133
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Scall (Some _t'15)
                                                        (Evar _ror32 
                                                        (Tfunction
                                                          (tuint :: tuint ::
                                                           nil) tuint
                                                          cc_default))
                                                        ((Ebinop Oxor
                                                           (Etempvar _t'132 tuint)
                                                           (Etempvar _t'133 tuint)
                                                           tuint) ::
                                                         (Econst_int (Int.repr 16) tint) ::
                                                         nil))))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 15) tint)
                                                        (tptr tuint)) tuint)
                                                    (Etempvar _t'15 tuint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'130
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 11) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'131
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 15) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 11) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'130 tuint)
                                                          (Etempvar _t'131 tuint)
                                                          tuint))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'128
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'129
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 11) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'16)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'128 tuint)
                                                               (Etempvar _t'129 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 12) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 7) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'16 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'124
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 3) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'125
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 7) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'126
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                  (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Ssequence
                                                              (Sset _t'127
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'126 tuchar)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'124 tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'125 tuint)
                                                                    (Etempvar _t'127 tuint)
                                                                    tuint)
                                                                  tuint))))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'122
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 15) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'123
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Scall (Some _t'17)
                                                                (Evar _ror32 
                                                                (Tfunction
                                                                  (tuint ::
                                                                   tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Ebinop Oxor
                                                                   (Etempvar _t'122 tuint)
                                                                   (Etempvar _t'123 tuint)
                                                                   tuint) ::
                                                                 (Econst_int (Int.repr 8) tint) ::
                                                                 nil))))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 15) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Etempvar _t'17 tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'120
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 11) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'121
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'120 tuint)
                                                                  (Etempvar _t'121 tuint)
                                                                  tuint))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'118
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'119
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'18)
                                                                  (Evar _ror32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'118 tuint)
                                                                    (Etempvar _t'119 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 7) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'18 tuint))))))))))
                                            Sbreak)
                                          (Ssequence
                                            (Sloop
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'114
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'115
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'116
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                (Etempvar _r tint)
                                                                (tptr (tarray tuchar 16)))
                                                              (tarray tuchar 16))
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 2) tint)
                                                                (Econst_int (Int.repr 4) tint)
                                                                tint)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'117
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _m (tarray tuint 16))
                                                              (Etempvar _t'116 tuchar)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'114 tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'115 tuint)
                                                              (Etempvar _t'117 tuint)
                                                              tuint) tuint))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'112
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 15) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'113
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'19)
                                                          (Evar _ror32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'112 tuint)
                                                             (Etempvar _t'113 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 16) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 15) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'19 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'110
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 10) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'111
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 15) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 10) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'110 tuint)
                                                            (Etempvar _t'111 tuint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'108
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 5) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'109
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 10) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'20)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'108 tuint)
                                                                 (Etempvar _t'109 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 12) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 5) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'20 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'104
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 0) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'105
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 5) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'106
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _t'107
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'106 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'104 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'105 tuint)
                                                                    (Etempvar _t'107 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'102
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'103
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'21)
                                                                  (Evar _ror32 
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
                                                                   (Econst_int (Int.repr 8) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 15) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'21 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'100
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'101
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'100 tuint)
                                                                    (Etempvar _t'101 tuint)
                                                                    tuint))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'98
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'99
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Scall (Some _t'22)
                                                                    (Evar _ror32 
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
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Etempvar _t'22 tuint))))))))))
                                              Sbreak)
                                            (Ssequence
                                              (Sloop
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'94
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'95
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 6) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'96
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                  (Etempvar _r tint)
                                                                  (tptr (tarray tuchar 16)))
                                                                (tarray tuchar 16))
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Econst_int (Int.repr 5) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'97
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _m (tarray tuint 16))
                                                                (Etempvar _t'96 tuchar)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'94 tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'95 tuint)
                                                                (Etempvar _t'97 tuint)
                                                                tuint) tuint))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'92
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 12) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'93
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'23)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'92 tuint)
                                                               (Etempvar _t'93 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 16) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 12) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'23 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'90
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 11) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'91
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 12) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 11) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'90 tuint)
                                                              (Etempvar _t'91 tuint)
                                                              tuint))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'88
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 6) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'89
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Scall (Some _t'24)
                                                                (Evar _ror32 
                                                                (Tfunction
                                                                  (tuint ::
                                                                   tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Ebinop Oxor
                                                                   (Etempvar _t'88 tuint)
                                                                   (Etempvar _t'89 tuint)
                                                                   tuint) ::
                                                                 (Econst_int (Int.repr 12) tint) ::
                                                                 nil))))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 6) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Etempvar _t'24 tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'84
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'85
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'86
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sset _t'87
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'86 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'84 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'85 tuint)
                                                                    (Etempvar _t'87 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'82
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'83
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Scall (Some _t'25)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Etempvar _t'25 tuint)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'80
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'81
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'80 tuint)
                                                                    (Etempvar _t'81 tuint)
                                                                    tuint))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'78
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'79
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'26)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'26 tuint))))))))))
                                                Sbreak)
                                              (Ssequence
                                                (Sloop
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'74
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 2) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'75
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'76
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                  (tarray tuchar 16))
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'77
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _m (tarray tuint 16))
                                                                  (Etempvar _t'76 tuchar)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'74 tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'75 tuint)
                                                                  (Etempvar _t'77 tuint)
                                                                  tuint)
                                                                tuint))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'72
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 13) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'73
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'27)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'72 tuint)
                                                                 (Etempvar _t'73 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 16) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 13) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'27 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'70
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'71
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 13) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'70 tuint)
                                                                (Etempvar _t'71 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'68
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'69
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'28)
                                                                  (Evar _ror32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'68 tuint)
                                                                    (Etempvar _t'69 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 12) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'28 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'64
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'65
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'66
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'67
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'66 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'64 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'65 tuint)
                                                                    (Etempvar _t'67 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'62
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'63
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'29)
                                                                    (Evar _ror32 
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
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'29 tuint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'60
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'61
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'60 tuint)
                                                                    (Etempvar _t'61 tuint)
                                                                    tuint))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'58
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'30)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'30 tuint))))))))))
                                                  Sbreak)
                                                (Sloop
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'54
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'55
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 4) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'56
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                  (tarray tuchar 16))
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'57
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _m (tarray tuint 16))
                                                                  (Etempvar _t'56 tuchar)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'54 tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'55 tuint)
                                                                  (Etempvar _t'57 tuint)
                                                                  tuint)
                                                                tuint))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'52
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 14) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'53
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'31)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'52 tuint)
                                                                 (Etempvar _t'53 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 16) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 14) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'31 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'50
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 9) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'51
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 14) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 9) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'50 tuint)
                                                                (Etempvar _t'51 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'48
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'49
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'32)
                                                                  (Evar _ror32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'48 tuint)
                                                                    (Etempvar _t'49 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 12) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'32 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'44
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'45
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'46
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'47
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'46 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'45 tuint)
                                                                    (Etempvar _t'47 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'42
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'43
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'33)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'33 tuint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'40
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'41
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'40 tuint)
                                                                    (Etempvar _t'41 tuint)
                                                                    tuint))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'34)
                                                                    (Evar _ror32 
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
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'34 tuint))))))))))
                                                  Sbreak)))))))))
                                (Sset _r
                                  (Ebinop Oadd (Etempvar _r tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Ssequence
                                (Sset _i (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tint)
                                                   (Econst_int (Int.repr 8) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'35
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                                (Tstruct _blake2s_ctx noattr))
                                              _h (tarray tuint 8))
                                            (Etempvar _i tint) (tptr tuint))
                                          tuint))
                                      (Ssequence
                                        (Sset _t'36
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _v (tarray tuint 16))
                                              (Etempvar _i tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sset _t'37
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _v (tarray tuint 16))
                                                (Ebinop Oadd
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tint) (tptr tuint)) tuint))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                                    (Tstruct _blake2s_ctx noattr))
                                                  _h (tarray tuint 8))
                                                (Etempvar _i tint)
                                                (tptr tuint)) tuint)
                                            (Ebinop Oxor
                                              (Etempvar _t'35 tuint)
                                              (Ebinop Oxor
                                                (Etempvar _t'36 tuint)
                                                (Etempvar _t'37 tuint) tuint)
                                              tuint))))))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Sset _data
                                  (Ebinop Oadd (Etempvar _data (tptr tuchar))
                                    (Econst_int (Int.repr 64) tint)
                                    (tptr tuchar)))
                                (Sset _nblocks
                                  (Ebinop Osub (Etempvar _nblocks tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))))))))))))))).

(* the loop over the 10 rounds: for (r = 0; r < 10; r++) { 8 G }  *)
Definition b2s_rloop_stmt : statement :=
(Ssequence
                              (Sset _r (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                                                 (Econst_int (Int.repr 10) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'194
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _v (tarray tuint 16))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _t'195
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _v (tarray tuint 16))
                                                  (Econst_int (Int.repr 4) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _t'196
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                        (Etempvar _r tint)
                                                        (tptr (tarray tuchar 16)))
                                                      (tarray tuchar 16))
                                                    (Ebinop Oadd
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 2) tint)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 0) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar))
                                              (Ssequence
                                                (Sset _t'197
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _m (tarray tuint 16))
                                                      (Etempvar _t'196 tuchar)
                                                      (tptr tuint)) tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'194 tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'195 tuint)
                                                      (Etempvar _t'197 tuint)
                                                      tuint) tuint))))))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'192
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 12) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'193
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tuint)) tuint))
                                                (Scall (Some _t'3)
                                                  (Evar _ror32 (Tfunction
                                                                 (tuint ::
                                                                  tuint ::
                                                                  nil) tuint
                                                                 cc_default))
                                                  ((Ebinop Oxor
                                                     (Etempvar _t'192 tuint)
                                                     (Etempvar _t'193 tuint)
                                                     tuint) ::
                                                   (Econst_int (Int.repr 16) tint) ::
                                                   nil))))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _v (tarray tuint 16))
                                                  (Econst_int (Int.repr 12) tint)
                                                  (tptr tuint)) tuint)
                                              (Etempvar _t'3 tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'190
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 8) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'191
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 12) tint)
                                                      (tptr tuint)) tuint))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 8) tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'190 tuint)
                                                    (Etempvar _t'191 tuint)
                                                    tuint))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'188
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 4) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'189
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 8) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Scall (Some _t'4)
                                                      (Evar _ror32 (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                      ((Ebinop Oxor
                                                         (Etempvar _t'188 tuint)
                                                         (Etempvar _t'189 tuint)
                                                         tuint) ::
                                                       (Econst_int (Int.repr 12) tint) ::
                                                       nil))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 4) tint)
                                                      (tptr tuint)) tuint)
                                                  (Etempvar _t'4 tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'184
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'185
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 4) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'186
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                (Etempvar _r tint)
                                                                (tptr (tarray tuchar 16)))
                                                              (tarray tuchar 16))
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 2) tint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'187
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _m (tarray tuint 16))
                                                              (Etempvar _t'186 tuchar)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'184 tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'185 tuint)
                                                              (Etempvar _t'187 tuint)
                                                              tuint) tuint))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'182
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 12) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'183
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'5)
                                                          (Evar _ror32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'182 tuint)
                                                             (Etempvar _t'183 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 8) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 12) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'5 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'180
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 8) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'181
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 12) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 8) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'180 tuint)
                                                            (Etempvar _t'181 tuint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'178
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 4) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'179
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'6)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'178 tuint)
                                                               (Etempvar _t'179 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 7) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 4) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'6 tuint))))))))))
                                      Sbreak)
                                    (Ssequence
                                      (Sloop
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'174
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _v (tarray tuint 16))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _t'175
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 5) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'176
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                          (Etempvar _r tint)
                                                          (tptr (tarray tuchar 16)))
                                                        (tarray tuchar 16))
                                                      (Ebinop Oadd
                                                        (Ebinop Omul
                                                          (Econst_int (Int.repr 2) tint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tint)
                                                        (Econst_int (Int.repr 0) tint)
                                                        tint) (tptr tuchar))
                                                    tuchar))
                                                (Ssequence
                                                  (Sset _t'177
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _m (tarray tuint 16))
                                                        (Etempvar _t'176 tuchar)
                                                        (tptr tuint)) tuint))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'174 tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'175 tuint)
                                                        (Etempvar _t'177 tuint)
                                                        tuint) tuint))))))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'172
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 13) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'173
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint)) tuint))
                                                  (Scall (Some _t'7)
                                                    (Evar _ror32 (Tfunction
                                                                   (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                   tuint
                                                                   cc_default))
                                                    ((Ebinop Oxor
                                                       (Etempvar _t'172 tuint)
                                                       (Etempvar _t'173 tuint)
                                                       tuint) ::
                                                     (Econst_int (Int.repr 16) tint) ::
                                                     nil))))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 13) tint)
                                                    (tptr tuint)) tuint)
                                                (Etempvar _t'7 tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'170
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 9) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'171
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 13) tint)
                                                        (tptr tuint)) tuint))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 9) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'170 tuint)
                                                      (Etempvar _t'171 tuint)
                                                      tuint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'168
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'169
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 9) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Scall (Some _t'8)
                                                        (Evar _ror32 
                                                        (Tfunction
                                                          (tuint :: tuint ::
                                                           nil) tuint
                                                          cc_default))
                                                        ((Ebinop Oxor
                                                           (Etempvar _t'168 tuint)
                                                           (Etempvar _t'169 tuint)
                                                           tuint) ::
                                                         (Econst_int (Int.repr 12) tint) ::
                                                         nil))))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 5) tint)
                                                        (tptr tuint)) tuint)
                                                    (Etempvar _t'8 tuint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'164
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'165
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 5) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'166
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                  (Etempvar _r tint)
                                                                  (tptr (tarray tuchar 16)))
                                                                (tarray tuchar 16))
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'167
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _m (tarray tuint 16))
                                                                (Etempvar _t'166 tuchar)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'164 tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'165 tuint)
                                                                (Etempvar _t'167 tuint)
                                                                tuint) tuint))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'162
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 13) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'163
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'9)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'162 tuint)
                                                               (Etempvar _t'163 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 8) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 13) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'9 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'160
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 9) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'161
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 13) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 9) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'160 tuint)
                                                              (Etempvar _t'161 tuint)
                                                              tuint))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'158
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 5) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'159
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 9) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'10)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'158 tuint)
                                                                 (Etempvar _t'159 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 7) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 5) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'10 tuint))))))))))
                                        Sbreak)
                                      (Ssequence
                                        (Sloop
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'154
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _v (tarray tuint 16))
                                                    (Econst_int (Int.repr 2) tint)
                                                    (tptr tuint)) tuint))
                                              (Ssequence
                                                (Sset _t'155
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 6) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'156
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                            (Etempvar _r tint)
                                                            (tptr (tarray tuchar 16)))
                                                          (tarray tuchar 16))
                                                        (Ebinop Oadd
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 2) tint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tint)
                                                          (Econst_int (Int.repr 0) tint)
                                                          tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _t'157
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _m (tarray tuint 16))
                                                          (Etempvar _t'156 tuchar)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 2) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'154 tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'155 tuint)
                                                          (Etempvar _t'157 tuint)
                                                          tuint) tuint))))))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'152
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 14) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'153
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 2) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Scall (Some _t'11)
                                                      (Evar _ror32 (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                      ((Ebinop Oxor
                                                         (Etempvar _t'152 tuint)
                                                         (Etempvar _t'153 tuint)
                                                         tuint) ::
                                                       (Econst_int (Int.repr 16) tint) ::
                                                       nil))))
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 14) tint)
                                                      (tptr tuint)) tuint)
                                                  (Etempvar _t'11 tuint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'150
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 10) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'151
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 14) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 10) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'150 tuint)
                                                        (Etempvar _t'151 tuint)
                                                        tuint))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'148
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 6) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'149
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 10) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'12)
                                                          (Evar _ror32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'148 tuint)
                                                             (Etempvar _t'149 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 12) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 6) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'12 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'144
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 2) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'145
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 6) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'146
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                  (tarray tuchar 16))
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'147
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _m (tarray tuint 16))
                                                                  (Etempvar _t'146 tuchar)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'144 tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'145 tuint)
                                                                  (Etempvar _t'147 tuint)
                                                                  tuint)
                                                                tuint))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'142
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 14) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'143
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'13)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'142 tuint)
                                                                 (Etempvar _t'143 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 8) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 14) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'13 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'140
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 10) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'141
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 14) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 10) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'140 tuint)
                                                                (Etempvar _t'141 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'138
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 6) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'139
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Scall (Some _t'14)
                                                                (Evar _ror32 
                                                                (Tfunction
                                                                  (tuint ::
                                                                   tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Ebinop Oxor
                                                                   (Etempvar _t'138 tuint)
                                                                   (Etempvar _t'139 tuint)
                                                                   tuint) ::
                                                                 (Econst_int (Int.repr 7) tint) ::
                                                                 nil))))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 6) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Etempvar _t'14 tuint))))))))))
                                          Sbreak)
                                        (Ssequence
                                          (Sloop
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'134
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _v (tarray tuint 16))
                                                      (Econst_int (Int.repr 3) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'135
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 7) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'136
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                              (Etempvar _r tint)
                                                              (tptr (tarray tuchar 16)))
                                                            (tarray tuchar 16))
                                                          (Ebinop Oadd
                                                            (Ebinop Omul
                                                              (Econst_int (Int.repr 2) tint)
                                                              (Econst_int (Int.repr 3) tint)
                                                              tint)
                                                            (Econst_int (Int.repr 0) tint)
                                                            tint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _t'137
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _m (tarray tuint 16))
                                                            (Etempvar _t'136 tuchar)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'134 tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'135 tuint)
                                                            (Etempvar _t'137 tuint)
                                                            tuint) tuint))))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'132
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 15) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'133
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Scall (Some _t'15)
                                                        (Evar _ror32 
                                                        (Tfunction
                                                          (tuint :: tuint ::
                                                           nil) tuint
                                                          cc_default))
                                                        ((Ebinop Oxor
                                                           (Etempvar _t'132 tuint)
                                                           (Etempvar _t'133 tuint)
                                                           tuint) ::
                                                         (Econst_int (Int.repr 16) tint) ::
                                                         nil))))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 15) tint)
                                                        (tptr tuint)) tuint)
                                                    (Etempvar _t'15 tuint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'130
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 11) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'131
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 15) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 11) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'130 tuint)
                                                          (Etempvar _t'131 tuint)
                                                          tuint))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'128
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'129
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 11) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'16)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'128 tuint)
                                                               (Etempvar _t'129 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 12) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 7) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'16 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'124
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 3) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'125
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 7) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'126
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                  (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                  (tptr tuchar))
                                                                tuchar))
                                                            (Ssequence
                                                              (Sset _t'127
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'126 tuchar)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'124 tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'125 tuint)
                                                                    (Etempvar _t'127 tuint)
                                                                    tuint)
                                                                  tuint))))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'122
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 15) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'123
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Scall (Some _t'17)
                                                                (Evar _ror32 
                                                                (Tfunction
                                                                  (tuint ::
                                                                   tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Ebinop Oxor
                                                                   (Etempvar _t'122 tuint)
                                                                   (Etempvar _t'123 tuint)
                                                                   tuint) ::
                                                                 (Econst_int (Int.repr 8) tint) ::
                                                                 nil))))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 15) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Etempvar _t'17 tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'120
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 11) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'121
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'120 tuint)
                                                                  (Etempvar _t'121 tuint)
                                                                  tuint))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'118
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'119
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'18)
                                                                  (Evar _ror32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'118 tuint)
                                                                    (Etempvar _t'119 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 7) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'18 tuint))))))))))
                                            Sbreak)
                                          (Ssequence
                                            (Sloop
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'114
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _v (tarray tuint 16))
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _t'115
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 5) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'116
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                (Etempvar _r tint)
                                                                (tptr (tarray tuchar 16)))
                                                              (tarray tuchar 16))
                                                            (Ebinop Oadd
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 2) tint)
                                                                (Econst_int (Int.repr 4) tint)
                                                                tint)
                                                              (Econst_int (Int.repr 0) tint)
                                                              tint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _t'117
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _m (tarray tuint 16))
                                                              (Etempvar _t'116 tuchar)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'114 tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'115 tuint)
                                                              (Etempvar _t'117 tuint)
                                                              tuint) tuint))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'112
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 15) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'113
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 0) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Scall (Some _t'19)
                                                          (Evar _ror32 
                                                          (Tfunction
                                                            (tuint ::
                                                             tuint :: nil)
                                                            tuint cc_default))
                                                          ((Ebinop Oxor
                                                             (Etempvar _t'112 tuint)
                                                             (Etempvar _t'113 tuint)
                                                             tuint) ::
                                                           (Econst_int (Int.repr 16) tint) ::
                                                           nil))))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 15) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _t'19 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'110
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 10) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'111
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 15) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 10) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'110 tuint)
                                                            (Etempvar _t'111 tuint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'108
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 5) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'109
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 10) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'20)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'108 tuint)
                                                                 (Etempvar _t'109 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 12) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 5) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'20 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'104
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 0) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'105
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 5) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'106
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _t'107
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'106 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'104 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'105 tuint)
                                                                    (Etempvar _t'107 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'102
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'103
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'21)
                                                                  (Evar _ror32 
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
                                                                   (Econst_int (Int.repr 8) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 15) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'21 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'100
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'101
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'100 tuint)
                                                                    (Etempvar _t'101 tuint)
                                                                    tuint))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'98
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'99
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 10) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Scall (Some _t'22)
                                                                    (Evar _ror32 
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
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Etempvar _t'22 tuint))))))))))
                                              Sbreak)
                                            (Ssequence
                                              (Sloop
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'94
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _v (tarray tuint 16))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _t'95
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 6) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'96
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                  (Etempvar _r tint)
                                                                  (tptr (tarray tuchar 16)))
                                                                (tarray tuchar 16))
                                                              (Ebinop Oadd
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (Econst_int (Int.repr 5) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _t'97
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _m (tarray tuint 16))
                                                                (Etempvar _t'96 tuchar)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'94 tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'95 tuint)
                                                                (Etempvar _t'97 tuint)
                                                                tuint) tuint))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'92
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 12) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'93
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Scall (Some _t'23)
                                                            (Evar _ror32 
                                                            (Tfunction
                                                              (tuint ::
                                                               tuint :: nil)
                                                              tuint
                                                              cc_default))
                                                            ((Ebinop Oxor
                                                               (Etempvar _t'92 tuint)
                                                               (Etempvar _t'93 tuint)
                                                               tuint) ::
                                                             (Econst_int (Int.repr 16) tint) ::
                                                             nil))))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 12) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'23 tuint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'90
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 11) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'91
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 12) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 11) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'90 tuint)
                                                              (Etempvar _t'91 tuint)
                                                              tuint))))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'88
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 6) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'89
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Scall (Some _t'24)
                                                                (Evar _ror32 
                                                                (Tfunction
                                                                  (tuint ::
                                                                   tuint ::
                                                                   nil) tuint
                                                                  cc_default))
                                                                ((Ebinop Oxor
                                                                   (Etempvar _t'88 tuint)
                                                                   (Etempvar _t'89 tuint)
                                                                   tuint) ::
                                                                 (Econst_int (Int.repr 12) tint) ::
                                                                 nil))))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 6) tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Etempvar _t'24 tuint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'84
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _t'85
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'86
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sset _t'87
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'86 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'84 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'85 tuint)
                                                                    (Etempvar _t'87 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'82
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'83
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Scall (Some _t'25)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                  tuint)
                                                                (Etempvar _t'25 tuint)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'80
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'81
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'80 tuint)
                                                                    (Etempvar _t'81 tuint)
                                                                    tuint))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'78
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'79
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'26)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'26 tuint))))))))))
                                                Sbreak)
                                              (Ssequence
                                                (Sloop
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'74
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 2) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'75
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 7) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'76
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                  (tarray tuchar 16))
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'77
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _m (tarray tuint 16))
                                                                  (Etempvar _t'76 tuchar)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'74 tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'75 tuint)
                                                                  (Etempvar _t'77 tuint)
                                                                  tuint)
                                                                tuint))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'72
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 13) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'73
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 2) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'27)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'72 tuint)
                                                                 (Etempvar _t'73 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 16) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 13) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'27 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'70
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 8) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'71
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 13) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'70 tuint)
                                                                (Etempvar _t'71 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'68
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'69
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'28)
                                                                  (Evar _ror32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'68 tuint)
                                                                    (Etempvar _t'69 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 12) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'28 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'64
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'65
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'66
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'67
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'66 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'64 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'65 tuint)
                                                                    (Etempvar _t'67 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'62
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'63
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'29)
                                                                    (Evar _ror32 
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
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'29 tuint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'60
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'61
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'60 tuint)
                                                                    (Etempvar _t'61 tuint)
                                                                    tuint))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'58
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'30)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 7) tint) ::
                                                                    nil))))
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'30 tuint))))))))))
                                                  Sbreak)
                                                (Sloop
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'54
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _v (tarray tuint 16))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'55
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 4) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _t'56
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                  (tarray tuchar 16))
                                                                (Ebinop Oadd
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (tptr tuchar))
                                                              tuchar))
                                                          (Ssequence
                                                            (Sset _t'57
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _m (tarray tuint 16))
                                                                  (Etempvar _t'56 tuchar)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'54 tuint)
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'55 tuint)
                                                                  (Etempvar _t'57 tuint)
                                                                  tuint)
                                                                tuint))))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'52
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 14) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'53
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 3) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Scall (Some _t'31)
                                                              (Evar _ror32 
                                                              (Tfunction
                                                                (tuint ::
                                                                 tuint ::
                                                                 nil) tuint
                                                                cc_default))
                                                              ((Ebinop Oxor
                                                                 (Etempvar _t'52 tuint)
                                                                 (Etempvar _t'53 tuint)
                                                                 tuint) ::
                                                               (Econst_int (Int.repr 16) tint) ::
                                                               nil))))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _v (tarray tuint 16))
                                                              (Econst_int (Int.repr 14) tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Etempvar _t'31 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'50
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _v (tarray tuint 16))
                                                                (Econst_int (Int.repr 9) tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'51
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 14) tint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 9) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'50 tuint)
                                                                (Etempvar _t'51 tuint)
                                                                tuint))))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'48
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'49
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Scall (Some _t'32)
                                                                  (Evar _ror32 
                                                                  (Tfunction
                                                                    (tuint ::
                                                                    tuint ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                  ((Ebinop Oxor
                                                                    (Etempvar _t'48 tuint)
                                                                    (Etempvar _t'49 tuint)
                                                                    tuint) ::
                                                                   (Econst_int (Int.repr 12) tint) ::
                                                                   nil))))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _v (tarray tuint 16))
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Etempvar _t'32 tuint)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'44
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _t'45
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _t'46
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _blake2s_sigma (tarray (tarray tuchar 16) 10))
                                                                    (Etempvar _r tint)
                                                                    (tptr (tarray tuchar 16)))
                                                                    (tarray tuchar 16))
                                                                    (Ebinop Oadd
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _t'47
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _m (tarray tuint 16))
                                                                    (Etempvar _t'46 tuchar)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'44 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'45 tuint)
                                                                    (Etempvar _t'47 tuint)
                                                                    tuint)
                                                                    tuint))))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'42
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'43
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'33)
                                                                    (Evar _ror32 
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
                                                                    (Econst_int (Int.repr 8) tint) ::
                                                                    nil))))
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                  (Etempvar _t'33 tuint)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'40
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'41
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'40 tuint)
                                                                    (Etempvar _t'41 tuint)
                                                                    tuint))))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'38
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'34)
                                                                    (Evar _ror32 
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
                                                                    (Evar _v (tarray tuint 16))
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Etempvar _t'34 tuint))))))))))
                                                  Sbreak)))))))))
                                (Sset _r
                                  (Ebinop Oadd (Etempvar _r tint)
                                    (Econst_int (Int.repr 1) tint) tint)))).

(* after the rounds: the feed-forward loop, data += 64, --nblocks *)
Definition b2s_feed_stmt : statement :=
(Ssequence
                              (Ssequence
                                (Sset _i (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tint)
                                                   (Econst_int (Int.repr 8) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'35
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                                (Tstruct _blake2s_ctx noattr))
                                              _h (tarray tuint 8))
                                            (Etempvar _i tint) (tptr tuint))
                                          tuint))
                                      (Ssequence
                                        (Sset _t'36
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _v (tarray tuint 16))
                                              (Etempvar _i tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sset _t'37
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _v (tarray tuint 16))
                                                (Ebinop Oadd
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tint) (tptr tuint)) tuint))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                                    (Tstruct _blake2s_ctx noattr))
                                                  _h (tarray tuint 8))
                                                (Etempvar _i tint)
                                                (tptr tuint)) tuint)
                                            (Ebinop Oxor
                                              (Etempvar _t'35 tuint)
                                              (Ebinop Oxor
                                                (Etempvar _t'36 tuint)
                                                (Etempvar _t'37 tuint) tuint)
                                              tuint))))))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Sset _data
                                  (Ebinop Oadd (Etempvar _data (tptr tuchar))
                                    (Econst_int (Int.repr 64) tint)
                                    (tptr tuchar)))
                                (Sset _nblocks
                                  (Ebinop Osub (Etempvar _nblocks tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))).
