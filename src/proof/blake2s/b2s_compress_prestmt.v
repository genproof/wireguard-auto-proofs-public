(* blake2s_compress_generic: the loop body split at the rounds (Clight of src/blake2s/code.v, verbatim):
   b2s_pre1 rest = counter, message words, rest; b2s_pre2 rest = h copy, IV, rest. *)
Require Import VST.floyd.proofauto.
Require Import WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stepstmt.

Definition b2s_pre1 (rest: statement) : statement :=
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
        rest)).

Definition b2s_pre2 (rest: statement) : statement :=
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
                          rest))))))))).

Definition b2s_iv (rest: statement) : statement :=
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
                          rest)))))))).

Lemma b2s_pre2_eq rest : exists hc, b2s_pre2 rest = Ssequence hc (b2s_iv rest).
Proof. eexists. reflexivity. Qed.

Lemma b2s_step_stmt_eq :
  b2s_step_stmt = b2s_pre1 (b2s_pre2 (Ssequence b2s_rloop_stmt b2s_feed_stmt)).
Proof. reflexivity. Qed.
