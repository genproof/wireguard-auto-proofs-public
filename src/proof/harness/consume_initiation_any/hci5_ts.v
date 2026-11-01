(* law consume_initiation_any: the harness's own
   function ts_step(t, up) (harness/consume_initiation_any.c: t = t +- 1 as a 96-bit big-endian number).  main uses
   it only to move A's latest timestamp to SOME 12 bytes next to the message's (the replay boundary); the law's
   model reads the timestamp from the snapshot taken afterwards, so the specification states only that the 12
   bytes stay 12 bytes.  Body at the world compspecs (the law's unit), for ANY varspecs and funspecs (it calls
   nothing). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require WgNoise.proof.libc.libc_bytes.
Require WgNoise.harness.x_consume_initiation_any.code.
Local Open Scope logic.

Module HT5 := WgNoise.harness.x_consume_initiation_any.code.

Definition hci5_ts_step_spec :=
  DECLARE HT5._ts_step
  WITH sh: share, t: val, T: list byte, up: int
  PRE [ tptr tuchar, tint ]
    PROP (writable_share sh; Zlength T = 12)
    PARAMS (t; Vint up)
    SEP (hbytes sh T t)
  POST [ tvoid ] EX T': list byte,
    PROP (Zlength T' = 12)
    RETURN ()
    SEP (hbytes sh T' t).

Section Body.
#[local] Existing Instance W_consume_initiation_any.

Lemma hci5_ts_hbytes sh T t :
  hbytes sh T t = @data_at W_consume_initiation_any sh (tarray tuchar (Zlength T)) (bytes T) t.
Proof. unfold hbytes. apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs. Qed.

Lemma hci5_ts_zext v : Vint (Int.zero_ext 8 v) = Vubyte (Byte.repr (Int.unsigned v)).
Proof.
  unfold Vubyte. f_equal. rewrite Byte.unsigned_repr_eq.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 v)). rewrite Int.zero_ext_mod by computable. reflexivity.
Qed.

Lemma hci5_ts_upd i U b : upd_Znth i (bytes U) (Vubyte b) = bytes (upd_Znth i U b).
Proof. unfold bytes. rewrite upd_Znth_map. reflexivity. Qed.

Lemma hci5_ts_body0 : semax_body [] [] HT5.f_ts_step hci5_ts_step_spec.
Proof.
  start_function.
  rewrite hci5_ts_hbytes, H.
  forward.
  forward_loop
    (EX i: Z, EX U: list byte,
       PROP (-1 <= i <= 11; Zlength U = 12)
       LOCAL (temp HT5._i (Vint (Int.repr i)); temp HT5._t t; temp HT5._up (Vint up))
       SEP (data_at sh (tarray tuchar 12) (bytes U) t))
    break: (EX U: list byte,
       PROP (Zlength U = 12)
       LOCAL ()
       SEP (data_at sh (tarray tuchar 12) (bytes U) t)).
  - Exists 11 T. entailer!.
  - Intros i U.
    forward_if.
    + assert_PROP (Zlength (bytes U) = 12) by (entailer!; unfold bytes; rewrite Zlength_map; auto).
      forward.
      { go_lower. unfold bytes; rewrite Znth_map by lia. apply prop_right. simpl. apply tc_val_Vubyte. }
      unfold bytes at 1. rewrite Znth_map by lia.
      forward.
      forward_if (EX v: int,
        PROP () LOCAL (temp HT5._t'1 (Vint v); temp HT5._old (Vubyte (Znth i U)); temp HT5._i (Vint (Int.repr i));
                       temp HT5._t t; temp HT5._up (Vint up))
        SEP (data_at sh (tarray tuchar 12) (bytes U) t)).
      * forward. match goal with |- context [temp HT5._t'1 (Vint ?v)] => Exists v end. entailer!.
      * forward. match goal with |- context [temp HT5._t'1 (Vint ?v)] => Exists v end. entailer!.
      * Intros v.
        forward.
        rewrite hci5_ts_zext, hci5_ts_upd.
        assert (HU: Zlength (upd_Znth i U (Byte.repr (Int.unsigned v))) = 12) by (rewrite upd_Znth_Zlength; lia).
        forward_if (EX c: int,
          PROP () LOCAL (temp HT5._t'2 (Vint c); temp HT5._i (Vint (Int.repr i)); temp HT5._t t;
                         temp HT5._up (Vint up))
          SEP (data_at sh (tarray tuchar 12) (bytes (upd_Znth i U (Byte.repr (Int.unsigned v)))) t)).
        -- forward.
           { go_lower. unfold bytes; rewrite Znth_map by lia. apply prop_right. simpl. apply tc_val_Vubyte. }
           unfold bytes at 1. rewrite Znth_map by lia.
           forward.
           match goal with |- context [temp HT5._t'2 (Vint ?c)] => Exists c end. entailer!.
        -- forward.
           match goal with |- context [temp HT5._t'2 (Vint ?c)] => Exists c end. entailer!.
        -- Intros c.
           forward_if.
           ++ forward. Exists (upd_Znth i U (Byte.repr (Int.unsigned v))). entailer!.
           ++ forward. Exists (i - 1) (upd_Znth i U (Byte.repr (Int.unsigned v))). entailer!.
    + forward. Exists U. entailer!.
  - Intros U. Exists U. rewrite hci5_ts_hbytes. match goal with Hz: Zlength U = 12 |- _ => rewrite Hz end. entailer!.
Qed.

(* a body proved in the empty context holds in any (it calls nothing, reads no global) *)
Lemma hci5_ts_body V G : semax_body V G HT5.f_ts_step hci5_ts_step_spec.
Proof.
  apply (semax_body_subsumption _ [] V [] G _ _ hci5_ts_body0).
  unfold func_tycontext, make_tycontext, tycontext_sub. simpl.
  repeat split; intros; try apply Maps.PTree.gempty; auto.
  - destruct (Maps.PTree.get id _); auto.
Qed.

End Body.
