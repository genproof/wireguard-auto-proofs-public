(* byte-buffer lemmas of main's segments (the packet's
   two parts back into one malloc'd block before free). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

(* splitting a byte array (as haead_ref_body3.v's har_split) *)
Lemma hka5e_split sh n n1 n2 (l1 l2: list val) p : Zlength l1 = n1 -> Zlength l2 = n2 -> n = n1 + n2 ->
  field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) (l1 ++ l2) p =
  (data_at sh (tarray tuchar n1) l1 p * data_at sh (tarray tuchar n2) l2 (offset_val n1 p))%logic.
Proof.
  intros H1 H2 Hn Hf. subst n1 n2 n.
  rewrite (split2_data_at_Tarray_app (Zlength l1) (Zlength l1 + Zlength l2) sh tuchar l1 l2);
    [| reflexivity | exact (ltac:(lia) : Zlength (A:=val) l2 = Zlength l1 + Zlength l2 - Zlength l1)].
  replace (Zlength l1 + Zlength l2 - Zlength l1) with (Zlength l2) by lia.
  rewrite field_address0_offset.
  2: { pose proof (Zlength_nonneg l1); pose proof (Zlength_nonneg l2). auto with field_compatible. }
  simpl nested_field_offset. f_equal. f_equal. f_equal. simpl. lia.
Qed.

(* a malloc'd byte block is field_compatible *)
Lemma hka5e_fc n p : 0 <= n -> malloc_compatible (sizeof (tarray tuchar n)) p -> field_compatible (tarray tuchar n) [] p.
Proof.
  intros Hn H. apply malloc_compatible_field_compatible; auto.
Qed.

(* the packet (header + encrypted_data) as the one block malloc gave *)
Lemma hka5e_pkt_join sh pkt (hdr: list val) (c: list byte) :
  Zlength hdr = 16 -> field_compatible (tarray tuchar (16 + Zlength c)) [] pkt ->
  (data_at sh (tarray tuchar 16) hdr pkt *
   data_at sh (tarray tuchar (Zlength c)) (map Vubyte c) (offset_val 16 pkt))%logic
  |-- data_at_ sh (tarray tuchar (16 + Zlength c)) pkt.
Proof.
  intros Hh Hf.
  rewrite <- (hka5e_split sh (16 + Zlength c) 16 (Zlength c) hdr (map Vubyte c) pkt);
    [| exact Hh | rewrite Zlength_map; reflexivity | reflexivity | exact Hf].
  apply data_at_data_at_.
Qed.
