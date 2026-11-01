(* law handshake_receive: body proofs of local
   functions of the harness unit (hrx5_spec.v), at the unit's compspecs HRX.  The harness's helpers m_expired, m_cookie, draw_type, draw_macs.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_help_lemmas.
Local Open Scope logic.

#[local] Existing Instance HRX.

(* the world's compspecs binder CSw hidden from typeclass resolution (it would be picked over HRX) *)
Definition hrx5_help_hide : Type := compspecs.
Ltac hrx5_help_hide_cs := match goal with C: compspecs |- _ => change hrx5_help_hide in C end.

Lemma hrx5_body_m_expired x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_m_expired
    hrx5_m_expired_spec.
Proof.
  intros _ _ _.
  start_function. hrx5_help_hide_cs.
  forward.
  unfold birthdate_expired, s64_le, NSEC_PER_SEC.
  destruct (Int64.lt _ _); entailer!.
Qed.

Ltac hrx5_help_args :=
  simpl;
  repeat match goal with H: Zlength (_ ?s) = ?n |- context [Zlength (_ ?s)] => rewrite H end;
  unfold hrx5_help_fa4, hrx5_help_fa16, hrx5_help_fa2;
  rewrite ?field_address_offset by auto with field_compatible; simpl; normalize.

Lemma hrx5_body_m_cookie x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_m_cookie
    hrx5_m_cookie_spec.
Proof.
  intros _ _ _.
  start_function. hrx5_help_hide_cs.
  assert_PROP (skb_ok s) as OK by (unfold skb_src_rep; entailer!).
  pose proof OK as (Hpr & H4 & H6 & H2).
  rewrite (hrx5_help_skb_open2 shs sp dv lv s OK).
  rewrite hrx5_help_buf0. Intros.
  assert_PROP (field_compatible (tarray tuchar 18) [] v_buf) as FCb by entailer!.
  assert_PROP (field_compatible t_skb [] sp) as FCs.
  { entailer!. match goal with H: field_compatible t_skb (DOT HRC._protocol) sp |- _ =>
      destruct H as (?&?&?&?&?&?); repeat split; auto end. }
  forward.
  forward_call 2048.
  forward.
  { entailer!; lia. }
  set (A := if Z.eq_dec (sk_proto s) PROTO_IP then sk_ip4 s
            else if Z.eq_dec (sk_proto s) PROTO_IPV6 then sk_ip6 s else []).
  forward_if (PROP () LOCAL (temp HRC._n (Vlong (Int64.repr (Zlength A))); lvar HRC._buf (tarray tuchar 18) v_buf;
      gvars gv; temp HRC._out o; temp HRC._secret k; temp HRC._skb sp)
    SEP (data_at Tsh (tarray tuchar 18) (hrx5_help_bufv A) v_buf; hout sho 16 o; hbytes shk SECRET k;
      field_at shs t_skb (DOT HRC._protocol) (Vint (Int.repr (sk_proto s))) sp;
      hbytes shs (sk_ip4 s) (hrx5_help_fa4 sp); hbytes shs (sk_ip6 s) (hrx5_help_fa16 sp);
      hbytes shs (sk_port s) (hrx5_help_fa2 sp); hrx5_help_skb_rest2 shs sp dv lv; blake2s_globals gv)).
  - assert (Hp: sk_proto s = PROTO_IP).
    { apply (f_equal Int.unsigned) in H0. replace (swab16 2048) with 8 in H0 by reflexivity.
      rewrite !Int.unsigned_repr in H0 by rep_lia. exact H0. }
    assert (HA: A = sk_ip4 s) by (unfold A; rewrite Hp; reflexivity).
    sep_apply (hrx5_help_buf_open0 (Zlength (sk_ip4 s)) v_buf); [lia | auto]. Intros.
    forward_call (Tsh, v_buf, shs, hrx5_help_fa4 sp, sk_ip4 s).
    { entailer!. hrx5_help_args. }
    forward.
    rewrite HA. sep_apply (hrx5_help_buf_close0 (sk_ip4 s) v_buf); [lia | auto].
    entailer!. rewrite H4; reflexivity.
  - assert (Hp: sk_proto s <> PROTO_IP).
    { intro E. apply H0. rewrite E. reflexivity. }
    forward_call 34525.
    forward.
    forward_if (PROP () LOCAL (temp HRC._n (Vlong (Int64.repr (Zlength A))); lvar HRC._buf (tarray tuchar 18) v_buf;
      gvars gv; temp HRC._out o; temp HRC._secret k; temp HRC._skb sp)
    SEP (data_at Tsh (tarray tuchar 18) (hrx5_help_bufv A) v_buf; hout sho 16 o; hbytes shk SECRET k;
      field_at shs t_skb (DOT HRC._protocol) (Vint (Int.repr (sk_proto s))) sp;
      hbytes shs (sk_ip4 s) (hrx5_help_fa4 sp); hbytes shs (sk_ip6 s) (hrx5_help_fa16 sp);
      hbytes shs (sk_port s) (hrx5_help_fa2 sp); hrx5_help_skb_rest2 shs sp dv lv; blake2s_globals gv)).
    + assert (Hp6: sk_proto s = PROTO_IPV6).
      { apply (f_equal Int.unsigned) in H1. replace (swab16 34525) with 56710 in H1 by reflexivity.
        rewrite !Int.unsigned_repr in H1 by rep_lia. exact H1. }
      assert (HA: A = sk_ip6 s) by (unfold A; rewrite if_false by auto; rewrite Hp6; reflexivity).
      sep_apply (hrx5_help_buf_open0 (Zlength (sk_ip6 s)) v_buf); [lia | auto]. Intros.
      forward_call (Tsh, v_buf, shs, hrx5_help_fa16 sp, sk_ip6 s).
      { entailer!. hrx5_help_args. }
      forward.
      rewrite HA. sep_apply (hrx5_help_buf_close0 (sk_ip6 s) v_buf); [lia | auto].
      entailer!. rewrite H6; reflexivity.
    + assert (Hp6: sk_proto s <> PROTO_IPV6).
      { intro E. apply H1. rewrite E. reflexivity. }
      assert (HA: A = []) by (unfold A; rewrite !if_false by auto; reflexivity).
      forward. rewrite HA. entailer!.
  - assert (HAl: 0 <= Zlength A <= 16) by (unfold A; repeat destruct Z.eq_dec; rewrite ?Zlength_nil; lia).
    sep_apply (hrx5_help_buf_open A (Zlength (sk_port s)) v_buf); [lia | lia | auto]. Intros.
    forward_call (Tsh, offset_val (Zlength A) v_buf, shs, hrx5_help_fa2 sp, sk_port s).
    { entailer!. hrx5_help_args. }
    sep_apply (hrx5_help_buf_close A (sk_port s) v_buf); [lia | auto].
    sep_apply (hrx5_help_buf_open (A ++ sk_port s) 0 v_buf); [rewrite Zlength_app; lia |]. Intros.
    rewrite <- (hrx5_help_hin Tsh (A ++ sk_port s) v_buf) by (rewrite Zlength_app; lia).
    rewrite <- (hrx5_help_hin shk SECRET k) by lia.
    forward_call (gv, sho, o, shk, k, SECRET, Tsh, v_buf, A ++ sk_port s).
    { entailer!. simpl. rewrite H, Zlength_app, H2. reflexivity. }
    { rewrite Zlength_app. rep_lia. }
    rewrite (hrx5_help_hin Tsh (A ++ sk_port s) v_buf) by (rewrite Zlength_app; lia).
    rewrite (hrx5_help_hin shk SECRET k) by lia.
    rewrite hrx5_help_hout0, Z.add_0_r.
    pose proof (hrx5_help_buf_close (A ++ sk_port s) [] v_buf) as Hc.
    rewrite Zlength_nil, Z.add_0_r in Hc.
    sep_apply Hc; [rewrite Zlength_app; lia |]. clear Hc.
    rewrite app_nil_r, (hrx5_help_skb_open2 shs sp dv lv s OK).
    replace (MAC SECRET (A ++ sk_port s)) with (cookie_of SECRET s) by reflexivity.
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 18) (hrx5_help_bufv (A ++ sk_port s)) v_buf).
    entailer!.
Qed.

Lemma hrx5_help_mods b m : 0 <= b <= Int.max_signed -> 0 < m <= Int.max_signed ->
  Int.mods (Int.repr b) (Int.repr m) = Int.repr (b mod m).
Proof.
  intros Hb Hm. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Ltac hrx5_help_mone :=
  match goal with H: _ /\ Int.repr _ = Int.mone |- _ =>
    destruct H as [_ H]; apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end.

Lemma hrx5_body_draw_type x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_draw_type
    hrx5_draw_type_spec.
Proof.
  intros _ _ _.
  start_function. hrx5_help_hide_cs.
  forward_call. Intros b.
  apply semax_seq with (PROP () LOCAL (temp HRC._t (Vint t)) SEP ()).
  { eapply (semax_switch_PQR (b mod 4)); [reflexivity | entailer! | entailer! | ].
    { hrx5_help_mone. }
    { f_equal. apply hrx5_help_mods; rep_lia. }
    pose proof (Z.mod_pos_bound b 4 ltac:(lia)).
    unfold select_switch at 1; unfold select_switch_default at 1.
    process_cases Signed.
    - forward_call. Intros c. forward_call. Intros d.
      pose proof (Z.mod_pos_bound c 255 ltac:(lia)). pose proof (Z.mod_pos_bound d 3 ltac:(lia)).
      forward.
      { entailer!. rewrite !hrx5_help_mods by rep_lia. rewrite !add_repr, mul_repr, !Int.signed_repr by rep_lia.
        rewrite Int.unsigned_repr by rep_lia. change (Int.unsigned Int.iwordsize) with 32.
        repeat split; try rep_lia; intros [_ Hm]; apply (f_equal Int.unsigned) in Hm; vm_compute in Hm; discriminate. }
      match goal with |- context [Vint ?X = Vint _] => Exists X end. entailer!.
    - forward_call. Intros n. forward. Exists (Int.repr n). entailer!.
    - forward. entailer!. }
  abbreviate_semax. forward. Exists t. entailer!.
Qed.

Lemma hrx5_help_MAC_len key m : Zlength (MAC key m) = 16.
Proof. unfold MAC, WgNoise.proof.blake2s.model.blake2s, WgNoise.proof.blake2s.model.b2s_digest_stream, WgNoise.proof.blake2s.model.b2s_out. rewrite Zlength_map. reflexivity. Qed.

Lemma hrx5_help_cookie_len K s : Zlength (cookie_of K s) = 16.
Proof. apply hrx5_help_MAC_len. Qed.

(* the arguments of a call on img + len - m *)
Ltac hrx5_help_ptr_args i :=
  entailer!;
  let b := fresh "b" in let o := fresh "o" in
  destruct i as [| | | | | b o]; try contradiction;
  rewrite ?hrx5_help_MAC_len; simpl; f_equal; f_equal;
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one; unfold Ptrofs.of_ints; rewrite Int.signed_repr by rep_lia;
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc; f_equal;
  rewrite Ptrofs.neg_repr, ptrofs_add_repr; f_equal; lia.

(* the end of draw_macs: the image P ++ M1' ++ M2' *)
Ltac hrx5_help_close shi P M1' i n HP H3 FCn M2x HM2x :=
  let Hs := fresh "Hs" in
  pose proof (hrx5_help_split2 shi (P ++ M1') M2x i) as Hs;
  rewrite Zlength_app, HP, H3, HM2x in Hs; replace (n - 32 + 16) with (n - 16) in Hs by lia;
  sep_apply (derives_refl' _ _ (eq_sym (Hs FCn))); clear Hs;
  Exists ((P ++ M1') ++ M2x);
  rewrite <- !hrx5_help_lout;
  entailer!;
  rewrite !Zlength_app, HP, H3, HM2x; split; [lia |];
  rewrite <- app_assoc, sublist_app1 by lia; rewrite sublist_same by lia; reflexivity.

Lemma hrx5_body_draw_macs x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_draw_macs
    hrx5_draw_macs_spec.
Proof.
  intros _ _ _.
  start_function. hrx5_help_hide_cs.
  set (n := Zlength IMG) in *.
  assert_PROP (@field_compatible HCS (tarray tuchar n) [] i) as FCi by (unfold hbytes; entailer!).
  set (P := sublist 0 (n - 32) IMG). set (M1 := sublist (n - 32) (n - 16) IMG).
  set (M2 := sublist (n - 16) n IMG).
  assert (HP: Zlength P = n - 32) by (unfold P; rewrite Zlength_sublist; lia).
  assert (HM1: Zlength M1 = 16) by (unfold M1; rewrite Zlength_sublist; lia).
  assert (HM2: Zlength M2 = 16) by (unfold M2; rewrite Zlength_sublist; lia).
  assert (HI: IMG = P ++ M1 ++ M2) by (unfold P, M1, M2; list_solve).
  assert (FC1: @field_compatible HCS (tarray tuchar (Zlength P + Zlength M1)) [] i).
  { apply field_compatible_array_smaller0 with n; auto. lia. }
  rewrite HI, app_assoc, (hrx5_help_split2 shi (P ++ M1) M2 i)
    by (rewrite !Zlength_app, HP, HM1, HM2; replace (n - 32 + 16 + 16) with n by lia; exact FCi).
  rewrite (hrx5_help_split2 shi P M1 i) by exact FC1.
  rewrite Zlength_app, HP, HM1.
  rewrite !hrx5_help_lout.
  assert (FCa: @field_compatible HCS (tarray tuchar (n - 32 + 16)) [] i) by (rewrite <- HP, <- HM1; exact FC1).
  assert (Pi: isptr i) by (destruct FCi; auto).
  clear FC1.
  forward_call. Intros b1.
  forward_if (EX M1': list byte,
    PROP (Zlength M1' = 16)
    LOCAL (lvar HRC._mac (tarray tuchar 16) v_mac; lvar HRC._c (tarray tuchar 16) v_c; gvars gv; temp HRC._img i;
      temp HRC._len (Vlong (Int64.repr n)); temp HRC._mk1 k; temp HRC._secret c; temp HRC._skb sp)
    SEP (hout Tsh 16 v_mac; hout Tsh 16 v_c; hbytes shi (P ++ M1') i;
      hbytes shi M2 (offset_val (n - 32 + 16) i); hbytes shk MK1 k;
      hbytes shc SEC c; skb_src_rep shs sp dv lv s; blake2s_globals gv)).
  - entailer!. hrx5_help_mone.
  - rewrite (hrx5_help_hin_split shi P i), <- (hrx5_help_hin shk MK1 k) by lia.
    Intros.
    forward_call (gv, Tsh, v_mac, shk, k, MK1, shi, i, P).
    { entailer!. simpl. rewrite HP, H0. reflexivity. }
    rewrite (hrx5_help_hin shk MK1 k) by lia.
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_help_hin_split shi P i))).
    sep_apply (hrx5_help_hbytes_out shi M1 (offset_val (n - 32) i)). rewrite HM1.
    forward_call (shi, offset_val (n - 32) i, Tsh, v_mac, MAC MK1 P).
    { hrx5_help_ptr_args i. }
    { rewrite hrx5_help_MAC_len. rep_lia. }
    pose proof (hrx5_help_split2 shi P (MAC MK1 P) i) as Hs.
    rewrite hrx5_help_MAC_len, HP in Hs.
    sep_apply (derives_refl' _ _ (eq_sym (Hs FCa))). clear Hs.
    sep_apply (hrx5_help_hbytes_out Tsh (MAC MK1 P) v_mac). rewrite hrx5_help_MAC_len.
    Exists (MAC MK1 P). entailer!.
  - forward.
    pose proof (hrx5_help_split2 shi P M1 i) as Hs.
    rewrite HM1, HP in Hs.
    sep_apply (derives_refl' _ _ (eq_sym (Hs FCa))). clear Hs.
    Exists M1. entailer!.
  - Intros M1'.
    replace (n - 32 + 16) with (n - 16) by lia.
    forward_call. Intros b2.
    eapply (semax_switch_PQR (b2 mod 3)); [reflexivity | entailer! | entailer! | ].
    { hrx5_help_mone. }
    { f_equal. apply hrx5_help_mods; rep_lia. }
    pose proof (Z.mod_pos_bound b2 3 ltac:(lia)).
    unfold select_switch at 1; unfold select_switch_default at 1.
    assert (FCn: @field_compatible HCS (tarray tuchar (n - 16 + 16)) [] i)
      by (replace (n - 16 + 16) with n by lia; exact FCi).
    process_cases Signed.
    + forward_call (gv, Tsh, v_c, shc, c, SEC, shs, sp, s, dv, lv).
      rewrite <- (hrx5_help_hin Tsh (cookie_of SEC s) v_c) by (rewrite hrx5_help_cookie_len; lia).
      rewrite <- (hrx5_help_hin shi (P ++ M1') i) by (rewrite Zlength_app; lia).
      forward_call (gv, Tsh, v_mac, Tsh, v_c, cookie_of SEC s, shi, i, P ++ M1').
      { entailer!. simpl. rewrite Zlength_app, HP, H3, hrx5_help_cookie_len.
        replace (n - 32 + 16) with (n - 16) by lia. reflexivity. }
      { rewrite Zlength_app, hrx5_help_cookie_len. rep_lia. }
      rewrite (hrx5_help_hin Tsh (cookie_of SEC s) v_c) by (rewrite hrx5_help_cookie_len; lia).
      rewrite (hrx5_help_hin shi (P ++ M1') i) by (rewrite Zlength_app; lia).
      sep_apply (hrx5_help_hbytes_out shi M2 (offset_val (n - 16) i)). rewrite HM2.
      forward_call (shi, offset_val (n - 16) i, Tsh, v_mac, MAC (cookie_of SEC s) (P ++ M1')).
      { hrx5_help_ptr_args i. }
      { rewrite hrx5_help_MAC_len. rep_lia. }
      forward.
      sep_apply (hrx5_help_hbytes_out Tsh (cookie_of SEC s) v_c).
      sep_apply (hrx5_help_hbytes_out Tsh (MAC (cookie_of SEC s) (P ++ M1')) v_mac).
      rewrite hrx5_help_cookie_len, hrx5_help_MAC_len.
      hrx5_help_close shi P M1' i n HP H3 FCn (MAC (cookie_of SEC s) (P ++ M1')) (hrx5_help_MAC_len (cookie_of SEC s) (P ++ M1')).
    + sep_apply (hrx5_help_hbytes_out shi M2 (offset_val (n - 16) i)). rewrite HM2.
      forward_call (shi, offset_val (n - 16) i, Byte.zero, 16).
      { hrx5_help_ptr_args i. }
      forward.
      assert (HZ: Zlength (Zrepeat Byte.zero 16) = 16) by reflexivity.
      hrx5_help_close shi P M1' i n HP H3 FCn (Zrepeat Byte.zero 16) HZ.
    + forward.
      hrx5_help_close shi P M1' i n HP H3 FCn M2 HM2.
Qed.

(* the conjunction of this file's body lemmas *)
Definition hrx5_bodies_help : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_m_expired hrx5_m_expired_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_m_cookie hrx5_m_cookie_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_draw_type hrx5_draw_type_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_draw_macs hrx5_draw_macs_spec).

Theorem hrx5_grp_help : hrx5_bodies_help.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3.
  exact (conj (hrx5_body_m_expired _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_m_cookie _ _ _ _ _ _ H1 H2 H3)
    (conj (hrx5_body_draw_type _ _ _ _ _ _ H1 H2 H3)
    (hrx5_body_draw_macs _ _ _ _ _ _ H1 H2 H3)))).
Qed.
