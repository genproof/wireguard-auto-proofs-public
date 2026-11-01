(* law cookie_reply: the bodies of the harness's local functions m_expired and m_cookie. v1 template (the same C functions and specifications):
   proof/harness/cookie_reply/hcy4_local.v + hcy4_loc_lemmas.v; the Gprog is now hcy5_Gprog (common4 + protocol4:
   m_cookie calls quickproof_swab16, bytes_copy, m_mac). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_loc_lemmas.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Section Local.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_body_m_expired :
  semax_body hcy5_V (hcy5_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HY.f_m_expired
    hcy5_m_expired_spec.
Proof.
  start_function.
  forward.
  unfold birthdate_expired, s64_le, NSEC_PER_SEC.
  destruct (Int64.lt _ _); entailer!.
Qed.

Ltac hcy5_loc_args :=
  simpl;
  repeat match goal with H: Zlength (_ ?s) = ?n |- context [Zlength (_ ?s)] => rewrite H end;
  unfold hcy5_loc_fa4, hcy5_loc_fa16, hcy5_loc_fa2;
  rewrite ?field_address_offset by auto with field_compatible; simpl; normalize.

Lemma hcy5_body_m_cookie :
  semax_body hcy5_V (hcy5_Gprog x25519 aead_enc aead_dec xaead_enc xaead_dec) HY.f_m_cookie
    hcy5_m_cookie_spec.
Proof.
  start_function.
  assert_PROP (skb_ok s) as OK by (unfold skb_rep; entailer!).
  pose proof OK as (Hpr & H4 & H6 & H2).
  rewrite (hcy5_loc_skb_open shs sp s OK).
  rewrite hcy5_loc_buf0. Intros.
  assert_PROP (field_compatible (tarray tuchar 18) [] v_buf) as FCb by entailer!.
  assert_PROP (field_compatible t_skb [] sp) as FCs.
  { entailer!. match goal with H: field_compatible t_skb (DOT HY._protocol) sp |- _ =>
      destruct H as (?&?&?&?&?&?); repeat split; auto end. }
  forward.
  forward_call 2048.
  forward.
  { entailer!; lia. }
  set (A := if Z.eq_dec (sk_proto s) PROTO_IP then sk_ip4 s
            else if Z.eq_dec (sk_proto s) PROTO_IPV6 then sk_ip6 s else []).
  forward_if (PROP () LOCAL (temp HY._n (Vlong (Int64.repr (Zlength A))); lvar HY._buf (tarray tuchar 18) v_buf;
      gvars gv; temp HY._out o; temp HY._secret k; temp HY._skb sp)
    SEP (data_at Tsh (tarray tuchar 18) (hcy5_loc_bufv A) v_buf; hout sho 16 o; hbytes shk SECRET k;
      field_at shs t_skb (DOT HY._protocol) (Vint (Int.repr (sk_proto s))) sp;
      hbytes shs (sk_ip4 s) (hcy5_loc_fa4 sp); hbytes shs (sk_ip6 s) (hcy5_loc_fa16 sp);
      hbytes shs (sk_port s) (hcy5_loc_fa2 sp); hcy5_loc_skb_rest shs sp s; blake2s_globals gv)).
  - assert (Hp: sk_proto s = PROTO_IP).
    { apply (f_equal Int.unsigned) in H0. replace (swab16 2048) with 8 in H0 by reflexivity.
      rewrite !Int.unsigned_repr in H0 by rep_lia. exact H0. }
    assert (HA: A = sk_ip4 s) by (unfold A; rewrite Hp; reflexivity).
    sep_apply (hcy5_loc_buf_open0 (Zlength (sk_ip4 s)) v_buf); [lia | auto]. Intros.
    forward_call (Tsh, v_buf, shs, hcy5_loc_fa4 sp, sk_ip4 s).
    { entailer!. hcy5_loc_args. }
    forward.
    rewrite HA. sep_apply (hcy5_loc_buf_close0 (sk_ip4 s) v_buf); [lia | auto].
    entailer!. rewrite H4; reflexivity.
  - assert (Hp: sk_proto s <> PROTO_IP).
    { intro E. apply H0. rewrite E. reflexivity. }
    forward_call 34525.
    forward.
    forward_if (PROP () LOCAL (temp HY._n (Vlong (Int64.repr (Zlength A))); lvar HY._buf (tarray tuchar 18) v_buf;
      gvars gv; temp HY._out o; temp HY._secret k; temp HY._skb sp)
    SEP (data_at Tsh (tarray tuchar 18) (hcy5_loc_bufv A) v_buf; hout sho 16 o; hbytes shk SECRET k;
      field_at shs t_skb (DOT HY._protocol) (Vint (Int.repr (sk_proto s))) sp;
      hbytes shs (sk_ip4 s) (hcy5_loc_fa4 sp); hbytes shs (sk_ip6 s) (hcy5_loc_fa16 sp);
      hbytes shs (sk_port s) (hcy5_loc_fa2 sp); hcy5_loc_skb_rest shs sp s; blake2s_globals gv)).
    + assert (Hp6: sk_proto s = PROTO_IPV6).
      { apply (f_equal Int.unsigned) in H1. replace (swab16 34525) with 56710 in H1 by reflexivity.
        rewrite !Int.unsigned_repr in H1 by rep_lia. exact H1. }
      assert (HA: A = sk_ip6 s) by (unfold A; rewrite if_false by auto; rewrite Hp6; reflexivity).
      sep_apply (hcy5_loc_buf_open0 (Zlength (sk_ip6 s)) v_buf); [lia | auto]. Intros.
      forward_call (Tsh, v_buf, shs, hcy5_loc_fa16 sp, sk_ip6 s).
      { entailer!. hcy5_loc_args. }
      forward.
      rewrite HA. sep_apply (hcy5_loc_buf_close0 (sk_ip6 s) v_buf); [lia | auto].
      entailer!. rewrite H6; reflexivity.
    + assert (Hp6: sk_proto s <> PROTO_IPV6).
      { intro E. apply H1. rewrite E. reflexivity. }
      assert (HA: A = []) by (unfold A; rewrite !if_false by auto; reflexivity).
      forward. rewrite HA. entailer!.
  - assert (HAl: 0 <= Zlength A <= 16) by (unfold A; repeat destruct Z.eq_dec; rewrite ?Zlength_nil; lia).
    sep_apply (hcy5_loc_buf_open A (Zlength (sk_port s)) v_buf); [lia | lia | auto]. Intros.
    forward_call (Tsh, offset_val (Zlength A) v_buf, shs, hcy5_loc_fa2 sp, sk_port s).
    { entailer!. hcy5_loc_args. }
    sep_apply (hcy5_loc_buf_close A (sk_port s) v_buf); [lia | auto].
    sep_apply (hcy5_loc_buf_open (A ++ sk_port s) 0 v_buf); [rewrite Zlength_app; lia |]. Intros.
    rewrite <- (hcy5_loc_hin Tsh (A ++ sk_port s) v_buf) by (rewrite Zlength_app; lia).
    rewrite <- (hcy5_loc_hin shk SECRET k) by lia.
    forward_call (gv, sho, o, shk, k, SECRET, Tsh, v_buf, A ++ sk_port s).
    { entailer!. simpl. rewrite H, Zlength_app, H2. reflexivity. }
    { rewrite Zlength_app. rep_lia. }
    rewrite (hcy5_loc_hin Tsh (A ++ sk_port s) v_buf) by (rewrite Zlength_app; lia).
    rewrite (hcy5_loc_hin shk SECRET k) by lia.
    rewrite hcy5_loc_hout0, Z.add_0_r.
    pose proof (hcy5_loc_buf_close (A ++ sk_port s) [] v_buf) as Hc.
    rewrite Zlength_nil, Z.add_0_r in Hc.
    sep_apply Hc; [rewrite Zlength_app; lia |]. clear Hc.
    rewrite app_nil_r, (hcy5_loc_skb_open shs sp s OK).
    replace (MAC SECRET (A ++ sk_port s)) with (cookie_of SECRET s) by reflexivity.
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 18) (hcy5_loc_bufv (A ++ sk_port s)) v_buf).
    entailer!.
Qed.

End Local.
