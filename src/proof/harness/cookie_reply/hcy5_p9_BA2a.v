(* law cookie_reply, phase P9, segment BA2a.  reply->receiver_index = h->entry.index.
   Port of v1's *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---- helpers (prefix hcy5_p9_BA2a_) ---- *)
#[local] Instance hcy5_p9_BA2a_cceN : change_composite_env Noise.CS W_cookie_reply.
Proof. make_cs_preserve Noise.CS W_cookie_reply. Defined.
#[local] Instance hcy5_p9_BA2a_cceC : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.

(* the handshake entry of the pool belongs to a peer of PS *)
Lemma hcy5_p9_BA2a_inPS PS KE T a idx :
  hcy5_T_ok PS KE T -> t_entry T (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx) ->
  In a (map peer_addr4 PS).
Proof.
  intros ((own & ix & HD & _) & _) He. unfold t_entry in He.
  destruct (sfind (t_D T) (hs_addr a)) as [[sh E]|] eqn:Hs; [|discriminate]. inv He.
  apply prot_rep3_sfind_In in Hs. rewrite HD in Hs. unfold hcy5_pool in Hs.
  apply in_app_or in Hs. destruct Hs as [Hs|Hs].
  - apply in_map_iff in Hs. destruct Hs as (k & Hk & _). unfold hcy5_kentry in Hk. inv Hk.
  - apply in_map_iff in Hs. destruct Hs as (a' & Ha' & Hin). unfold hcy5_hent in Ha'. inv Ha'. exact Hin.
Qed.

(* the peer at a: its handshake is field-compatible *)
Lemma hcy5_p9_BA2a_fc PS a : In a (map peer_addr4 PS) ->
  peers_rep PS |-- !! @field_compatible Noise.CS t_hs [] (hs_addr a).
Proof.
  intros H.
  assert (H': In a (saddrs PS)).
  { replace (saddrs PS) with (map peer_addr4 PS); [exact H|].
    unfold saddrs; apply map_ext; intros [[? ?] ?]; reflexivity. }
  destruct (prot_rep3_sfind_in PS a H') as (sh & P & HP).
  unfold peers_rep. rewrite (prot_rep3_split _ _ _ _ _ HP). unfold peer_item_rep at 1, peer_rep. Intros.
  sep_apply (prot_rep3_hs_fc sh (hs_addr a) (p_hs P)). entailer!.
Qed.

(* an entry at the handshake's address, as the handshake's field entry at the world *)
Lemma hcy5_p9_BA2a_entry_W sh h E nx hd : @field_compatible Noise.CS t_hs [] h ->
  entry_at sh h E nx hd = @field_at W_cookie_reply sh t_hs (DOT HY._entry) (entry_val E nx hd) h.
Proof.
  intros FC.
  assert (FCW: @field_compatible W_cookie_reply t_hs [] h).
  { apply (@field_compatible_change_composite Noise.CS W_cookie_reply hcy5_p9_BA2a_cceN);
      [prove_cs_preserve_type | exact FC]. }
  rewrite (@field_at_data_at W_cookie_reply).
  rewrite (@field_address_offset W_cookie_reply)
    by (destruct FCW as (?&?&?&?&?); repeat split; auto; compute; tauto).
  change (@nested_field_type W_cookie_reply t_hs (DOT HY._entry)) with t_entry_s.
  change (@nested_field_offset W_cookie_reply t_hs (DOT HY._entry)) with 0.
  rewrite isptr_offset_val_zero by (destruct FC; auto).
  unfold entry_at.
  rewrite (@data_at_change_composite Noise.CS W_cookie_reply hcy5_p9_BA2a_cceN sh t_entry_s
    (entry_val E nx hd) (entry_val E nx hd) (JMeq_refl _) eq_refl). reflexivity.
Qed.

(* the table with the entry at h focused (as the handshake's field at the world) *)
Lemma hcy5_p9_BA2a_open sht tab T h sh E : sfind (t_D T) h = Some (sh, E) -> In h (t_L T) ->
  @field_compatible Noise.CS t_hs [] h ->
  itable sht tab T |--
  !! (itable_wf T /\ writable_share sh) &&
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) h) *
   @field_at W_cookie_reply sh t_hs (DOT HY._entry) (entry_val E (succ_in (t_L T) h) true) h).
Proof.
  intros Hs HL FC. unfold itable. Intros.
  assert (WS: writable_share sh).
  { destruct H as (_ & _ & _ & H4). apply prot_rep3_sfind_In in Hs. rewrite Forall_forall in H4.
    apply (H4 _ Hs). }
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (h, sh, E)) with (entry_at sh h E (succ_in (t_L T) h) (vin h (t_L T))).
  assert (Hv: vin h (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec h (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, (hcy5_p9_BA2a_entry_W _ _ _ _ _ FC). entailer!.
Qed.

Lemma hcy5_p9_BA2a_close sht tab T h sh E : sfind (t_D T) h = Some (sh, E) -> In h (t_L T) ->
  @field_compatible Noise.CS t_hs [] h -> itable_wf T ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) tab * iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) h) *
  @field_at W_cookie_reply sh t_hs (DOT HY._entry) (entry_val E (succ_in (t_L T) h) true) h
  |-- itable sht tab T.
Proof.
  intros Hs HL FC WF. unfold itable.
  rewrite (prot_rep3_split _ _ _ _ _ Hs).
  change (pool_item_rep (t_L T) (h, sh, E)) with (entry_at sh h E (succ_in (t_L T) h) (vin h (t_L T))).
  assert (Hv: vin h (t_L T) = true) by (unfold vin; destruct (in_dec eq_dec h (t_L T)); [reflexivity|contradiction]).
  rewrite Hv, (hcy5_p9_BA2a_entry_W _ _ _ _ _ FC). entailer!.
Qed.

(* the reply at the world *)
Lemma hcy5_p9_BA2a_cmsg_W sh p M :
  cmsg_rep sh p M = !! cm_ok M && @data_at W_cookie_reply sh t_cmsg (cmsg_val M) p.
Proof.
  unfold cmsg_rep. f_equal.
  rewrite (@data_at_change_composite Cookie.CS W_cookie_reply hcy5_p9_BA2a_cceC sh t_cmsg
    (cmsg_val M) (cmsg_val M) (JMeq_refl _) eq_refl). reflexivity.
Qed.

(* the reply after the store of the receiver index *)
Lemma hcy5_p9_BA2a_cmsg_close sh p M idx : cm_ok M ->
  @data_at W_cookie_reply sh t_cmsg (fst (cmsg_val M), (Vint idx, snd (snd (cmsg_val M)))) p
  |-- cmsg_rep sh p (hcy5_p9_rcv M idx).
Proof.
  intros OK. rewrite hcy5_p9_BA2a_cmsg_W. apply andp_right; [apply prop_right; exact OK | apply derives_refl].
Qed.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p9_BA2a_ok {Espec: OracleKind} gv L FR R S m c rp Q rr CK NS PS T np CL KE md a idx CM' :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_T_ok PS KE T -> t_entry T (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx) -> In (hs_addr a) (t_L T) ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE CM' md [] [temp HY._h (hs_addr a)])
    hcy5_p9_BA2a
    (normal_ret_assert
      (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS PS T np CL KE (hcy5_p9_rcv CM' idx) md []
         [temp HY._h (hs_addr a)])).
Proof.
  intros HH HT He HL. unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_BA2a.
  simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; simpl app.
  pose proof (hcy5_p9_BA2a_inPS _ _ _ _ _ HT He) as HIn.
  unfold t_entry in He. destruct (sfind (t_D T) (hs_addr a)) as [[sh E]|] eqn:Hs; [|discriminate]. inv He.
  assert_PROP (@field_compatible Noise.CS t_hs [] (hs_addr a)) as FC.
  { sep_apply (hcy5_p9_BA2a_fc PS a HIn). entailer!. }
  sep_apply (hcy5_p9_BA2a_open Tsh (l_ita L) T (hs_addr a) sh _ Hs HL FC). Intros.
  forward.
  match goal with |- context [temp HY._t'118 ?v] => replace v with (Vint idx) by reflexivity end.
  rewrite hcy5_p9_BA2a_cmsg_W. Intros.
  forward.
  sep_apply (hcy5_p9_BA2a_close Tsh (l_ita L) T (hs_addr a) sh _ Hs HL FC H).
  sep_apply (hcy5_p9_BA2a_cmsg_close Ews rp CM' idx H1).
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; simpl app.
  entailer!.
Qed.

End Seg.
