(* law handshake, phase P5, segment B.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p5_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Local Open Scope logic.

Lemma hhs3_p5_B_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible, size_compatible, align_compatible. destruct p; simpl; try tauto.
  assert (A: forall ce, align_compatible_rec ce (tarray tuchar n) (Ptrofs.unsigned i)).
  { intros ce. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  pose proof (A (@cenv_cs cs1)). pose proof (A (@cenv_cs cs2)). tauto.
Qed.

#[local] Instance hhs3_p5_B_CCE : change_composite_env Noise.CS W_handshake.
Proof. make_cs_preserve Noise.CS W_handshake. Defined.

#[local] Instance hhs3_p5_B_CCEH : change_composite_env HCS W_handshake.
Proof. make_cs_preserve HCS W_handshake. Defined.

(* the response message at the world (for the load of the receiver index) *)
Lemma hhs3_p5_B_resp_W sh m M : rm_ok M -> resp_rep sh m M =
  @data_at W_handshake sh t_resp
     (Vint (rm_type M), (Vint (rm_sender M), (Vint (rm_receiver M), (bytes (rm_eph M), (bytes (rm_encn M),
      (bytes (rm_mac1 M), bytes (rm_mac2 M))))))) m.
Proof.
  intros Hok. unfold resp_rep, resp_val. rewrite prop_true_andp by exact Hok.
  apply equal_f, (@data_at_change_composite Noise.CS W_handshake _ sh t_resp); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

(* the response message: its ephemeral and enc_nothing as buffers, the rest *)
Section NoiseFields.
#[local] Existing Instance Noise.CS.

Definition hhs3_p5_B_rrest (sh: share) (m: val) (M: resp_msg) : mpred :=
  field_at sh t_resp (DOT I._header) (Vint (rm_type M)) m *
  field_at sh t_resp (DOT I._sender_index) (Vint (rm_sender M)) m *
  field_at sh t_resp (DOT I._receiver_index) (Vint (rm_receiver M)) m *
  field_at sh t_resp (DOT I._macs) (bytes (rm_mac1 M), bytes (rm_mac2 M)) m.

Lemma hhs3_p5_B_resp_open sh m M :
  rm_ok M -> field_compatible t_resp [] m ->
  resp_rep sh m M =
  hbytes sh (rm_eph M) (offset_val 12 m) * hbytes sh (rm_encn M) (offset_val 44 m) * hhs3_p5_B_rrest sh m M.
Proof.
  intros Hok FC. unfold resp_rep, hhs3_p5_B_rrest, resp_val. rewrite prop_true_andp by exact Hok.
  pose proof Hok as (L1 & L2 & L3 & L4).
  unfold hbytes. rewrite L1, L2. rewrite !(@hhs3_p5_B_tuchar_cs HCS Noise.CS).
  unfold_data_at (data_at _ t_resp _ m).
  rewrite (field_at_data_at sh t_resp (DOT I._unencrypted_ephemeral)),
    (field_at_data_at sh t_resp (DOT I._encrypted_nothing)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.
End NoiseFields.

(* the table after create_initiation *)
Lemma hhs3_p5_B_TA1 L I : hhs3_TA1 L I =
  mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I))] [hs_addr (l_pb L)].
Proof.
  unfold hhs3_TA1, t_insert, t_set_index, t_entry, t_upd, hhs3_TA0, hhs3_EB; cbn [t_D t_L sfind supd vremove].
  rewrite !if_true by auto. reflexivity.
Qed.

(* the table opened at its only entry: the entry as a field of the peer, at the world *)
Lemma hhs3_p5_B_open tab pb E : @field_compatible Noise.CS t_peer [] pb ->
  itable Tsh tab (mkT [(hs_addr pb, Tsh, E)] [hs_addr pb]) =
  @data_at Noise.CS Tsh t_itab (hs_addr pb) tab *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (e_peer E, (nullval, (Vtrue, (Vint (e_type E), Vint (e_index E))))) pb.
Proof.
  intros FC0. assert (FC: @field_compatible W_handshake t_peer [] pb).
  { apply (@field_compatible_change_composite Noise.CS W_handshake _); [prove_cs_preserve_type | exact FC0]. }
  unfold itable, pool_item_rep, entry_at, entry_val, vin. cbn [t_L t_D hd VST.msl.iter_sepcon.iter_sepcon succ_in].
  rewrite if_true by auto. destruct (in_dec eq_dec (hs_addr pb) [hs_addr pb]) as [_|N]; [|exfalso; apply N; left; auto].
  rewrite field_at_data_at. rewrite field_address_offset by auto with field_compatible.
  erewrite <- (@data_at_change_composite Noise.CS W_handshake _ Tsh t_entry_s); [| apply JMeq_refl | prove_cs_preserve_type].
  rewrite prop_true_andp.
  2:{ unfold itable_wf; cbn [t_L t_D saddrs map]. split; [constructor; [intros []|constructor]|].
      split; [intros x Hx; exact Hx|]. split; [constructor; [intros []|constructor]|].
      constructor; [apply writable_share_top | constructor]. }
  rewrite sepcon_emp. reflexivity.
Qed.

Lemma hhs3_p5_B_open1 L I : @field_compatible Noise.CS t_peer [] (l_pb L) ->
  itable Tsh (l_ita L) (hhs3_TA1 L I) =
  @data_at Noise.CS Tsh t_itab (hs_addr (l_pb L)) (l_ita L) *
  @field_at W_handshake Tsh t_peer (DOT HC._handshake DOT HC._entry)
    (l_pb L, (nullval, (Vtrue, (Vint IDX_HANDSHAKE, Vint (i_idx I))))) (l_pb L).
Proof. intros FC. rewrite hhs3_p5_B_TA1. apply (hhs3_p5_B_open _ _ (mkEntry (l_pb L) IDX_HANDSHAKE (i_idx I)) FC). Qed.

Lemma hhs3_p5_B_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_handshake sh t_mident (mident_val I) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_handshake hhs3_p5_B_CCEH sh t_mident (mident_val I)
    (mident_val I) (@JMeq_refl _ (mident_val I)) ltac:(vm_compute; reflexivity))).
Qed.

(* the identity: its private key as a buffer *)
Lemma hhs3_p5_B_mident_open sh I p :
  @field_compatible HCS t_mident [] p -> Zlength (mi_priv I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  hbytes sh (mi_priv I) (offset_val 0 p) *
  (@field_at HCS sh t_mident (DOT HC._pub) (bytes (mi_pub I)) p *
   @field_at HCS sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p).
Proof.
  intros FC L1. unfold mident_val, hbytes. rewrite L1.
  unfold_data_at (@data_at HCS sh t_mident _ p).
  rewrite (@field_at_data_at HCS sh t_mident (DOT HC._priv)).
  rewrite field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.

(* the initiation model: its ephemeral private key as a buffer, its state *)
Lemma hhs3_p5_B_minit_open sh E encs enct ep ck h p :
  @field_compatible HCS t_minit [] p -> Zlength ep = 32 ->
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  hbytes sh ep (offset_val 108 p) * @data_at HCS sh t_mstate (mstate_val ck h) (offset_val 140 p) *
  (@field_at HCS sh t_minit (DOT HC._ephemeral) (bytes E) p *
   @field_at HCS sh t_minit (DOT HC._enc_static) (bytes encs) p *
   @field_at HCS sh t_minit (DOT HC._enc_timestamp) (bytes enct) p).
Proof.
  intros FC L1. unfold minit_val, mstate_val, hbytes. rewrite L1.
  unfold_data_at (@data_at HCS sh t_minit _ p).
  rewrite (@field_at_data_at HCS sh t_minit (DOT HC._eph_priv)), (@field_at_data_at HCS sh t_minit (DOT HC._st)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  apply pred_ext; cancel.
Qed.

Lemma hhs3_p5_B_minit_len sh E encs enct ep ck h p :
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p |--
  !! (Zlength ep = 32 /\ Zlength ck = 32 /\ Zlength h = 32).
Proof.
  unfold minit_val, mstate_val. unfold_data_at (@data_at HCS sh t_minit _ p).
  rewrite (@field_at_data_at HCS sh t_minit (DOT HC._st)). simpl nested_field_type.
  unfold_data_at (@data_at HCS sh (Tstruct _ _) _ _). entailer!. unfold bytes in *.
  repeat match goal with Hv: value_fits (tarray tuchar _) _ |- _ =>
    rewrite value_fits_eq in Hv; cbn -[Zlength] in Hv; destruct Hv as [? _] end.
  rewrite !Zlength_map in *. lia.
Qed.

Lemma hhs3_p5_B_tsplit bs p : hbytes Tsh bs p = hbytes Ews bs p * hbytes (Share.comp Ews) bs p.
Proof. unfold hbytes. symmetry. apply data_at_share_join. apply join_comp_Tsh. Qed.

Lemma hhs3_p5_B_clamp_len r : Zlength r = 32 -> Zlength (clamp r) = 32.
Proof. intros. unfold clamp. list_solve. Qed.

Local Open Scope Z_scope.

Section P5B.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Ltac hhs3_p5_B_absurd :=
  first [ discriminate
        | exfalso; match goal with Hx: _ <> _ |- _ => apply Hx; reflexivity end
        | exfalso; match goal with Hx: Int.repr ?a = Int.zero |- _ =>
            apply (f_equal Int.unsigned) in Hx; rewrite Int.unsigned_repr in Hx by rep_lia; discriminate end
        | exfalso; match goal with Hx: @eq int _ _ |- _ =>
            apply (f_equal Int.unsigned) in Hx; vm_compute in Hx; discriminate end ].

Ltac hhs3_p5_B_fchain := repeat (apply semax_if_seq; forward_if; [hhs3_p5_B_absurd | forward]).

Ltac hhs3_p5_B_close R S m1 m2 a0 f0 l0 I M1 H1 MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa Cre acc ST2 :=
  unfold hhs3_p5_SB, hhs3_p5_SBC;
  Exists R S m1 m2 a0 f0 l0 I M1 H1; Exists MI nowb PA1 CI1 CI2 Q M2 H2 MR nowa; Exists Cre acc ST2;
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps, hhs3_p5_st2, hhs3_consts, wg_consts;
  cbn [app]; cbv beta iota.

Lemma hhs3_p5_B_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p5_SA x25519 aead_enc aead_dec gv L FR) hhs3_p5_B
    (overridePost (hhs3_p5_SB x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p5_SA, hhs3_Delta, hhs3_R, hhs3_p5_B. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb PA1 CI1 CI2. Intros Q M2 H2 MR nowa Cre.
  unfold hhs3_p5_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  rewrite (hhs3_p5_B_mident_W Tsh (hhs3_IA x25519 R) (l_ia L)).
  forward.
  rewrite <- (hhs3_p5_B_mident_W Tsh (hhs3_IA x25519 R) (l_ia L)).
  pose proof HH as (Hx & Ha & _ & _ & _).
  destruct MI as [[[[[Ei encs] enct] ep] ck] h]. cbv beta iota.
  unfold mident_val at 1. cbv beta iota.
  destruct (mi_ok (hhs3_IA x25519 R)) eqn:EA.
  2: { apply semax_if_seq. forward_if. { hhs3_p5_B_absurd. } forward.
       hhs3_p5_B_fchain. forward.
       assert (Eacc: hhs3_p5_acc x25519 aead_dec R I (Ei, encs, enct, ep, ck, h) M2 = false)
         by (unfold hhs3_p5_acc; rewrite EA; reflexivity).
       hhs3_p5_B_close R S m1 m2 a0 f0 l0 I M1 H1 (Ei, encs, enct, ep, ck, h) nowb PA1 CI1 CI2 Q M2 H2 MR nowa Cre
         false (@nil byte, @nil byte).
       entailer!. }
  (* A has an identity: the receiver index against pb's entry index *)
  apply semax_if_seq. forward_if. 2: { hhs3_p5_B_absurd. }
  assert_PROP (rm_ok (hhs3_M2m x25519 R M2)) as Hrok by (unfold resp_rep; entailer!).
  rewrite (hhs3_p5_B_resp_W Ews m2 _ Hrok).
  forward.
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_pb L)) as FCpb by (unfold peer_rep; entailer!).
  rewrite (hhs3_p5_B_open1 L I FCpb). Intros.
  forward.
  forward.
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_open1 L I FCpb))).
  rewrite <- (hhs3_p5_B_resp_W Ews m2 _ Hrok).
  change (rm_receiver (hhs3_M2m x25519 R M2)) with (rm_receiver M2).
  destruct (Int.eq (rm_receiver M2) (i_idx I)) eqn:EI.
  2: { hhs3_p5_B_fchain. forward.
       assert (Eacc: hhs3_p5_acc x25519 aead_dec R I (Ei, encs, enct, ep, ck, h) M2 = false)
         by (unfold hhs3_p5_acc; rewrite EA, EI; reflexivity).
       hhs3_p5_B_close R S m1 m2 a0 f0 l0 I M1 H1 (Ei, encs, enct, ep, ck, h) nowb PA1 CI1 CI2 Q M2 H2 MR nowa Cre
         false (@nil byte, @nil byte).
       entailer!. }
  (* the harness model *)
  apply semax_if_seq. forward_if. 2: { hhs3_p5_B_absurd. }
  assert_PROP (@field_compatible Noise.CS t_resp [] m2) as FCm2.
  { unfold resp_rep. rewrite prop_true_andp by exact Hrok. entailer!. }
  rewrite (hhs3_p5_B_resp_open Ews m2 _ Hrok FCm2).
  pose proof Hrok as (Lre & Lrn & _ & _).
  assert (LprivA: Zlength (mi_priv (hhs3_IA x25519 R)) = 32).
  { unfold hhs3_IA, mident_of. cbn [mi_priv]. apply hhs3_p5_B_clamp_len. apply H. }
  assert (Lpsk: Zlength (r_psk R) = 32) by apply H.
  assert_PROP (@field_compatible HCS t_mident [] (l_ia L)) as FCia by entailer!.
  rewrite (hhs3_p5_B_mident_open Tsh (hhs3_IA x25519 R) (l_ia L) FCia LprivA).
  assert_PROP (Zlength ep = 32 /\ Zlength ck = 32 /\ Zlength h = 32) as Lmi.
  { sep_apply (hhs3_p5_B_minit_len Tsh Ei encs enct ep ck h (l_mi L)). entailer!. }
  destruct Lmi as (Lep & Lck & Lh).
  assert_PROP (@field_compatible HCS t_minit [] (l_mi L)) as FCmi by entailer!.
  rewrite (hhs3_p5_B_minit_open Tsh Ei encs enct ep ck h (l_mi L) FCmi Lep).
  rewrite (hhs3_p5_B_tsplit ep), (hhs3_p5_B_tsplit (mi_priv (hhs3_IA x25519 R))), (hhs3_p5_B_tsplit (r_psk R)).
  unfold hhs3_consts, wg_consts. Intros.
  apply -> seq_assoc. eapply semax_seq'.
  forward_call (gv, Tsh, l_st2 L, Tsh, offset_val 140 (l_mi L), ck, h, Ews, offset_val 108 (l_mi L), ep,
                offset_val 0 (l_ia L), mi_priv (hhs3_IA x25519 R), l_psk L, r_psk R,
                offset_val 12 m2, rm_eph (hhs3_M2m x25519 R M2), offset_val 44 m2, rm_encn (hhs3_M2m x25519 R M2)).
  1: { assert (isptr m2) by (destruct FCm2; auto). tauto. }
  change (m_consume_response_model x25519 aead_dec ck h ep (mi_priv (hhs3_IA x25519 R)) (r_psk R)
            (rm_eph (hhs3_M2m x25519 R M2)) (rm_encn (hhs3_M2m x25519 R M2)))
    with (hhs3_mcr x25519 aead_dec R (Ei, encs, enct, ep, ck, h) M2).
  apply ENTAIL_refl.
  unfold MORE_COMMANDS, abbreviate. forward.
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_tsplit ep (offset_val 108 (l_mi L))))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_tsplit (mi_priv (hhs3_IA x25519 R)) (offset_val 0 (l_ia L))))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_tsplit (r_psk R) (l_psk L)))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_minit_open Tsh Ei encs enct ep ck h (l_mi L) FCmi Lep))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_mident_open Tsh (hhs3_IA x25519 R) (l_ia L) FCia LprivA))).
  sep_apply (derives_refl' _ _ (eq_sym (hhs3_p5_B_resp_open Ews m2 _ Hrok FCm2))).
  destruct (hhs3_mcr x25519 aead_dec R (Ei, encs, enct, ep, ck, h) M2) as [ST2|] eqn:E3.
  - forward.
    assert (Eacc: hhs3_p5_acc x25519 aead_dec R I (Ei, encs, enct, ep, ck, h) M2 = true)
      by (unfold hhs3_p5_acc; rewrite EA, EI, E3; reflexivity).
    destruct ST2 as [ck2 h2].
    hhs3_p5_B_close R S m1 m2 a0 f0 l0 I M1 H1 (Ei, encs, enct, ep, ck, h) nowb PA1 CI1 CI2 Q M2 H2 MR nowa Cre
      true (ck2, h2).
    entailer!.
  - forward.
    assert (Eacc: hhs3_p5_acc x25519 aead_dec R I (Ei, encs, enct, ep, ck, h) M2 = false)
      by (unfold hhs3_p5_acc; rewrite EA, EI, E3; reflexivity).
    hhs3_p5_B_close R S m1 m2 a0 f0 l0 I M1 H1 (Ei, encs, enct, ep, ck, h) nowb PA1 CI1 CI2 Q M2 H2 MR nowa Cre
      false (@nil byte, @nil byte).
    entailer!.
Qed.

End P5B.
