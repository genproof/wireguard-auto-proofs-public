(* law replay: the persistent locals back to data_at_ (for main's two returns: the stack frame).
   A's table holds pb's handshake entry (hashed or not), B's holds pa's (unhashed); each peer gets its entry
   back (prot_rep_lemmas3: peer_rep * entry_at |-- data_at_ t_peer).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

Section CloseNoise.
#[local] Existing Instance Noise.CS.

Lemma hrp3_close_dev sh wg D : device_rep sh wg D |-- data_at_ sh t_dev wg.
Proof.
  unfold device_rep, identity_rep, checker_rep, id_addr, cc_addr.
  Intros. Intros lk1 lk2.
  unfold_data_at (data_at_ sh t_dev wg).
  rewrite (field_at_data_at sh t_dev [StructField I._static_identity]).
  rewrite (field_at_data_at sh t_dev [StructField I._cookie_checker]).
  rewrite !field_address_offset by auto with field_compatible.
  rewrite <- !sepcon_assoc.
  repeat apply sepcon_derives; first [exact (field_at_field_at_ _ _ _ _ _) | exact (data_at_data_at_ _ _ _ _)].
Qed.

(* an index table whose pool is one entry *)
Lemma hrp3_close_itab sht tab T a sh E :
  t_D T = [(a, sh, E)] ->
  itable sht tab T |-- data_at_ sht t_itab tab * EX n: val, EX h: bool, entry_at sh a E n h.
Proof.
  intros HD. unfold itable. rewrite HD. Intros. simpl.
  Exists (succ_in (t_L T) a) (vin a (t_L T)).
  rewrite sepcon_emp. cancel.
Qed.

End CloseNoise.

#[local] Instance hrp3_CCE : change_composite_env Noise.CS W_replay.
Proof. make_cs_preserve Noise.CS W_replay. Defined.

Lemma hrp3_close_cs_dev sh p :
  @data_at_ Noise.CS sh t_dev p = @data_at_ W_replay sh (Tstruct RC._wg_device noattr) p.
Proof.
  change (Tstruct RC._wg_device noattr) with t_dev.
  rewrite (@data_at__change_composite Noise.CS W_replay hrp3_CCE sh t_dev) by reflexivity; reflexivity.
Qed.
Lemma hrp3_close_cs_itab sh p :
  @data_at_ Noise.CS sh t_itab p = @data_at_ W_replay sh (Tstruct RC._index_hashtable noattr) p.
Proof.
  change (Tstruct RC._index_hashtable noattr) with t_itab.
  rewrite (@data_at__change_composite Noise.CS W_replay hrp3_CCE sh t_itab) by reflexivity; reflexivity.
Qed.
Lemma hrp3_close_cs_ptab sh p :
  @data_at_ Noise.CS sh t_ptab p = @data_at_ W_replay sh (Tstruct RC._pubkey_hashtable noattr) p.
Proof.
  change (Tstruct RC._pubkey_hashtable noattr) with t_ptab.
  rewrite (@data_at__change_composite Noise.CS W_replay hrp3_CCE sh t_ptab) by reflexivity; reflexivity.
Qed.
Lemma hrp3_close_cs_peer sh p :
  @data_at_ Noise.CS sh t_peer p = @data_at_ W_replay sh (Tstruct RC._wg_peer noattr) p.
Proof.
  change (Tstruct RC._wg_peer noattr) with t_peer.
  rewrite (@data_at__change_composite Noise.CS W_replay hrp3_CCE sh t_peer) by reflexivity; reflexivity.
Qed.

Lemma hrp3_close : hrp3_rep_facts -> hrp3_close_fact.
Proof.
  intros (_ & _ & _ & _ & _ & _ & Hpeer & _).
  intros F DA DB TA PB PA (E & HD & _).
  sep_apply (hrp3_close_dev Tsh (f_wa F) DA).
  sep_apply (hrp3_close_dev Tsh (f_wb F) DB).
  sep_apply (hrp3_close_itab Tsh (f_ita F) TA _ _ _ HD).
  sep_apply (hrp3_close_itab Tsh (f_itb F) (hrp3_TB0 (f_pa F)) _ _ _ (eq_refl _)).
  Intros n2 h2 n1 h1.
  sep_apply (Hpeer Tsh (f_pb F) PB E n1 h1).
  sep_apply (Hpeer Tsh (f_pa F) PA (hrp3_E0 (f_pa F)) n2 h2).
  unfold ptable.
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab (f_pb F) (f_pta F)).
  sep_apply (@data_at_data_at_ Noise.CS Tsh t_ptab (f_pa F) (f_ptb F)).
  rewrite !hrp3_close_cs_dev, !hrp3_close_cs_itab, !hrp3_close_cs_ptab, !hrp3_close_cs_peer.
  cancel.
Qed.
