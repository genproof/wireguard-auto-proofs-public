(* The law hs_response_state: main's stack frame at a return.  struct pair, after any run in which each index
   table holds exactly its peer's handshake entry, and the two message buffers are uninitialised memory of
   their types again, in the world's compspecs (VST frees main's locals at its return). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol5.prot_repr5.
Require Import WgNoise.proof.harness.hs_common.hs_specs.
Require Import WgNoise.proof.harness.hs_common.hs_worlds.
Require Import WgNoise.proof.harness.hs_common.hs_close.
Require Import WgNoise.proof.harness.hs_response_state.hrs_conv.
Local Open Scope logic.

(* a message buffer after a create step is uninitialised memory of its type *)
Lemma hrs_init_close sh m Mo : init_opt_rep sh m Mo |-- @data_at_ Noise.CS sh t_init m.
Proof. destruct Mo; simpl; [apply hs_close_init | apply derives_refl]. Qed.
Lemma hrs_resp_close sh m Mo : resp_opt_rep sh m Mo |-- @data_at_ Noise.CS sh t_resp m.
Proof. destruct Mo; simpl; [apply hs_close_resp | apply derives_refl]. Qed.

Lemma hrs_close_frame p m r Mo Ro DA DB TA TB ka kb PA PB EA EB :
  @field_compatible CSh t_pair [] p ->
  t_D TA = [(hs_addr (pair_ap p), Tsh, EA)] -> t_D TB = [(hs_addr (pair_bp p), Tsh, EB)] ->
  init_opt_rep Tsh m Mo * resp_opt_rep Tsh r Ro *
  device_rep5 Tsh (pair_a p) DA * device_rep5 Tsh (pair_b p) DB *
  itable Tsh (pair_ai p) TA * itable Tsh (pair_bi p) TB *
  ptable Tsh (pair_ak p) ka * ptable Tsh (pair_bk p) kb *
  peer_rep5 Tsh (pair_ap p) PA * peer_rep5 Tsh (pair_bp p) PB
  |-- @data_at_ W_hrs Tsh (Tstruct HRS._pair noattr) p *
      @data_at_ W_hrs Tsh (Tstruct HRS._message_handshake_initiation noattr) m *
      @data_at_ W_hrs Tsh (Tstruct HRS._message_handshake_response noattr) r.
Proof.
  intros Hfc HA HB. rewrite hrs_conv_pair, hrs_conv_init, hrs_conv_resp.
  sep_apply (hs_pair_close Tsh p DA DB TA TB ka kb PA PB EA EB Hfc HA HB).
  sep_apply (hrs_init_close Tsh m Mo). sep_apply (hrs_resp_close Tsh r Ro). cancel.
Qed.
