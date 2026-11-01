(* law handshake_receive, phase B4, segment C, part G:
   the agreement of the harness's target with the model (pure; port of hcy5_p11_agree).  Cut and states: hrx5_B4_C_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_C_defs.
Local Open Scope logic.

Definition hrx5_B4_C_G_sh (x: val * share * peer) : Prop := match x with (_, sh, _) => sh = Ews end.

(* the node search and the peer search agree (both find the first match, at the same position) *)
Lemma hrx5_B4_C_G_find T (NS: list hnode4) (PS: list (val * share * peer)) a :
  map hn_p NS = map peer_addr4 PS -> Forall (fun N => isptr (hn_addr N)) NS -> Forall (hrx5_B4_C_G_sh) PS ->
  (hrx5_nfind NS a = nullval -> sfind PS a = None) /\
  (hrx5_nfind NS a <> nullval ->
   exists P NS1 N NS2, sfind PS a = Some (Ews, P) /\ hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\
     hn_addr N = hrx5_nfind NS a /\ hn_rest N = prsnap_val P).
Proof.
  revert PS; induction NS as [|N0 NS IH]; intros [|[[p sh] P] PS] Hm Hptr Hsh; simpl in Hm; try discriminate.
  - split; [reflexivity | simpl; congruence].
  - inversion Hm as [[H1 H2]]. inversion Hptr; subst. inversion Hsh as [|? ? Hsh0 Hsh1]; subst.
    unfold hrx5_B4_C_G_sh in Hsh0. subst sh. simpl.
    destruct (EqDec_val (hn_p N0) a) as [e|ne].
    + split.
      * intros Hn. rewrite Hn in H3. simpl in H3. contradiction.
      * intros _. exists P, [], (hn_snapshot4 T N0 (hn_p N0, Ews, P)), (hnodes_snapped4 T NS PS).
        split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
    + destruct (IH PS H2 H4 Hsh1) as [IH1 IH2].
      split; [exact IH1|].
      intros Hn. destruct (IH2 Hn) as (P' & NS1 & N & NS2 & HP & HS & Ha & Hr).
      exists P', (hn_snapshot4 T N0 (hn_p N0, Ews, P) :: NS1), N, NS2.
      split; [exact HP|]. split; [|split; assumption].
      unfold hnodes_snapped4 in *. simpl. rewrite HS. reflexivity.
Qed.

Lemma hrx5_B4_C_G_ok : hrx5_B4_C_G_stmt.
Proof.
  intros x25519 xaead_dec R L NS PS KE T head nk M [Hok [_ [_ [_ [Hnp _]]]]] Hptr.
  assert (Hsh: Forall hrx5_B4_C_G_sh PS).
  { eapply Forall_impl; [|exact Hok]. intros [[p sh] P] H. exact (proj1 H). }
  unfold hrx5_B4_C_t0, hrx5ck_tgt, t_lookup.
  destruct (t_find_index T (t_L T) (cm_receiver M)) as [[a E]|]; [|split; [reflexivity | congruence]].
  destruct (Int.eq (Int.and (e_type E) (Int.or IDX_HANDSHAKE IDX_KEYPAIR)) Int.zero);
    [split; [reflexivity | congruence]|].
  destruct (hrx5_B4_C_G_find T NS PS (e_peer E) Hnp Hptr Hsh) as [G1 G2].
  split.
  - intros Hn. rewrite (G1 Hn). reflexivity.
  - intros Hn. destruct (G2 Hn) as (P & NS1 & N & NS2 & HP & HS & Ha & Hr).
    exists a, E, P, NS1, N, NS2. auto.
Qed.
