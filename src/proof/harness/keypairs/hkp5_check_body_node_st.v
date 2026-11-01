(* law keypairs: the cut of check_all's segment NODE
   (hkp5_check_body_node.v) into its 15 comparison stages, the final test and the hashed part, and the opened
   state of the stages. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Export WgNoise.proof.harness.keypairs.hkp5_check_body_defs.
Require Export WgNoise.proof.harness.keypairs.hkp5_check_body_node_lem.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

(* the left-nested sequence of the || chain *)
Fixpoint hkc5n_L (n: nat) (s: statement) : statement :=
  match n with O => s | S n' => match s with Ssequence a _ => hkc5n_L n' a | _ => Sskip end end.
Definition hkc5n_R (n: nat) (s: statement) : statement :=
  match hkc5n_L n s with Ssequence _ b => b | _ => Sskip end.

Definition hkc5n_skp : statement :=
  ltac:(let x := eval cbv delta [hkc5_node] in hkc5_node in
        let y := eval cbv beta iota in (match x with Ssequence s _ => s | _ => Sskip end) in exact y).
Definition hkc5n_X : statement :=
  ltac:(let x := eval cbv delta [hkc5_node] in hkc5_node in
        let y := eval cbv beta iota in
          (match x with Ssequence _ (Ssequence (Ssequence s _) _) => s | _ => Sskip end) in exact y).
Definition hkc5n_i30 : statement :=
  ltac:(let x := eval cbv delta [hkc5_node] in hkc5_node in
        let y := eval cbv beta iota in
          (match x with Ssequence _ (Ssequence (Ssequence _ s) _) => s | _ => Sskip end) in exact y).
Definition hkc5n_s56 : statement :=
  ltac:(let x := eval cbv delta [hkc5_node] in hkc5_node in
        let y := eval cbv beta iota in
          (match x with Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end) in exact y).
Definition hkc5n_ifh : statement :=
  ltac:(let x := eval cbv delta [hkc5_node] in hkc5_node in
        let y := eval cbv beta iota in
          (match x with Ssequence _ (Ssequence _ (Ssequence _ s)) => s | _ => Sskip end) in exact y).

Ltac hkc5n_stage n :=
  let x := eval cbv beta iota delta [hkc5n_R hkc5n_L hkc5n_X] in (hkc5n_R n hkc5n_X) in exact x.

Definition hkc5n_c14 : statement :=
  ltac:(let x := eval cbv beta iota delta [hkc5n_L hkc5n_X] in (hkc5n_L 14 hkc5n_X) in exact x).
Definition hkc5n_c15 : statement := ltac:(hkc5n_stage 13%nat).
Definition hkc5n_c16 : statement := ltac:(hkc5n_stage 12%nat).
Definition hkc5n_c17 : statement := ltac:(hkc5n_stage 11%nat).
Definition hkc5n_c18 : statement := ltac:(hkc5n_stage 10%nat).
Definition hkc5n_c20 : statement := ltac:(hkc5n_stage 9%nat).
Definition hkc5n_c22 : statement := ltac:(hkc5n_stage 8%nat).
Definition hkc5n_c23 : statement := ltac:(hkc5n_stage 7%nat).
Definition hkc5n_c24 : statement := ltac:(hkc5n_stage 6%nat).
Definition hkc5n_c25 : statement := ltac:(hkc5n_stage 5%nat).
Definition hkc5n_c26 : statement := ltac:(hkc5n_stage 4%nat).
Definition hkc5n_c27 : statement := ltac:(hkc5n_stage 3%nat).
Definition hkc5n_c28 : statement := ltac:(hkc5n_stage 2%nat).
Definition hkc5n_c29 : statement := ltac:(hkc5n_stage 1%nat).
Definition hkc5n_c30 : statement := ltac:(hkc5n_stage 0%nat).

Lemma hkc5n_node_eq_stmt :
  hkc5_node = Ssequence hkc5n_skp (Ssequence (Ssequence hkc5n_X hkc5n_i30) (Ssequence hkc5n_s56 hkc5n_ifh)).
Proof. reflexivity. Qed.

Lemma hkc5n_X_eq :
  hkc5n_X =
  Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence (Ssequence
  (Ssequence (Ssequence (Ssequence (Ssequence hkc5n_c14 hkc5n_c15) hkc5n_c16) hkc5n_c17) hkc5n_c18) hkc5n_c20)
  hkc5n_c22) hkc5n_c23) hkc5n_c24) hkc5n_c25) hkc5n_c26) hkc5n_c27) hkc5n_c28) hkc5n_c29) hkc5n_c30.
Proof. reflexivity. Qed.

(* the opened state of the stages: the node, the keypair's compared fields (at W_keypairs; lk the receiving
   counter's lock, bt its bitmap), its entry (sx its list link), P, the rest Fr; t: the stage's result (0) *)
Section St.
Variables (F: hkp5_fix) (P: peer) (m: val) (M: hk5_mk) (nx: val) (n: Z) (lk: val) (bt: list int64) (sx: val)
  (Fr: mpred).

Definition hkc5n_base : list localdef := temp KC._kp (m5_kp M) :: temp KC._k m :: hkc5_lv F n.

Definition hkc5n_sep : list mpred :=
  [@data_at W_keypairs Ews t_mk5 (hk5_mk_val M nx) m;
   @field_at W_keypairs Ews t_kp (DOT KC._sending) (symkey_val (mkSym (m5_send M) (m5_birth M) (m5_sv M))) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._receiving) (symkey_val (mkSym (m5_recv M) (m5_birth M) (m5_rv M))) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._remote_index) (Vint (m5_rindex M)) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._i_am_the_initiator) (Val.of_bool (m5_init M)) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._refcount) (Vint (m5_refs M)) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._internal_id) (Vlong (m5_id M)) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._sending_counter) (Vlong (m5_scnt M)) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._receiving_counter) (Vlong (m5_rcnt M), (lk, map Vlong bt)) (m5_kp M);
   @field_at W_keypairs Ews t_kp (DOT KC._entry)
     (entry_val (mkEntry (f_p F) IDX_KEYPAIR (m5_index M)) sx (m5_hashed M)) (m5_kp M);
   peer_rep Tsh (f_p F) P; Fr].

Definition hkc5n_St0 : environ -> mpred := PROPx [] (LOCALx hkc5n_base (SEPx hkc5n_sep)).
Definition hkc5n_St1 (t: ident) : environ -> mpred :=
  PROPx [] (LOCALx (temp t (Vint Int.zero) :: hkc5n_base) (SEPx hkc5n_sep)).

End St.

(* the facts every stage may use *)
Definition hkc5n_facts (m: val) (M: hk5_mk) : Prop :=
  isptr m /\ isptr (m5_kp M) /\ Zlength (m5_send M) = 32 /\ Zlength (m5_recv M) = 32.
