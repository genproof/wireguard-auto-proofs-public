(* law keypairs: the segment HS (P's handshake entry).
*)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

Local Open Scope logic.

#[local] Instance hkc5_hs_CCE : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.

Lemma hkc5_hs_sfind_in {A: Type} (D: list (val * share * A)) a sh E :
  sfind D a = Some (sh, E) -> In a (saddrs D).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [left; auto | right; auto].
Qed.

Lemma hkc5_hs_pool_split {A: Type} (D: list (val * share * A)) a sh E (f: val * share * A -> mpred) :
  sfind D a = Some (sh, E) -> iter_sepcon f D = f (a, sh, E) * iter_sepcon f (sdel D a).
Proof.
  induction D as [|[[x shx] w] D IH]; simpl; intros Hs; [discriminate|].
  destruct (EqDec_val x a); [inv Hs; reflexivity|].
  rewrite (IH Hs); simpl. rewrite <- !sepcon_assoc, (sepcon_comm (f _) (f _)). reflexivity.
Qed.

(* P's handshake entry in the pool, as a field of P at main's compspecs *)
Lemma hkc5_hs_entry_eq sh p v :
  @field_compatible Noise.CS t_peer [] p ->
  @data_at Noise.CS sh t_entry_s v (hs_addr p) =
  @field_at W_keypairs sh t_peer (DOT prot_repr3.I._handshake DOT prot_repr3.I._entry) v p.
Proof.
  intros FC.
  assert (Hc: cs_preserve_type Noise.CS W_keypairs (@coeq _ _ hkc5_hs_CCE) t_peer = true) by (vm_compute; reflexivity).
  rewrite <- (@field_at_change_composite Noise.CS W_keypairs hkc5_hs_CCE sh t_peer
                (DOT prot_repr3.I._handshake DOT prot_repr3.I._entry) v v (JMeq_refl _) Hc).
  rewrite (@field_at_data_at Noise.CS). rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  reflexivity.
Qed.

Lemma hkc5_hs_open sht t T p she E :
  @field_compatible Noise.CS t_peer [] p -> sfind (t_D T) (hs_addr p) = Some (she, E) ->
  itable sht t T =
  !! itable_wf T &&
  (@data_at Noise.CS sht t_itab (hd nullval (t_L T)) t *
   @field_at W_keypairs she t_peer (DOT prot_repr3.I._handshake DOT prot_repr3.I._entry)
     (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) p *
   iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p))).
Proof.
  intros FC HS. unfold itable. rewrite (hkc5_hs_pool_split _ _ _ _ _ HS).
  unfold pool_item_rep at 1, entry_at. rewrite hkc5_hs_entry_eq by auto.
  rewrite sepcon_assoc. reflexivity.
Qed.

Lemma hkc5_hs_close sht t T p she E b :
  @field_compatible Noise.CS t_peer [] p -> sfind (t_D T) (hs_addr p) = Some (she, E) -> itable_wf T ->
  vin (hs_addr p) (t_L T) = b ->
  @data_at Noise.CS sht t_itab (hd nullval (t_L T)) t *
  @field_at W_keypairs she t_peer (DOT prot_repr3.I._handshake DOT prot_repr3.I._entry)
    (e_peer E, (succ_in (t_L T) (hs_addr p), (Val.of_bool b, (Vint (e_type E), Vint (e_index E))))) p *
  iter_sepcon (pool_item_rep (t_L T)) (sdel (t_D T) (hs_addr p)) |-- itable sht t T.
Proof.
  intros FC HS W <-. rewrite (hkc5_hs_open sht t T p she E FC HS). apply andp_right; [apply prop_right; auto|].
  unfold entry_val. apply derives_refl.
Qed.

Lemma hkc5_hs_ok : hkc5_hs_stmt.
Proof.
  intros Espec F T P idx n FR R HS HC.
  destruct R as [Rn Rb Rc Rr]. unfold hkc5_PH, hkc5_lv.
  set (p := f_p F) in *. set (t := f_t F) in *.
  assert_PROP (@field_compatible Noise.CS t_peer [] p) as FC by (unfold peer_rep; entailer!).
  rewrite (hkc5_hs_open Tsh t T p Tsh _ FC HS). Intros. rename H into W.
  unfold hkc5_hs. unfold entry_val. destruct (vin (hs_addr p) (t_L T)) eqn:HV.
  - forward. forward_if.
    2: { exfalso. discriminate. }
    sep_apply (hkc5_hs_close Tsh t T p Tsh _ true FC HS W HV).
    forward_call (Tsh, t, T, hs_addr p).
    { destruct FC; auto. }
    { apply (hkc5_hs_sfind_in _ _ _ _ HS). }
    rewrite HV. specialize (HC eq_refl).
    forward_if (temp KC._t'35 (Vint Int.zero)).
    { exfalso. discriminate. }
    { rewrite (hkc5_hs_open Tsh t T p Tsh _ FC HS). Intros. unfold entry_val. rewrite HV.
      forward.
      sep_apply (hkc5_hs_close Tsh t T p Tsh _ true FC HS W HV).
      forward_call (Tsh, t, T, idx).
      rewrite HC. cbn [e_index]. forward.
      entailer!. }
    forward_if.
    { exfalso. auto. }
    forward.
    entailer!.
    rewrite (hkc5_hs_open Tsh t T p Tsh _ FC HS). unfold entry_val. rewrite HV. apply andp_left2. apply derives_refl.
  - forward. forward_if.
    { exfalso. discriminate. }
    forward.
    entailer!.
Qed.
