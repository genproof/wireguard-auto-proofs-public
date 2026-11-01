(* law keypairs: the live loop LOOP from NODE.  NODE and the count_index fact are hypotheses. *)
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
Local Open Scope logic.

Local Notation iter_sepcon := VST.msl.iter_sepcon.iter_sepcon.

#[local] Instance hkc5_inh_mk : Inhabitant hk5_mk :=
  mkMK5 nullval Int.zero Int64.zero false Int.zero [] [] false false false Int.zero Int64.zero Int64.zero
        Int64.zero Int64.zero.
#[local] Instance hkc5_inh_kp : Inhabitant keypair :=
  mkKP (mkSym [] Int64.zero false) Int64.zero (mkSym [] Int64.zero false) Int64.zero [] Int.zero false Int.zero
       Int64.zero.

(* a segment stated for any R with overridePost, used where the next state is R's normal one *)
Lemma hkc5_use {Espec: OracleKind} {cs: compspecs} Delta P Q c (R: ret_assert) :
  ENTAIL Delta, Q |-- RA_normal R -> @semax cs Espec Delta P c (overridePost Q R) -> @semax cs Espec Delta P c R.
Proof.
  intros HQ HS. eapply semax_post; [ | | | | exact HS]; destruct R; unfold overridePost; cbn;
  auto; intros; apply andp_left2; apply derives_refl.
Qed.

Lemma hkc5_kps_cons CSw k K (l: list (val * keypair)) :
  keypairs_rep CSw ((k, K) :: l) = (keypair_rep CSw k K * keypairs_rep CSw l)%logic.
Proof. reflexivity. Qed.

Lemma hkc5_kps_app CSw (l1 l2: list (val * keypair)) :
  keypairs_rep CSw (l1 ++ l2) = (keypairs_rep CSw l1 * keypairs_rep CSw l2)%logic.
Proof.
  induction l1 as [|[k K] l1 IH]; cbn [app].
  - unfold keypairs_rep at 2. cbn [iter_sepcon]. rewrite emp_sepcon. reflexivity.
  - rewrite !hkc5_kps_cons, IH, sepcon_assoc. reflexivity.
Qed.

Lemma hkc5_nh_snoc (L: list (val * hk5_mk)) x :
  hkc5_nh (L ++ [x]) = hkc5_nh L + (if m5_hashed (snd x) then 1 else 0).
Proof.
  unfold hkc5_nh. rewrite filter_app, Zlength_app. cbn [filter].
  destruct (m5_hashed (snd x)); reflexivity.
Qed.

Lemma hkc5_mklist_head ML : hk5_mklist ML |-- !! is_pointer_or_null (hk5_head ML).
Proof.
  destruct ML as [|[m M] ML]; cbn [hk5_mklist hk5_head].
  - entailer!.
  - unfold hk5_node. Intros. entailer!.
Qed.

(* the live list cut at a node *)
Definition hkc5_hd (l: list (val * hk5_mk)) (z: val) : val := match l with [] => z | (a, _) :: _ => a end.

Fixpoint hkc5_seg (L: list (val * hk5_mk)) (z: val) : mpred :=
  match L with
  | [] => emp
  | (m, M) :: L' => hk5_node m M (hkc5_hd L' z) * hkc5_seg L' z
  end.

Lemma hkc5_mklist_app L1 L2 :
  hk5_mklist (L1 ++ L2) = hkc5_seg L1 (hk5_head L2) * hk5_mklist L2.
Proof.
  induction L1 as [|[m M] L1 IH]; cbn [app hk5_mklist hkc5_seg].
  - rewrite emp_sepcon; auto.
  - rewrite IH, sepcon_assoc.
    replace (hk5_head (L1 ++ L2)) with (hkc5_hd L1 (hk5_head L2)); [reflexivity|].
    destruct L1 as [|[a A] L1']; reflexivity.
Qed.

Lemma hkc5_seg_snoc L m M z :
  hkc5_seg (L ++ [(m, M)]) z = hkc5_seg L m * hk5_node m M z.
Proof.
  induction L as [|[a A] L IH]; cbn [app hkc5_seg hkc5_hd].
  - rewrite emp_sepcon, sepcon_emp; auto.
  - rewrite IH, <- sepcon_assoc.
    replace (hkc5_hd (L ++ [(m, M)]) z) with (hkc5_hd L m); [reflexivity|].
    destruct L as [|[b B] L']; reflexivity.
Qed.

Definition hkc5_LS (F: hkp5_fix) (P: peer) (T: tstate) (KS: list (val * keypair)) (ML: list (val * hk5_mk))
  (Rm: mpred) (n: Z) : environ -> mpred :=
  PROPx []
  (LOCALx (hkc5_lv F n)
  (SEPx [peer_rep Tsh (f_p F) P; itable Tsh (f_t F) T; keypairs_rep W_keypairs KS;
         data_at Ews (tptr t_mk5) (hk5_head ML) (f_gv F KC._live); hk5_mklist ML; Rm])).

(* LOOP with any frame Rm *)
Lemma hkc5_loop_core {Espec: OracleKind} F P T KS ML (Rm: mpred) (R: ret_assert) :
  hkc5_node_stmt -> hkc5_count_index_stmt ->
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match (f_p F) T (snd x) (snd y)) ML KS ->
  ~ In nullval (map fst ML) ->
  NoDup (t_indices T (t_L T)) ->
  semax hkc5_Delta (hkc5_LS F P T KS ML Rm 0) hkc5_loop
    (overridePost (hkc5_LS F P T KS ML Rm (hkc5_nh ML)) R).
Proof.
  intros HNODE HCI HF2 HNm HNDi.
  assert (LEN: Zlength KS = Zlength ML).
  { apply Forall2_length in HF2. rewrite !Zlength_correct. lia. }
  rewrite hkc5_loop_eq. unfold hkc5_LS, hkc5_lv.
  destruct R as [Rn Rb Rc Rr]. unfold overridePost.
  assert_PROP (is_pointer_or_null (hk5_head ML)) as HPN by (sep_apply (hkc5_mklist_head ML); entailer!).
  forward.
  forward_loop
    (EX i: Z,
     PROP (0 <= i <= Zlength ML)
     LOCAL (temp KC._k (hk5_head (sublist i (Zlength ML) ML));
            temp KC._hashed (Vlong (Int64.repr (hkc5_nh (sublist 0 i ML)))); temp KC._p (f_p F);
            temp KC._t (f_t F); temp KC._w (f_w F); gvars (f_gv F))
     SEP (peer_rep Tsh (f_p F) P; itable Tsh (f_t F) T; keypairs_rep W_keypairs (sublist 0 i KS);
          keypairs_rep W_keypairs (sublist i (Zlength ML) KS);
          data_at Ews (tptr t_mk5) (hk5_head ML) (f_gv F KC._live);
          hkc5_seg (sublist 0 i ML) (hk5_head (sublist i (Zlength ML) ML)); hk5_mklist (sublist i (Zlength ML) ML);
          Rm))
  continue:
    (EX i: Z,
     PROP (0 <= i < Zlength ML)
     LOCAL (temp KC._k (fst (Znth i ML));
            temp KC._hashed (Vlong (Int64.repr (hkc5_nh (sublist 0 (i + 1) ML)))); temp KC._p (f_p F);
            temp KC._t (f_t F); temp KC._w (f_w F); gvars (f_gv F))
     SEP (peer_rep Tsh (f_p F) P; itable Tsh (f_t F) T; keypairs_rep W_keypairs (sublist 0 (i + 1) KS);
          keypairs_rep W_keypairs (sublist (i + 1) (Zlength ML) KS);
          data_at Ews (tptr t_mk5) (hk5_head ML) (f_gv F KC._live);
          hkc5_seg (sublist 0 i ML) (fst (Znth i ML));
          hk5_node (fst (Znth i ML)) (snd (Znth i ML)) (hk5_head (sublist (i + 1) (Zlength ML) ML));
          hk5_mklist (sublist (i + 1) (Zlength ML) ML); Rm))
  break:
    (PROP ()
     LOCAL (temp KC._hashed (Vlong (Int64.repr (hkc5_nh ML))); temp KC._p (f_p F); temp KC._t (f_t F);
            temp KC._w (f_w F); gvars (f_gv F))
     SEP (peer_rep Tsh (f_p F) P; itable Tsh (f_t F) T; keypairs_rep W_keypairs KS;
          data_at Ews (tptr t_mk5) (hk5_head ML) (f_gv F KC._live); hk5_mklist ML; Rm)).
  - (* entry *)
    Exists 0.
    rewrite !sublist_nil, (sublist_same 0 (Zlength ML) ML), (sublist_same 0 (Zlength ML) KS) by lia.
    change (hkc5_nh []) with 0. change (keypairs_rep W_keypairs []) with (@emp mpred _ _). cbn [hkc5_seg].
    entailer!.
  - (* body *)
    Intros i.
    assert (i = Zlength ML \/ i < Zlength ML) as [-> | Hi] by lia.
    + (* the end of the list: break *)
      rewrite !sublist_nil; cbn [hk5_head].
      forward_if; [contradiction |].
      forward.
      rewrite (sublist_same 0 (Zlength ML) ML), (sublist_same 0 (Zlength ML) KS) by lia.
      pose proof (hkc5_mklist_app ML []) as EL.
      rewrite app_nil_r in EL; cbn [hk5_head] in EL.
      rewrite EL.
      change (keypairs_rep W_keypairs []) with (@emp mpred _ _).
      entailer!.
    + (* node i *)
      rewrite (sublist_next i (Zlength ML) ML) by lia.
      rewrite (sublist_next i (Zlength ML) KS) by lia.
      pose proof (Forall2_Znth _ _ _ HF2 i ltac:(lia)) as [EK HM].
      destruct (Znth i ML) as [m M] eqn:EM. destruct (Znth i KS) as [k K] eqn:EK'.
      cbn [fst snd] in EK, HM. subst k.
      assert (Hm: In m (map fst ML)).
      { apply (in_map fst ML (m, M)). rewrite <- EM. apply Znth_In. lia. }
      cbn [hk5_head hk5_mklist]. rewrite hkc5_kps_cons.
      forward_if.
      * (* tc of the test: the node is a valid pointer *)
        unfold hk5_node. Intros. entailer!.
      * (* the node *)
        assert (HCm: m5_hashed M = true -> count_index T (m5_index M) = 1).
        { intros Hh. destruct HM as (_ & Hs & Hv & _).
          apply (HCI T (m5_kp M) (mkEntry (f_p F) IDX_KEYPAIR (m5_index M))); auto.
          - unfold vin in Hv. destruct (in_dec eq_dec (m5_kp M) (t_L T)); [auto | congruence].
          - unfold t_entry. rewrite Hs. reflexivity. }
        eapply hkc5_use;
          [ | eapply semax_pre;
              [ | apply (HNODE Espec F T P m M (hk5_head (sublist (i+1) (Zlength ML) ML)) K
                     (hkc5_nh (sublist 0 i ML))
                     (keypairs_rep W_keypairs (sublist 0 i KS) *
                      keypairs_rep W_keypairs (sublist (i + 1) (Zlength ML) KS) *
                      data_at Ews (tptr t_mk5) (hk5_head ML) (f_gv F KC._live) * hkc5_seg (sublist 0 i ML) m *
                      hk5_mklist (sublist (i + 1) (Zlength ML) ML) * Rm)%logic); auto ] ].
        2: unfold hkc5_PN, hkc5_lv; entailer!.
        unfold POSTCONDITION, abbreviate. cbn [RA_normal loop1_ret_assert].
        Exists i.
        rewrite EM. cbn [fst snd].
        rewrite (sublist_split 0 i (i+1) ML), (sublist_split 0 i (i+1) KS) by lia.
        rewrite (sublist_len_1 i ML), (sublist_len_1 i KS) by lia. rewrite EM, EK'.
        rewrite hkc5_nh_snoc, hkc5_kps_app, hkc5_kps_cons. cbn [snd].
        change (keypairs_rep W_keypairs []) with (@emp mpred _ _).
        unfold hkc5_PN, hkc5_lv. entailer!.
      * (* k is not NULL *)
        exfalso. apply HNm. match goal with Hx: m = nullval |- _ => rewrite <- Hx end. exact Hm.
  - (* k = k->next *)
    Intros i.
    assert (Eseg: hkc5_seg (sublist 0 (i+1) ML) (hk5_head (sublist (i+1) (Zlength ML) ML)) =
      (hkc5_seg (sublist 0 i ML) (fst (Znth i ML)) *
       hk5_node (fst (Znth i ML)) (snd (Znth i ML)) (hk5_head (sublist (i+1) (Zlength ML) ML)))%logic).
    { rewrite (sublist_split 0 i (i+1)) by lia. rewrite sublist_len_1 by lia. destruct (Znth i ML) as [m M].
      apply hkc5_seg_snoc. }
    assert_PROP (is_pointer_or_null (hk5_head (sublist (i+1) (Zlength ML) ML))) as HPN'
      by (sep_apply (hkc5_mklist_head (sublist (i+1) (Zlength ML) ML)); entailer!).
    unfold hk5_node at 1. Intros. unfold hk5_mk_val.
    forward.
    Exists (i + 1). rewrite Eseg. unfold hk5_node, hk5_mk_val. entailer!.
  - (* break -> post *)
    unfold POSTCONDITION, abbreviate. cbn [RA_normal]. entailer!.
Qed.
