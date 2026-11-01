(* law cookie_reply: phase P8 of main, statements
   52: kes = kents_add(&ita, peers, NULL, 1).

   (+ its children's files). *)
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
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

Ltac hcy5_p8_dif := match goal with |- context [if ?c then _ else _] => destruct c end.

(* ---- the node list's head ---- *)
Lemma hcy5_p8_hnodes_head l NS :
  hnodes_rep4 W l NS |-- !! (is_pointer_or_null l /\ (l = nullval -> NS = [])).
Proof.
  destruct NS as [|N NS]; simpl.
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible _ _ (hn_addr N) |- _ => apply field_compatible_isptr in Hf end.
    split; [destruct (hn_addr N); simpl in *; auto; contradiction |].
    intros Hn; rewrite Hn in *; contradiction.
Qed.

(* ---- the peers after the slot fills ---- *)
Lemma hcy5_p8_fill_proj P k c :
  p_device (fill_slot P k c) = p_device P /\ p_hs (fill_slot P k c) = p_hs P /\
  p_refs (fill_slot P k c) = p_refs P /\ p_cookie (fill_slot P k c) = p_cookie P /\
  p_pknext (fill_slot P k c) = p_pknext P.
Proof.
  unfold fill_slot, p_set_slots.
  repeat (first [destruct (Z.eq_dec _ _) | destruct (eq_dec _ _)]); cbn; auto 10.
Qed.

Lemma hcy5_p8_pok_mono L KS KS' x :
  incl KS KS' -> hcy5_pok L KS x -> hcy5_pok L KS' x.
Proof.
  intros Hi. destruct x as [[a sh] P]. unfold hcy5_pok.
  intros (H1 & H2 & H3 & H4 & H5 & H6). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 _))))).
  eapply Forall_impl; [| exact H6]. intros k [Hk | Hk]; [left | right]; auto.
Qed.

Lemma hcy5_p8_pok_fill L KS a sh P k c :
  In k KS -> hcy5_pok L KS (a, sh, P) -> hcy5_pok L KS (a, sh, fill_slot P k c).
Proof.
  intros Hk. unfold hcy5_pok. intros (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (hcy5_p8_fill_proj P k c) as (E1 & E2 & E3 & E4 & _).
  rewrite E1, E2, E3, E4. refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 _))))).
  inversion H6 as [| ? ? Hc H6']; subst. inversion H6' as [| ? ? Hp H6'']; subst.
  inversion H6'' as [| ? ? Hn _]; subst.
  unfold fill_slot, p_set_slots.
  repeat (first [destruct (Z.eq_dec _ _) | destruct (eq_dec _ _)]); cbn;
    repeat apply Forall_cons; try apply Forall_nil; tauto.
Qed.

Lemma hcy5_p8_fill_pok L KS PS d :
  In (kd_addr d) KS -> Forall (hcy5_pok L KS) PS -> Forall (hcy5_pok L KS) (fill_peers PS d).
Proof.
  intros Hk HF. unfold fill_peers. rewrite Forall_map. eapply Forall_impl; [| exact HF].
  intros [[a sh] P] Hp. unfold Basics.compose. cbv beta iota.
  destruct (eq_dec a (kd_owner d)); [apply hcy5_p8_pok_fill; auto | exact Hp].
Qed.

Lemma hcy5_p8_fill_addrs PS d : map peer_addr4 (fill_peers PS d) = map peer_addr4 PS.
Proof.
  unfold fill_peers. rewrite map_map. apply map_ext. intros [[a sh] P]. hcy5_p8_dif; reflexivity.
Qed.

Lemma hcy5_p8_fill_phead PS d : hcy5_phead (fill_peers PS d) = hcy5_phead PS.
Proof. destruct PS as [| [[a sh] P] PS]; cbn; [reflexivity |]. hcy5_p8_dif; reflexivity. Qed.

Lemma hcy5_p8_fill_chain h PS d : pk_chain h PS -> pk_chain h (fill_peers PS d).
Proof.
  revert h. induction PS as [| [[a sh] P] PS IH]; intros h; cbn; [auto |].
  intros [-> Hc]. hcy5_p8_dif; cbn; split; auto.
  pose proof (hcy5_p8_fill_proj P (kd_addr d) (kd_slot d)) as (_ & _ & _ & _ & E). rewrite E. auto.
Qed.

Lemma hcy5_p8_fill_combine (NS: list hnode4) PS d N a sh P :
  In (N, (a, sh, P)) (combine NS PS) ->
  exists P', In (N, (a, sh, P')) (combine NS (fill_peers PS d)) /\ p_hs P' = p_hs P.
Proof.
  revert PS. induction NS as [| N0 NS IH]; intros PS; cbn; [tauto |].
  destruct PS as [| [[a0 sh0] P0] PS]; cbn; [tauto |].
  intros [Heq | Hin].
  - inversion Heq; subst. hcy5_p8_dif.
    + exists (fill_slot P (kd_addr d) (kd_slot d)). split; [left; reflexivity |].
      apply (hcy5_p8_fill_proj P (kd_addr d) (kd_slot d)).
    + exists P. split; [left; reflexivity | reflexivity].
  - destruct (IH PS Hin) as (P' & H1 & H2). exists P'. split; [right; exact H1 | exact H2].
Qed.

Lemma hcy5_p8_PS_lists L NS PS KD :
  hcy5_lists_ok L [] NS PS ->
  hcy5_lists_ok L (map kd_addr KD) NS (kents_PS true PS KD).
Proof.
  intros (H1 & H2 & H3 & H4 & H5).
  induction KD as [| d KD (I1 & I2 & I3 & I4 & I5)]; cbn [kents_PS].
  - refine (conj _ (conj H2 (conj H3 (conj H4 H5)))). eapply Forall_impl; [| exact H1].
    intros x. apply hcy5_p8_pok_mono. intros ? [].
  - unfold hcy5_lists_ok, hnodes_peers4 in *. rewrite hcy5_p8_fill_addrs, hcy5_p8_fill_phead.
    refine (conj _ (conj I2 (conj I3 (conj I4 _)))).
    + apply hcy5_p8_fill_pok; [left; reflexivity |].
      eapply Forall_impl; [| exact I1]. intros x. apply hcy5_p8_pok_mono. intros k Hk. right; exact Hk.
    + apply hcy5_p8_fill_chain. exact I5.
Qed.

Lemma hcy5_p8_PS_addrs PS KD : map peer_addr4 (kents_PS true PS KD) = map peer_addr4 PS.
Proof. induction KD as [| d KD IH]; cbn [kents_PS]; [reflexivity |]. rewrite hcy5_p8_fill_addrs. exact IH. Qed.

Lemma hcy5_p8_PS_phead PS KD : hcy5_phead (kents_PS true PS KD) = hcy5_phead PS.
Proof. induction KD as [| d KD IH]; cbn [kents_PS]; [reflexivity |]. rewrite hcy5_p8_fill_phead. exact IH. Qed.

Lemma hcy5_p8_PS_np pubB NS PS KD np :
  hcy5_np_ok pubB NS PS np -> hcy5_np_ok pubB NS (kents_PS true PS KD) np.
Proof.
  intros Hn. induction KD as [| d KD IH]; cbn [kents_PS]; [exact Hn |].
  destruct IH as [-> | (N & a & P & Hin & Ha & Hs)]; [left; reflexivity | right].
  destruct (hcy5_p8_fill_combine NS _ d N a Ews P Hin) as (P' & H1 & H2).
  exists N, a, P'. rewrite H2. auto.
Qed.

(* ---- the table after the kents ---- *)
Lemma hcy5_p8_in_vremove a m L : In a (vremove m L) -> In a L /\ a <> m.
Proof.
  induction L as [| x L IH]; cbn; [tauto |].
  destruct (EqDec_val x m) as [-> | Hx]; intros H.
  - destruct (IH H); auto.
  - destruct H as [<- | H]; [auto |]. destruct (IH H); auto.
Qed.

Lemma hcy5_p8_vremove_nodup {B: Type} (f: val -> B) m L :
  NoDup (map f L) -> NoDup (map f (vremove m L)).
Proof.
  induction L as [| x L IH]; cbn; intros H; [constructor |].
  inversion H; subst. destruct (EqDec_val x m); [auto |]. cbn. constructor; [| auto].
  intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Hy & Hin).
  apply hcy5_p8_in_vremove in Hin. destruct Hin as [Hin _]. apply H2. rewrite <- Hy. apply in_map; auto.
Qed.

Lemma hcy5_p8_ins_D T m sh E0 idx :
  t_D (t_insert (t_add T m sh E0) m idx) = (m, sh, mkEntry (e_peer E0) (e_type E0) idx) :: t_D T.
Proof.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd; cbn.
  destruct (EqDec_val m m) as [_ | Hn]; [| congruence]. cbn.
  destruct (EqDec_val m m) as [_ | Hn]; [reflexivity | congruence].
Qed.

Lemma hcy5_p8_ins_L T m sh E0 idx :
  t_L (t_insert (t_add T m sh E0) m idx) = m :: vremove m (t_L T).
Proof.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd; cbn.
  destruct (EqDec_val m m) as [_ | Hn]; [reflexivity | congruence].
Qed.

Lemma hcy5_p8_ins_entry_ne T m sh E0 idx a : a <> m ->
  t_entry (t_insert (t_add T m sh E0) m idx) a = t_entry T a.
Proof.
  intros Ha. unfold t_entry at 1. rewrite hcy5_p8_ins_D. cbn.
  destruct (EqDec_val m a) as [-> | _]; [congruence | reflexivity].
Qed.

Lemma hcy5_p8_ins_entry_eq T m sh E0 idx :
  t_entry (t_insert (t_add T m sh E0) m idx) m = Some (mkEntry (e_peer E0) (e_type E0) idx).
Proof.
  unfold t_entry. rewrite hcy5_p8_ins_D. cbn.
  destruct (EqDec_val m m) as [_ | Hn]; [reflexivity | congruence].
Qed.

Lemma hcy5_p8_add_entry_ne T m sh E0 a : a <> m -> t_entry (t_add T m sh E0) a = t_entry T a.
Proof.
  intros Ha. unfold t_entry, t_add. cbn.
  destruct (EqDec_val m a) as [-> | _]; [congruence | reflexivity].
Qed.

Lemma hcy5_p8_KT_D T KD :
  t_D (kents_T T KD) = map (fun d => (kd_addr d, Ews, mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d))) KD ++ t_D T.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T]; [reflexivity |].
  rewrite hcy5_p8_ins_D. cbn [t_D t_add map app]. rewrite IH. reflexivity.
Qed.

Lemma hcy5_p8_KT_idx T KD :
  kents_fresh T KD -> NoDup (t_indices T (t_L T)) -> NoDup (t_indices (kents_T T KD) (t_L (kents_T T KD))).
Proof.
  intros Hfr Hnd. induction KD as [| d KD IH]; cbn [kents_T]; [exact Hnd |].
  destruct Hfr as [Hfr Hf]. specialize (IH Hfr).
  set (T' := kents_T T KD) in *. set (m := kd_addr d) in *.
  rewrite hcy5_p8_ins_L. unfold t_indices. cbn [map]. rewrite hcy5_p8_ins_entry_eq. cbn [e_index].
  unfold t_fresh, t_indices in Hf. cbn [t_L t_add] in Hf.
  assert (Heq: forall g, (forall a, a <> m -> g a = t_entry T' a) ->
    map (fun a => match g a with Some E => e_index E | None => Int.zero end) (vremove m (t_L T')) =
    map (fun a => match t_entry T' a with Some E => e_index E | None => Int.zero end) (vremove m (t_L T'))).
  { intros g Hg. apply map_ext_in. intros a Ha. apply hcy5_p8_in_vremove in Ha. rewrite Hg by tauto. reflexivity. }
  rewrite (Heq _ (hcy5_p8_ins_entry_ne T' m Ews (kd_entry d) (kd_idx d))).
  rewrite (Heq _ (hcy5_p8_add_entry_ne T' m Ews (kd_entry d))) in Hf.
  constructor; [exact Hf |]. apply hcy5_p8_vremove_nodup. exact IH.
Qed.

Lemma hcy5_p8_sfind_in (D: list (val * share * entry)) a sh E :
  NoDup (saddrs D) -> In (a, sh, E) D -> sfind D a = Some (sh, E).
Proof.
  induction D as [| [[x shx] Ex] D IH]; cbn; [tauto |].
  intros Hnd Hin. inversion Hnd as [| ? ? Hx Hnd']; subst.
  destruct Hin as [Heq | Hin].
  - inversion Heq; subst. destruct (EqDec_val a a); [reflexivity | congruence].
  - destruct (EqDec_val x a) as [-> | _]; [| auto].
    exfalso. apply Hx. unfold saddrs. apply in_map_iff. exists (a, sh, E). auto.
Qed.

Lemma hcy5_p8_T_ok PS T KD :
  hcy5_T_ok PS [] T -> kents_draws_ok PS KD -> kents_fresh T KD ->
  NoDup (saddrs (t_D (kents_T T KD))) ->
  hcy5_T_ok (kents_PS true PS KD) (map kd_kent KD) (kents_T T KD).
Proof.
  intros ((own & ix & HD & _) & Hnd) (HK & _) Hfr Hnd'.
  set (T' := kents_T T KD) in *.
  assert (HTD: t_D T' = map (fun d => (kd_addr d, Ews, mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d))) KD ++ t_D T)
    by apply hcy5_p8_KT_D.
  split; [| apply hcy5_p8_KT_idx; auto].
  assert (Hlk: forall a sh E, In (a, sh, E) (t_D T') -> t_entry T' a = Some E).
  { intros a sh E Hin. unfold t_entry. rewrite (hcy5_p8_sfind_in _ a sh E Hnd' Hin). reflexivity. }
  exists (fun k => match t_entry T' k with Some E => e_peer E | None => nullval end),
         (fun k => match t_entry T' k with Some E => e_index E | None => Int.zero end).
  rewrite hcy5_p8_PS_addrs. replace (map ke_addr (map kd_kent KD)) with (map kd_addr KD)
    by (rewrite map_map; reflexivity).
  split.
  - rewrite HTD, HD. unfold hcy5_pool. cbn [map app].
    f_equal.
    + rewrite map_map. apply map_ext_in. intros d Hd. unfold hcy5_kentry.
      rewrite (Hlk (kd_addr d) Ews (mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d))); [reflexivity |].
      rewrite HTD. apply in_or_app; left.
      apply in_map_iff. exists d. auto.
    + apply map_ext_in. intros a Ha. unfold hcy5_hent.
      rewrite (Hlk (hs_addr a) Ews (mkEntry a IDX_HANDSHAKE (ix (hs_addr a)))); [reflexivity |].
      rewrite HTD, HD. apply in_or_app; right. unfold hcy5_pool. cbn [map app].
      apply in_map_iff. exists a. auto.
  - rewrite Forall_map. rewrite Forall_forall in HK |- *. intros d Hd. unfold Basics.compose.
    rewrite (Hlk (kd_addr d) Ews (mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d))).
    + cbn. apply (HK d Hd).
    + rewrite HTD. apply in_or_app; left. apply in_map_iff. exists d. auto.
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P8_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S7 x25519 xaead_enc gv L FR) hcy5_P8
    (overridePost (hcy5_S8 x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S7, hcy5_Delta, hcy5_R, hcy5_P8. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp. Intros Q nonce rr CK CM. Intros NS PS T np CL.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  assert_PROP (is_pointer_or_null (hcy5_head NS) /\ (hcy5_head NS = nullval -> NS = [])) as Hhd.
  { sep_apply (hcy5_p8_hnodes_head (hcy5_head NS) NS). entailer!. }
  destruct Hhd as [Hhp Hhn].
  forward.
  forward_call (gv, Tsh, l_ita L, T, hcy5_head NS, NS, nullval, PS, Int.one, S, hcy5_w0).
  { split.
    - destruct H0 as (HP & _). unfold peers_wf. eapply Forall_impl; [| exact HP].
      intros [[a sh] P] (-> & _). apply writable_Ews.
    - destruct H0 as (HP & Hpe & _).
      split; cycle 1.
      { eapply Forall_impl; [| exact HP]. intros [[a sh] P] (_ & _ & _ & _ & _ & Hs).
        eapply Forall_impl; [| exact Hs]. intros k [-> | []]. left; reflexivity. }
      unfold kents_owners_ok, hnodes_peers4 in *.
      destruct (eq_dec (hcy5_head NS) nullval) as [Hn | Hn].
      + specialize (Hhn Hn). subst NS. split; [reflexivity |]. rewrite <- Hpe. reflexivity.
      + split; [| split; [exact Hpe | reflexivity]]. intros ->. apply Hn. reflexivity. }
  Intros KD.
  forward.
  assert_PROP (itable_wf (kents_T T KD)) as Hwf. { unfold itable at 1. entailer!. }
  change (negb (Int.eq Int.one Int.zero)) with true.
  assert (HL: hcy5_lists_ok L (map ke_addr (map kd_kent KD)) NS (kents_PS true PS KD)).
  { rewrite map_map. apply hcy5_p8_PS_lists; exact H0. }
  assert (HN: hcy5_np_ok (hcy5_pubB x25519 R L) NS (kents_PS true PS KD) np) by (apply hcy5_p8_PS_np; exact H1).
  assert (HT: hcy5_T_ok (kents_PS true PS KD) (map kd_kent KD) (kents_T T KD)).
  { apply hcy5_p8_T_ok; auto. destruct Hwf as (_ & _ & Hd & _). exact Hd. }
  unfold hcy5_S8. Exists R (kents_S S KD) m c rp. Exists Q nonce rr CK CM.
  Exists NS (kents_PS true PS KD) (kents_T T KD) np CL. Exists (map kd_kent KD).
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars; cbn [app].
  rewrite hcy5_p8_PS_phead.
  replace (hcy5_khead (map kd_kent KD)) with (kents_head KD) by (destruct KD; reflexivity).
  entailer!.
Qed.

End Phase.
