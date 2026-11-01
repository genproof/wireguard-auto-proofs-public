(* create_initiation, stage F (ci_B12, ci_B13): dst->sender_index = wg_index_hashtable_insert(handshake->entry.peer->device->index_hashtable, &handshake->entry); handshake->state = HANDSHAKE_CREATED_INITIATION; ret = true;
   See
   prot4_ci_defs.v for ci_A (the state) and prot4_ci_sA.v for a proved example
   (proof recipe: destruct R; simplify_func_tycontext; unfold ci_A, ci_B..; abbreviate_semax; forward ...). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require Import WgNoise.proof.protocol4.prot4_ci_defs.

Section Helpers.
#[local] Existing Instance Noise.CS.

Lemma prot4_ci_sF_sfind_in: forall (l: list (val * share * entry)) a sh E,
  sfind l a = Some (sh, E) -> In (a, sh, E) l.
Proof.
induction l as [|[[x shx] Ex] l IH]; simpl; intros. discriminate.
destruct (EqDec_val x a). { subst x. inv H. now left. } { right; auto. }
Qed.

Lemma prot4_ci_sF_in_saddrs: forall T p, hs_in_pool T p -> In (hs_addr p) (saddrs (t_D T)).
Proof.
intros T p [E [HE _]]. unfold t_entry in HE.
destruct (sfind (t_D T) (hs_addr p)) as [[sh E']|] eqn:HS; [|discriminate].
apply prot4_ci_sF_sfind_in in HS. unfold saddrs. apply in_map_iff. exists (hs_addr p, sh, E'); auto.
Qed.

Lemma prot4_ci_sF_open: forall sht tab T p,
  hs_in_pool T p -> field_compatible t_hs [] (hs_addr p) ->
  itable sht tab T |--
  EX she: share, EX E: entry, EX nx: val, EX hd: bool,
    !! (readable_share she /\ e_peer E = p) &&
    (field_at she t_hs (DOT I._entry) (entry_val E nx hd) (hs_addr p) *
     (field_at she t_hs (DOT I._entry) (entry_val E nx hd) (hs_addr p) -* itable sht tab T)).
Proof.
intros sht tab T p [E [HE HP]] FC. unfold t_entry in HE.
destruct (sfind (t_D T) (hs_addr p)) as [[sh E']|] eqn:HS; [|discriminate]. injection HE as ->.
apply prot4_ci_sF_sfind_in in HS.
destruct (in_split _ _ HS) as [l1 [l2 Hl]].
unfold itable. Intros.
assert (WS: writable_share sh).
{ destruct H as [_ [_ [_ HF]]]. rewrite Forall_forall in HF. apply (HF _ HS). }
Exists sh E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T)).
rewrite prop_true_andp by auto.
assert (EQ: field_at sh t_hs (DOT I._entry) (entry_val E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p)
          = entry_at sh (hs_addr p) E (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))).
{ unfold entry_at. rewrite field_at_data_at. f_equal.
  rewrite field_address_offset by auto with field_compatible. simpl.
  apply isptr_offset_val_zero. apply FC. }
rewrite EQ. rewrite Hl at 1. rewrite VST.msl.iter_sepcon.iter_sepcon_app. simpl.
set (X := entry_at _ _ _ _ _).
match goal with |- sepcon ?A (sepcon ?B (sepcon X ?C)) |-- _ =>
  apply derives_trans with (sepcon X (sepcon A (sepcon B C))); [cancel|] end.
apply sepcon_derives; auto.
rewrite <- wand_sepcon_adjoint.
rewrite prop_true_andp by auto.
rewrite Hl, VST.msl.iter_sepcon.iter_sepcon_app. simpl. unfold X. cancel.
Qed.

End Helpers.

Section CI.
Context {Espec: OracleKind}.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
#[local] Existing Instance Noise.CS.

Lemma prot4_ci_sF:
  forall gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
         ret mt ms me mes met hst he hh hc kv tv S w T (Qc: environ -> mpred) (R: ret_assert),
  writable_share shm -> writable_share shp -> readable_share shd -> writable_share sht ->
  hs_in_pool T p ->
  semax (ci_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec CSw)
    (ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       True ret mt ms me mes met hst he hh hc kv tv S w T)
    (Ssequence ci_B12 ci_B13)
    (overridePost
      (EX idx: int,
       ci_A gv kc shm m shp p shd wg sid has pub tab sht rs ss kp tp FR
       (t_fresh T (hs_addr p) idx) (Vint Int.one) mt (Vint idx) me mes met (Vint HS_CREATED_INITIATION) he hh hc kv tv
         (shim_u32 S idx) w (t_insert T (hs_addr p) idx))
      (loop1_ret_assert Qc R)).
Proof.
intros until R. intros SHm SHp SHd SHt HP.
unfold ci_Delta. simplify_func_tycontext. unfold ci_A, ci_B12, ci_B13. abbreviate_semax.
destruct R as [Rn Rb Rc Rr].
assert_PROP (field_compatible t_hs [] (hs_addr p)) as FC.
{ entailer!. clear - H11. destruct H11 as (A&B&C&D&_); repeat split; auto. }
assert_PROP (isptr tab) as Ptab. { unfold itable. Intros. entailer!. }
(* t'5 = handshake->entry.peer: the entry lives in the table's pool *)
sep_apply (prot4_ci_sF_open sht tab T p HP FC). Intros she E nx hd. rename H into RS, H0 into HPE.
unfold entry_val. forward.
sep_apply modus_ponens_wand. rewrite HPE.
forward. forward.
assert (HIn := prot4_ci_sF_in_saddrs T p HP).
forward_call (gv, S, w, sht, tab, T, hs_addr p, @None (share * entry)).
{ change (raw_rep (hs_addr p) None) with emp. rewrite emp_sepcon. cancel. }
change (raw_add T (hs_addr p) None) with T. Intros idx.
forward. forward. forward.
Exists idx. entailer!.
Qed.
End CI.
