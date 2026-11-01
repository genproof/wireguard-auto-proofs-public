(* The bodies of the shim's index table functions (index_in_use, remove, insert, replace) against their v5
   specifications (prot_specs5.v: v4's, unchanged), in the context Gprot5 (prot_prog5.v).  The scripts are
   those of prot4_shim_table1.v and prot4_shim_table2_replace.v, re-run because a body's function context is
   part of its statement; their lemmas on the table representation are reused. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
(* raw_ok, raw_rep: the index table's raw entries, as in v4 (the v5 names below take precedence) *)
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_cs.
Require Import WgNoise.proof.protocol4.prot4_shim_table1.
Require Import WgNoise.proof.protocol4.prot4_shim_table2_replace.
Local Open Scope logic.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Lemma prot5_shim_body_in_use :
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_shim_index_in_use wg_shim_index_in_use_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  assert_PROP (is_pointer_or_null (hd nullval (t_L T))).
  { sep_apply (prot4_shim_table1_hd sht tab T [] (t_L T) eq_refl). entailer!. }
  rewrite prot4_shim_table1_open0 by auto. Intros.
  unfold Sfor. forward. gather_SEP 0 1. rewrite <- prot4_shim_table1_open0 by auto.
  forward_loop (EX L1: list val, EX L2: list val,
    PROP (t_L T = L1 ++ L2; ~ In idx (t_indices T L1))
    LOCAL (temp code._e (hd nullval L2); temp code._table tab; temp code._index (Vint idx))
    SEP (itable sht tab T))
  continue: (EX L1: list val, EX a: val, EX L2: list val,
    PROP (t_L T = L1 ++ a :: L2; ~ In idx (t_indices T (L1 ++ [a])))
    LOCAL (temp code._e a; temp code._table tab; temp code._index (Vint idx))
    SEP (itable sht tab T))
  break: (PROP (~ In idx (t_indices T (t_L T)))
    LOCAL (temp code._table tab; temp code._index (Vint idx))
    SEP (itable sht tab T)).
 { Exists (@nil val) (t_L T). entailer!. }
  { Intros L1 L2. rename H0 into HL, H1 into HI.
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (prot4_shim_table1_hd sht tab T L1 L2 HL). entailer!. }
    forward_if.
    { apply prot4_shim_table1_tc_hd with L1; auto. }
    { destruct L2 as [|a L2]; [simpl in H0; contradiction|]. simpl in H0 |- *.
      assert (Ha: In a (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
      destruct (prot4_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
      assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
      rewrite (prot4_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
      unfold entry_val. forward. forward.
      gather_SEP 0 1 2. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))). rewrite <- (prot4_shim_table1_open sht tab T a sh E) by auto.
      forward_if.
      - forward. rewrite prot4_shim_table1_inb_true; [entailer!|].
        eapply prot4_shim_table1_ind_in; eauto.
      - forward. Exists L1 a L2. entailer!. eapply prot4_shim_table1_ind_snoc; eauto. }
    { destruct L2 as [|a L2].
      - forward. entailer!. rewrite app_nil_r in HL. rewrite HL in *. auto.
      - simpl in H0. subst a.
        assert_PROP (isptr nullval).
        { sep_apply (prot4_shim_table1_isptr sht tab T nullval ltac:(eapply prot4_shim_table1_inL; eauto)).
          entailer!. }
        contradiction. }
  }
  { Intros L1 a L2. rename H0 into HL, H1 into HI.
    assert (Ha: In a (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
    destruct (prot4_shim_table1_sfind_in _ _ Ha) as (sh & E & HE).
    assert (writable_share sh) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
    assert (HS: succ_in (t_L T) a = hd nullval L2).
    { rewrite HL. apply prot4_shim_table1_succ. rewrite <- HL. apply HW. }
    assert_PROP (is_pointer_or_null (hd nullval L2)) as HP.
    { sep_apply (prot4_shim_table1_hd sht tab T (L1 ++ [a]) L2 ltac:(rewrite <- app_assoc; auto)). entailer!. }
    rewrite (prot4_shim_table1_open sht tab T a sh E) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. rewrite HS. forward.
    gather_SEP 0 1 2. rewrite <- HS. fold (entry_val E (succ_in (t_L T) a) (vin a (t_L T))).
    rewrite <- (prot4_shim_table1_open sht tab T a sh E) by auto.
    Exists (L1 ++ [a]) L2. entailer!.
    rewrite <- app_assoc; auto. }
  forward. rewrite prot4_shim_table1_inb_false by auto. entailer!.
Qed.

Lemma prot5_shim_body_remove :
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_remove wg_index_hashtable_remove_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  destruct raw as [[shr Er]|]; cbn [raw_ok raw_rep] in *.
  { destruct H as [Hshr Hnot]. unfold raw_entry. rewrite prot4_shim_table1_entry_S.
    forward. forward_if.
    - forward. rewrite <- prot4_shim_table1_entry_S. entailer!.
    - match goal with Hc: Int.zero <> Int.zero |- _ => contradiction Hc; auto end. }
  destruct (prot4_shim_table1_sfind_in _ _ H) as (she & Ee & HEe).
  assert (writable_share she) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
  rewrite (prot4_shim_table1_open sht tab T e she Ee) by auto. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Shim.CS t_itab [] tab) as Hfct by entailer!.
  unfold entry_val. forward.
  { entailer!. destruct (vin e (t_L T)); simpl; auto. }
  gather_SEP 0 1 2. fold (entry_val Ee (succ_in (t_L T) e) (vin e (t_L T))).
  rewrite <- (prot4_shim_table1_open sht tab T e she Ee) by auto.
  destruct (vin e (t_L T)) eqn:Hvin.
  2: { forward_if.
       - forward. entailer!.
         assert (HT: t_remove T e = T).
         { destruct T as [D L]. unfold t_remove; simpl in *. rewrite prot4_shim_table1_vremove_notin; auto.
           intros Hin. apply prot4_shim_table1_vin_iff in Hin. congruence. }
         rewrite HT. auto.
       - match goal with Hc: Int.zero <> Int.zero |- _ => contradiction Hc; auto end. }
  forward_if.
  { match goal with Hc: Int.one = Int.zero |- _ => inv Hc end. }
  apply prot4_shim_table1_vin_iff in Hvin.
  unfold Sfor. forward. forward. { entailer!. destruct Hfct; auto. }
  forward_loop (EX L1: list val, EX L2: list val,
     PROP (t_L T = L1 ++ L2; In e L2)
     LOCAL (temp code._link (prot4_shim_table1_link tab L1); temp code._table tab; temp code._entry e)
     SEP (itable sht tab T))
  continue: (EX L1: list val, EX p: val, EX L2: list val,
     PROP (t_L T = L1 ++ p :: L2; In e L2)
     LOCAL (temp code._link (prot4_shim_table1_link tab L1); temp code._table tab; temp code._entry e)
     SEP (itable sht tab T))
  break: (EX L1: list val, EX L2: list val, EX shl: share,
     PROP (t_L T = L1 ++ e :: L2; writable_share shl)
     LOCAL (temp code._table tab; temp code._entry e)
     SEP (@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot4_shim_table1_link tab L1);
          @data_at Shim.CS she t_entry_s (entry_val Ee (hd nullval L2) true) e;
          (@data_at Shim.CS shl (tptr t_entry_s) (hd nullval L2) (prot4_shim_table1_link tab L1) *
           @data_at Shim.CS she t_entry_s (entry_val Ee nullval false) e) -* itable sht tab (t_remove T e))).
  { Exists (@nil val) (t_L T). entailer!.
    unfold prot4_shim_table1_link; simpl. destruct Hfct as [Hp _]. destruct tab; try contradiction.
    simpl. rewrite Ptrofs.add_zero. reflexivity. }
  { Intros L1 L2. rename H2 into HL, H3 into HeL2.
    destruct L2 as [|p L2]; [contradiction|]. change (hd nullval (p :: L2)) with p.
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
    assert_PROP (isptr p) as Hpp by (sep_apply (prot4_shim_table1_isptr sht tab T p Hp); entailer!).
    sep_apply (prot4_shim_table1_link_rd sht tab T L1 (p :: L2) SH HW HL). Intros shl.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { apply (prot4_shim_table1_tc_hd sht tab T L1 (p :: L2)); auto. }
    2: { subst p. contradiction. }
    forward.
    sep_apply (prot4_shim_table1_link_rd sht tab T L1 (p :: L2) SH HW HL). Intros shl'.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { entailer!. apply denote_tc_test_eq_split; apply prot4_shim_table1_valid; auto. }
    - subst p.
      assert_PROP (is_pointer_or_null (hd nullval L2)) as HP2
        by (sep_apply (prot4_shim_table1_hd sht tab T (L1 ++ [e]) L2 ltac:(rewrite <- app_assoc; auto)); entailer!).
      sep_apply (prot4_shim_table1_link_wr sht tab T L1 e L2 she Ee SH HW HL HEe). Intros shw.
      unfold entry_val. forward. forward. forward.
      Exists L1 L2 shw. unfold entry_val. entailer!.
    - forward. Exists L1 p L2. entailer!. destruct HeL2; [congruence|auto]. }
  { Intros L1 p L2. rename H2 into HL, H3 into HeL2.
    assert (Hp: In p (saddrs (t_D T))) by (eapply prot4_shim_table1_inL; eauto).
    assert_PROP (@field_compatible Shim.CS t_entry_s [] p) as Hfp
      by (sep_apply (prot4_shim_table1_fc sht tab T p Hp); entailer!).
    sep_apply (prot4_shim_table1_link_rd sht tab T L1 (p :: L2) SH HW HL). Intros shl.
    change (hd nullval (p :: L2)) with p.
    assert (Hpp: isptr p) by (destruct Hfp; auto).
    forward. sep_apply modus_ponens_wand.
    forward.
    Exists (L1 ++ [p]) L2. entailer!.
    split; [rewrite <- app_assoc; auto|]. rewrite prot4_shim_table1_link_snoc.
    rewrite field_compatible_field_address
      by (apply field_compatible_cons; simpl; split; auto; right; left; reflexivity).
    reflexivity. }
  Intros L1 L2 shl.
  unfold entry_val. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  change (Vint Int.zero) with (Val.of_bool false).
  gather_SEP 0 1. entailer!. apply modus_ponens_wand.
Qed.

Lemma prot5_shim_body_insert :
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_insert wg_index_hashtable_insert_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  forward_call (sht, tab, T, e, raw).
  destruct (prot4_shim_table1_ins_start sht tab T e raw H HW) as (she & Ee & v0 & HW0 & HE0 & Hshe & Heq).
  gather_SEP 0 1. rewrite Heq. clear Heq. repeat flatten_sepcon_in_SEP.
  set (T0 := raw_add T e raw) in *. clearbody T0.
  forward_loop (EX v: val, EX S': shim,
      PROP (forall n, shim_u32 S' n = shim_u32 S n)
      LOCAL (temp code._table tab; temp code._entry e; gvars gv)
      SEP (@data_at Shim.CS sht t_itab (hd nullval (vremove e (t_L T0))) tab;
           @data_at Shim.CS she t_entry_s (e_peer Ee, (nullval, (Val.of_bool false, (Vint (e_type Ee), v)))) e;
           iter_sepcon (pool_item_rep (vremove e (t_L T0))) (sdel (t_D T0) e);
           shim_state4 gv S' w))
    continue: (EX n: int,
      PROP ()
      LOCAL (temp code._table tab; temp code._entry e; gvars gv)
      SEP (itable sht tab (prot4_shim_table1_Ti T0 e Ee n); shim_state4 gv (shim_u32 S n) w))
    break: (EX n: int,
      PROP (int_inb n (t_indices (prot4_shim_table1_Ti T0 e Ee n) (vremove e (t_L T0))) = false)
      LOCAL (temp code._table tab; temp code._entry e; gvars gv)
      SEP (itable sht tab (prot4_shim_table1_Ti T0 e Ee n); shim_state4 gv (shim_u32 S n) w)).
  - Exists v0 S. entailer!.
  - Intros v S'. match goal with Hx: forall n, shim_u32 _ n = _ |- _ => rename Hx into HS' end.
    forward_call (gv, S', w). Intros n.
    forward.
    Exists n. rewrite HS'. rewrite (prot4_shim_table1_Ti_open sht tab T0 e she Ee n) by auto.
    unfold entry_val; cbn [e_peer e_type e_index]. entailer!.
  - Intros n.
    rewrite (prot4_shim_table1_Ti_open sht tab T0 e she Ee n) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. forward.
    gather_SEP 0 1 2. fold (entry_val (mkEntry (e_peer Ee) (e_type Ee) n) nullval false).
    rewrite <- (prot4_shim_table1_Ti_open sht tab T0 e she Ee n) by auto.
    forward_call (sht, tab, prot4_shim_table1_Ti T0 e Ee n, n).
    destruct (int_inb n (t_indices (prot4_shim_table1_Ti T0 e Ee n) (t_L (prot4_shim_table1_Ti T0 e Ee n)))) eqn:Hb.
    + forward_if; [|discriminate].
      forward. Exists (Vint n) (shim_u32 S n). entailer!.
      rewrite (prot4_shim_table1_Ti_open sht tab T0 e she Ee n) by auto. unfold entry_val; cbn [e_peer e_type e_index].
      entailer!.
    + forward_if; [discriminate|].
      forward. Exists n. entailer!.
  - Intros n. match goal with Hx: int_inb _ _ = false |- _ => rename Hx into Hb end.
    assert_PROP (is_pointer_or_null (hd nullval (vremove e (t_L T0)))) as Hhd
      by (sep_apply (prot4_shim_table1_hd sht tab (prot4_shim_table1_Ti T0 e Ee n) [] (vremove e (t_L T0)) eq_refl);
          entailer!).
    rewrite (prot4_shim_table1_Ti_open sht tab T0 e she Ee n) by auto. repeat flatten_sepcon_in_SEP.
    unfold entry_val. cbn [e_peer e_type e_index].
    forward. forward. forward. forward. forward. forward.
    Exists n. apply andp_right.
    { apply prop_right. split; auto. unfold t_fresh.
      rewrite <- (prot4_shim_table1_Ti_indices T0 e Ee n). intros Hin.
      rewrite prot4_shim_table1_inb_true in Hb by auto. discriminate. }
    eapply derives_trans; [|apply sepcon_derives;
      [apply (prot4_shim_table1_ins_close sht tab T0 e she Ee n HW0 HE0) | apply derives_refl]].
    unfold entry_val; cbn [e_peer e_type e_index]. change (Vint Int.one) with (Val.of_bool true). cancel.
Qed.

Lemma prot5_shim_body_replace :
  @semax_body (QPvarspecs Shim.qp) (Gprot5 x25519 aead_enc aead_dec CSw Shim.CS) Shim.CS
      WgNoise.shim.code.f_wg_index_hashtable_replace wg_index_hashtable_replace_spec.
Proof.
  start_function.
  assert_PROP (itable_wf T) as HW by (unfold itable; entailer!).
  rename H into Ho, H0 into Hn, H1 into Hon, H2 into HnL.
  destruct (prot4_shim_table1_sfind_in _ _ Ho) as (sho & Eo & HEo).
  destruct (prot4_shim_table1_sfind_in _ _ Hn) as (shn & En & HEn).
  assert (writable_share sho) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
  assert (writable_share shn) by (destruct HW as (_ & _ & _ & HF); eapply prot4_shim_table1_sfind_wr; eauto).
  assert (Hsn: succ_in (t_L T) new = nullval) by (apply prot4_shim_table1_succ_notin; auto).
  assert (Hvn: vin new (t_L T) = false).
  { apply Bool.not_true_is_false. rewrite prot4_shim_table1_vin_iff. auto. }
  rewrite (prot4_shim_table1_open sht tab T old sho Eo) by auto. repeat flatten_sepcon_in_SEP.
  unfold entry_val. forward.
  { entailer!. destruct (vin old (t_L T)); simpl; auto. }
  gather_SEP 0 1 2. fold (entry_val Eo (succ_in (t_L T) old) (vin old (t_L T))).
  rewrite <- (prot4_shim_table1_open sht tab T old sho Eo) by auto.
  destruct (vin old (t_L T)) eqn:Hvin.
  2: { forward_if.
       - forward. unfold t_replace. rewrite Hvin. entailer!. apply derives_refl.
       - match goal with Hc: Int.zero <> Int.zero |- _ => contradiction Hc; auto end. }
  forward_if.
  { match goal with Hc: Int.one = Int.zero |- _ => inv Hc end. }
  apply prot4_shim_table1_vin_iff in Hvin.
  assert (Hvin' := Hvin). apply in_split in Hvin'. destruct Hvin' as (A0 & B0 & HL0).
  rewrite (prot4_shim_table1_open sht tab T old sho Eo) by auto. repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Shim.CS t_itab [] tab) as Hfct by entailer!.
  unfold entry_val. forward. forward.
  gather_SEP 0 1 2. fold (entry_val Eo (succ_in (t_L T) old) (vin old (t_L T))).
  rewrite <- (prot4_shim_table1_open sht tab T old sho Eo) by auto.
  rewrite (prot4_shim_table1_open sht tab T new shn En) by auto. repeat flatten_sepcon_in_SEP.
  unfold entry_val. forward.
  change (@data_at Shim.CS shn t_entry_s
    (e_peer En, (succ_in (t_L T) new, (Val.of_bool (vin new (t_L T)), (Vint (e_type En), Vint (e_index Eo))))) new)
    with (@data_at Shim.CS shn t_entry_s (entry_val (mkEntry (e_peer En) (e_type En) (e_index Eo)) (succ_in (t_L T) new) (vin new (t_L T))) new).
  gather_SEP 0 1 2.
  rewrite <- (prot4_shim_table2_T1_open sht tab T new shn En (e_index Eo)) by auto.
  set (T1 := prot4_shim_table2_T1 T new En (e_index Eo)).
  set (En1 := mkEntry (e_peer En) (e_type En) (e_index Eo)).
  assert (HW1: itable_wf T1) by (apply prot4_shim_table2_T1_wf; auto).
  assert (HEo1: sfind (t_D T1) old = Some (sho, Eo)) by (unfold T1; rewrite prot4_shim_table2_T1_sfind; auto).
  assert (HEn1: sfind (t_D T1) new = Some (shn, En1)) by (unfold T1; eapply prot4_shim_table2_T1_sfind_n; eauto).
  assert (Ho1: In old (saddrs (t_D T1))) by (eapply prot4_shim_table1_saddrs_in, prot4_shim_table1_sfind_In; eauto).
  forward.
  { entailer!. destruct Hfct; auto. }
  forward_loop (EX L1: list val, EX L2: list val,
     PROP (t_L T = L1 ++ L2; In old L2)
     LOCAL (temp code._link (prot4_shim_table1_link tab L1); temp code._table tab; temp code._old old;
            temp code._new new)
     SEP (itable sht tab T1))
  continue: (EX L1: list val, EX p: val, EX L2: list val,
     PROP (t_L T = L1 ++ p :: L2; In old L2)
     LOCAL (temp code._link (prot4_shim_table1_link tab L1); temp code._table tab; temp code._old old;
            temp code._new new)
     SEP (itable sht tab T1))
  break: (EX L1: list val, EX L2: list val, EX shl: share,
     PROP (t_L T = L1 ++ old :: L2; writable_share shl; is_pointer_or_null (hd nullval L2))
     LOCAL (temp code._table tab; temp code._old old; temp code._new new)
     SEP (@data_at Shim.CS shl (tptr t_entry_s) new (prot4_shim_table1_link tab L1);
          @data_at Shim.CS sho t_entry_s (entry_val Eo (hd nullval L2) true) old;
          @data_at Shim.CS shn t_entry_s (entry_val En1 nullval false) new;
          (@data_at Shim.CS shl (tptr t_entry_s) new (prot4_shim_table1_link tab L1) *
           @data_at Shim.CS sho t_entry_s (entry_val Eo nullval false) old *
           @data_at Shim.CS shn t_entry_s (entry_val En1 (hd nullval L2) true) new) -*
          itable sht tab (mkT (t_D T1) (L1 ++ new :: L2)))).
  { Exists (@nil val) (t_L T). entailer!.
    unfold prot4_shim_table1_link; simpl. destruct Hfct as [Hp _]. destruct tab; try contradiction.
    simpl. rewrite Ptrofs.add_zero. reflexivity. }
  { Intros L1 L2. rename H2 into HL, H3 into HoL2.
    destruct L2 as [|p L2]; [contradiction|]. change (hd nullval (p :: L2)) with p.
    assert (Hp: In p (saddrs (t_D T1))) by (eapply prot4_shim_table1_inL; eauto).
    assert_PROP (isptr p) as Hpp by (sep_apply (prot4_shim_table1_isptr sht tab T1 p Hp); entailer!).
    sep_apply (prot4_shim_table1_link_rd sht tab T1 L1 (p :: L2) SH HW1 HL). Intros shl.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { apply (prot4_shim_table1_tc_hd sht tab T1 L1 (p :: L2)); auto. }
    2: { subst p. contradiction. }
    forward.
    sep_apply (prot4_shim_table1_link_rd sht tab T1 L1 (p :: L2) SH HW1 HL). Intros shl'.
    forward. sep_apply modus_ponens_wand.
    forward_if.
    { entailer!. apply denote_tc_test_eq_split; apply prot4_shim_table1_valid; auto. }
    - subst p.
      assert_PROP (is_pointer_or_null (hd nullval L2)) as HP2
        by (sep_apply (prot4_shim_table1_hd sht tab T1 (L1 ++ [old]) L2 ltac:(rewrite <- app_assoc; auto)); entailer!).
      sep_apply (prot4_shim_table2_link_rep sht tab T1 L1 old L2 sho Eo new shn En1 SH HW1 HL HnL HEo1 HEn1 Hon).
      Intros shw.
      forward. forward.
      Exists L1 L2 shw. entailer!.
    - forward. Exists L1 p L2. entailer!. destruct HoL2; [congruence|auto]. }
  { Intros L1 p L2. rename H2 into HL, H3 into HoL2.
    assert (Hp: In p (saddrs (t_D T1))) by (eapply prot4_shim_table1_inL; eauto).
    assert_PROP (@field_compatible Shim.CS t_entry_s [] p) as Hfp
      by (sep_apply (prot4_shim_table1_fc sht tab T1 p Hp); entailer!).
    sep_apply (prot4_shim_table1_link_rd sht tab T1 L1 (p :: L2) SH HW1 HL). Intros shl.
    change (hd nullval (p :: L2)) with p.
    assert (Hpp: isptr p) by (destruct Hfp; auto).
    forward. sep_apply modus_ponens_wand.
    forward.
    Exists (L1 ++ [p]) L2. entailer!.
    split; [rewrite <- app_assoc; auto|]. rewrite prot4_shim_table1_link_snoc.
    rewrite field_compatible_field_address
      by (apply field_compatible_cons; simpl; split; auto; right; left; reflexivity).
    reflexivity. }
  Intros L1 L2 shl. rename H2 into HL.
  assert (HN: NoDup (L1 ++ old :: L2)) by (rewrite <- HL; apply HW).
  assert (HoL1: ~ In old L1) by (intro; apply (NoDup_remove_2 _ _ _ HN); apply in_or_app; auto).
  unfold entry_val. forward. forward. forward. forward. forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  change (Vint Int.zero) with (Val.of_bool false).
  change (Vint Int.one) with (Val.of_bool true).
  gather_SEP 0 1 2 3. rewrite <- !sepcon_assoc.
  forward.
  rewrite (prot4_shim_table2_result T old new sho Eo shn En L1 L2 HEo HEn HL HoL1).
  entailer!. apply modus_ponens_wand.
Qed.

End Bodies.
