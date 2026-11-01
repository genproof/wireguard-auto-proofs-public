(* An index table whose pool is one entry, as in the hs_ harnesses (each device's table holds its peer's
   handshake entry, hs_specs.v's hs_table): the table is its head pointer and that entry, whose list fields
   are given by the table's list.  The hs_ laws open the table this way to hand the entry to copy_peer and
   same_peer (hs_unchanged.h), and close it again. *)
Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require WgNoise.units.Noise.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Local Open Scope logic.

Section One.
#[local] Existing Instance Noise.CS.

Lemma hs_itable1 sht tab T a sh E :
  t_D T = [(a, sh, E)] ->
  itable sht tab T =
  !! itable_wf T && (data_at sht t_itab (hd nullval (t_L T)) tab * entry_at sh a E (succ_in (t_L T) a) (vin a (t_L T))).
Proof.
  intros HD. unfold itable. rewrite HD. simpl. rewrite sepcon_emp. reflexivity.
Qed.

(* the table of hs_table: no entry hashed, the entry's list fields NULL and false *)
Lemma hs_itable1_unhashed sht tab a sh E :
  itable sht tab (mkT [(a, sh, E)] []) =
  !! itable_wf (mkT [(a, sh, E)] []) && (data_at sht t_itab nullval tab * entry_at sh a E nullval false).
Proof.
  rewrite (hs_itable1 sht tab (mkT [(a, sh, E)] []) a sh E eq_refl). reflexivity.
Qed.

End One.
