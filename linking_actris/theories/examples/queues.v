From stdpp Require Import sorting.
From iris.base_logic.lib Require Import invariants token ghost_var.
From linking_actris Require Import atomic_array_queue.

Section queues.

Context `{!heapGS Σ, !queueG Σ, time_receiptG Σ, !tokenG Σ, !ghost_varG Σ loc}.

Definition prog_5 : expr :=
  let: "q" := new_queue #() in
  let: "d" := Fst "q" in
  let: "e" := Snd "q" in
  Fork (let: "q'" := new_queue #() in enqueue (Snd "q'") #42;; link_queue "e" (Fst "q'"));;
  dequeue "d".

(* The invariant for program 5 uses a ghost variable to allow the forked thread to
   update 'e' when linking. *)
Definition prog_5_inv (d : loc) γe : iProp Σ :=
  ∃ n e, is_queue d e (replicate n #42) ∗ ghost_var γe (1/2) e.

Lemma prog_5_spec :
  {{{ True }}} prog_5 {{{ RET #42; True }}}.
Proof.
  iMod (tr_ctx_alloc (nroot .@ "tr")) as (γ) "#Htr".
  iIntros (Φ) "_ HΦ". unfold prog_5.
  wp_apply (new_queue_spec with "[//]").
  iIntros (d e) "(Hq & Hd & He)"; wp_pures.
  iMod (ghost_var_alloc e) as (γe) "[Hγe Hγe']".
  iMod (inv_alloc (nroot .@ "q") _ (prog_5_inv d γe) with "[Hq Hγe']") as "#Hinv".
  { iNext. iExists 0, e. by iFrame. }
  wp_smart_apply (wp_fork with "[He Hγe]").
  - (* Forked thread *)
    iNext. iMod (tr_zero) as "Htr0".
    wp_apply (new_queue_spec with "[//]").
    iIntros (d' e') "(Hq' & Hd' & He')"; wp_pures.
    awp_apply (enqueue_spec with "Htr He'").
    iCombine "Hq' Htr0" as "H". iAaccIntro with "H".
    { (* Abort *) iIntros "[Hq' Htr0]". iModIntro. iFrame. }
    (* Commit *)

    iIntros "(Hq' & _) !> He'". wp_pures.
    awp_apply (link_queue_spec with "He Hd'").
    iInv (nroot .@ "q") as (n e'') "[>Hq >Hγe']".
    iDestruct (ghost_var_agree with "Hγe Hγe'") as %<-.
    iAaccIntro with "[Hq Hq']".
    { instantiate (1 := [tele_arg true; _; _; _; _]); simpl. iFrame. }

    { (* Abort *) iIntros "[Hq Hq']". iModIntro. iFrame. }

    (* Commit *)
    iMod (ghost_var_update with "[$Hγe $Hγe']") as "[Hγe Hγe']".
    iIntros "Hq !>". iSplitL; [|done].
    rewrite -replicate_S_end. iNext. iExists (S n), _. by iFrame.
  - (* Main thread *)
    wp_pures.
    awp_apply (dequeue_spec with "Hd").
    iInv (nroot .@ "q") as (n e') "[>Hq Hγe']".
    iAaccIntro with "Hq".
    { (* Abort *) iIntros "Hq". iModIntro. iFrame. }
    
    (* Commit *)
    iIntros (v vs) "(%Heq & _ & Hq) !>".
    destruct n as [|n]; first by eauto.
    rewrite replicate_S in Heq; simplify_eq.
    iSplitR "HΦ".
    + iNext. iExists _. by iFrame.
    + iIntros. by iApply "HΦ".
Qed.

Definition prog_6 : expr :=
  let: "q" := new_queue #() in
  let: "d" := Fst "q" in
  let: "e" := Snd "q" in
  Fork (enqueue "e" #42);;
  dequeue "d".

Definition prog_6_inv (d e : loc) : iProp Σ :=
  ∃ n, is_queue d e (replicate n #42).

Lemma prog_6_spec :
  {{{ True }}} prog_6 {{{ RET #42; True }}}.
Proof.
  iMod (tr_ctx_alloc (nroot .@ "tr")) as (γ) "#Htr".
  iIntros (Φ) "_ HΦ". unfold prog_6.
  wp_apply (new_queue_spec with "[//]").
  iIntros (d e) "(Hq & Hd & He)"; wp_pures.
  iMod (inv_alloc (nroot .@ "q") _ (prog_6_inv d e) with "[Hq]") as "#Hinv".
  { iNext. by iExists 0. }
  wp_smart_apply (wp_fork with "[He]").
  - (* Enqueue thread *)
    iNext. iMod (tr_zero) as "Htr0".
    awp_apply (enqueue_spec with "Htr He").
    iInv (nroot .@ "q") as (n) ">Hq".
    iCombine "Hq Htr0" as "H". iAaccIntro with "H".
    + (* Abort *)
      iIntros "[Hq Htr0]". iModIntro. iFrame.
    + (* Commit *)
      iIntros "(Hq & _) !>".
      rewrite -replicate_S_end. eauto with iFrame.
  - (* Dequeue thread *)
    wp_pures.
    awp_apply (dequeue_spec with "Hd").
    iInv (nroot .@ "q") as (n) ">Hq".
    iAaccIntro with "Hq".
    + (* Abort *)
      iIntros "Hq". iModIntro. iFrame.
    + (* Commit *)
      iIntros (v vs) "(%Heq & _ & Hq) !>".
      destruct n as [|n]; first by eauto.
      rewrite replicate_S in Heq; simplify_eq.
      iFrame; iIntros.
      by iApply "HΦ".
Qed.

Definition prog_8 : expr :=
  let: "q1" := new_queue #() in
  let: "d1" := Fst "q1" in
  let: "e1" := Snd "q1" in
  let: "q2" := new_queue #() in
  let: "d2" := Fst "q2" in
  let: "e2" := Snd "q2" in
  Fork (link_queue "e1" "d2");;
  link_queue "e2" "d1".

(* The invariant for 8 uses unique tokens (token γ) with the property that only one token
   exists for each ghost name. *)
Definition prog_8_inv (γ1 γ2 : gname) (d1 e1 d2 e2 : loc) : iProp Σ :=
  (is_queue d1 e1 [] ∗ is_queue d2 e2 []) ∨
  (token γ1 ∗ is_queue d1 e2 []) ∨
  (token γ2 ∗ is_queue d2 e1 []) ∨
  (token γ1 ∗ token γ2)%I.

Lemma prog_8_spec :
  {{{ True }}} prog_8 {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "_ HΦ". unfold prog_8.
  wp_apply (new_queue_spec with "[//]").
  iIntros (d1 e1) "(Hq1 & Hd1 & He1)"; wp_pures.
  wp_apply (new_queue_spec with "[//]").
  iIntros (d2 e2) "(Hq2 & Hd2 & He2)"; wp_pures.

  iMod (token_alloc) as (γ1) "Hγ1".
  iMod (token_alloc) as (γ2) "Hγ2".
  iMod (inv_alloc (nroot .@ "q") _ (prog_8_inv γ1 γ2 d1 e1 d2 e2) with "[Hq1 Hq2]") as "#Hinv".
  { iNext. iLeft. by iFrame. }
  
  wp_smart_apply (wp_fork with "[He1 Hd2 Hγ1]").
  - (* Forked thread *)
    iNext.
    awp_apply (link_queue_spec with "He1 Hd2").
    iInv (nroot .@ "q") as "[[>Hq1 >Hq2] | [[Hγ1' >Hq2] | [[Hγ2 >Hq1] | [Hγ1' Hγ2]]]]".
    + iAaccIntro with "[Hq1 Hq2]".
      { instantiate (1 := [tele_arg true; _; _; _; _]); simpl. iFrame. }
      * (* Abort *)
        iIntros "[Hq1 Hq2] !>". iFrame.
        iNext. iLeft. by iFrame.
      * (* Commit *)
        iIntros "Hq !>". iSplitL; [|done].
        iNext. iRight. iLeft. by iFrame.
    + iMod (token_exclusive with "Hγ1 Hγ1'") as %[].
    + iAaccIntro with "[Hq1]".
      { instantiate (1 := [tele_arg false; _; _; _; _]); simpl. eauto with iFrame. }
      * (* Abort *)
        iIntros "[Hq _] !>". iFrame.
        iNext. iRight; iRight; iLeft. by iFrame.
      * (* Commit *)
        iIntros "Hq !>". iSplitL; [|done].
        iNext. do 3 iRight. by iFrame.
    + iMod (token_exclusive with "Hγ1 Hγ1'") as %[].
  - (* Main thred *)
    wp_pures; awp_apply (link_queue_spec with "He2 Hd1").
    iInv (nroot .@ "q") as "[[>Hq1 >Hq2] | [[Hγ1 >Hq2] | [[Hγ2' >Hq1] | [Hγ1 Hγ2']]]]".
    + iAaccIntro with "[Hq1 Hq2]".
      { instantiate (1 := [tele_arg true; _; _; _; _]); simpl. iFrame. }
      * (* Abort *)
        iIntros "[Hq1 Hq2] !>". iFrame.
        iNext. iLeft. by iFrame.
      * (* Commit *)
        iIntros "Hq !>". iSplitR "HΦ"; [|by iApply "HΦ"].
        iNext. iRight. iRight. iLeft. by iFrame.
    + iAaccIntro with "[Hq2]".
      { instantiate (1 := [tele_arg false; _; _; _; _]); simpl. eauto with iFrame. }
      * (* Abort *)
        iIntros "[Hq _] !>". iFrame.
        iNext. iRight; iLeft. by iFrame.
      * (* Commit *)
        iIntros "Hq !>". iSplitR "HΦ"; [|by iApply "HΦ"].
        iNext. do 3 iRight. by iFrame.
    + iMod (token_exclusive with "Hγ2 Hγ2'") as %[].
    + iMod (token_exclusive with "Hγ2 Hγ2'") as %[].
Qed.

End queues.
