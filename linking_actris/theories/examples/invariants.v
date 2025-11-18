From iris.heap_lang Require Import lib.assert.
From iris.program_logic Require Export atomic.
From iris.base_logic.lib Require Import invariants token ghost_var.
From linking_actris Require Import proofmode.

Section invariants.

Context `{!heapGS Σ}.

Definition incr : val :=
  rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" ("n" + #1) then #()
    else "incr" "l".

Definition prog_7 : expr :=
  let: "l" := ref #40 in
  Fork (incr "l");; Fork (incr "l");;
  !"l".

Definition prog_7_inv (l : loc) : iProp Σ :=
  ∃ (n : nat), ⌜n ≥ 40⌝ ∗ l ↦ #n.

Lemma incr_spec_invariant N l :
  {{{ inv N (prog_7_inv l) }}}
    incr #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  unfold prog_7_inv.
  iLöb as "IH". wp_rec.
  wp_pures. wp_bind (! _ : expr).
  iInv "Hinv" as (n) ">(%Hn & Hl)".
  wp_load. iModIntro.
  iSplitL "Hl"; first eauto with iFrame.
  wp_pures. wp_bind (CmpXchg _ _ _ : expr).
  iInv "Hinv" as (n') ">(%Hn' & Hl)".
  destruct (decide (n = n')).
  - simplify_eq.
    wp_cmpxchg_suc.
    iModIntro. iSplitL "Hl".
    + iNext. iExists (n' + 1).
      rewrite Nat.add_1_r.
      replace (n' + 1)%Z with (Z.of_nat (S n')) by lia.
      iFrame. iPureIntro. lia.
    + wp_pures. iModIntro. by iApply "HΦ".
  - wp_cmpxchg_fail; first naive_solver.
    iModIntro.
    iSplitL "Hl"; first eauto with iFrame.
    wp_pures. by wp_apply "IH".
Qed.

Lemma prog_7_spec (N : namespace) :
  {{{ True }}} prog_7 {{{ (n : nat), RET #n; ⌜n ≥ 40⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  unfold prog_7.
  wp_alloc l as "Hl". wp_pures.
  iMod (inv_alloc N _ (prog_7_inv l) with "[Hl]") as "#Hinv".
  { iNext. iExists 40. iFrame. iPureIntro. lia. }
  wp_smart_apply (wp_fork with "[]").
  { iNext. iApply (incr_spec_invariant with "[$]"). iIntros "!> $". }
  wp_smart_apply (wp_fork with "[]").
  { iNext. iApply (incr_spec_invariant with "[$]"). iIntros "!> $". }
  wp_pures.
  iInv "Hinv" as (n) ">(%Hn & Hl)".
  wp_load. iModIntro.
  iSplitL "Hl"; first (unfold prog_7_inv; eauto with iFrame).
  by iApply "HΦ".
Qed.

Lemma incr_spec_atomic (l : loc) :
  ⊢ <<{ ∀∀ (n : nat), l ↦ #n }>> incr #l @ ∅ <<{ l ↦ #(n + 1) | RET #() }>>.
Proof.
  iIntros (Φ) "AU".
  iLöb as "IH". wp_rec.
  wp_bind (!_)%E.
  iMod "AU" as (n) "[Hl [Hcl _]]".
  wp_load.
  iMod ("Hcl" with "Hl") as "AU". iModIntro.
  wp_pures. wp_bind (CmpXchg _ _ _ : expr).
  iMod "AU" as (n') "[Hl Hcl]".
  destruct (decide (n = n')).
  - simplify_eq.
    wp_cmpxchg_suc.
    iDestruct "Hcl" as "[_ Hcl]".
    iMod ("Hcl" with "[$]") as "HΦ".
    by iModIntro; wp_pures.
  - wp_cmpxchg_fail; first naive_solver.
    iDestruct "Hcl" as "[Hcl _]".
    iMod ("Hcl" with "[$]") as "AU".
    iModIntro; wp_pures.
    wp_apply ("IH" with "[$]").
Qed.

(* Hoare Triples in Iris require eliminating a '▷' for the post-condition,
   whereas LATs do not. As such we use the weakest precondition representation
   without '▷' here. *)
Lemma incr_spec_invariant_from_atomic N l :
  inv N (prog_7_inv l) ⊢ WP (incr #l) {{ _, True }}.
Proof.
  iIntros "#Hinv".
  awp_apply (incr_spec_atomic).
  iInv "Hinv" as (n) ">(%Hn & Hl)".
  iAaccIntro with "Hl".
   (* Abort *)
    iIntros "Hl !>".
    unfold prog_7_inv. eauto with iFrame.
  + (* Commit *)
    iIntros "Hl !>".
    iSplitL "Hl"; [|done].
    iNext; iExists (n + 1).
    rewrite Nat.add_1_r.
    replace (n + 1)%Z with (Z.of_nat (S n)) by lia.
    iFrame. iPureIntro. lia.
Qed.

Lemma prog_7_spec_using_lat (N : namespace) :
  {{{ True }}} prog_7 {{{ (n : nat), RET #n; ⌜n ≥ 40⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  unfold prog_7.
  wp_alloc l as "Hl". wp_pures.
  iMod (inv_alloc N _ (prog_7_inv l) with "[Hl]") as "#Hinv".
  { iNext. iExists 40. iFrame. iPureIntro. lia. }
  wp_smart_apply (wp_fork with "[]").
  { iNext; by wp_apply incr_spec_invariant_from_atomic. }
  wp_smart_apply (wp_fork with "[]").
  { iNext; by wp_apply incr_spec_invariant_from_atomic. }
  wp_pures.
  iInv "Hinv" as (n) ">(%Hn & Hl)".
  wp_load. iModIntro.
  iSplitL "Hl"; first (unfold prog_7_inv; eauto with iFrame).
  by iApply "HΦ".
Qed.

End invariants.
