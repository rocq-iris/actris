From stdpp Require Import sorting.
From iris.heap_lang Require Import lib.assert.
From linking_actris Require Import proofmode adequacy.

Definition prog1 : expr :=
  let: "c" := start_chan (λ: "c'", let: "n" := recv "c'" in send "c'" ("n" + #1)) in
  let: "d" := start_chan (λ: "d'", send "c" #2;; link "d'" "c") in
  recv "d".

Section spec.

Context `{!heapGS Σ, !chanGS Σ}.

Definition c_prot : iProto Σ := <! (n : nat)> MSG #n; <?> MSG #(n + 1); END.
Definition d_prot : iProto Σ := <?> MSG #3; END.

Lemma prog1_spec :
    {{{ proto_chan_ctx }}}
      prog1
    {{{ RET #3; True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ". unfold prog1. wp_pures.
  wp_apply (start_chan_spec c_prot with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %c Hc". wp_pures.
    wp_recv (n) as "n"; wp_pures.
    by wp_send with "[//]". }
  iIntros "!> %c Hc"; wp_pures.
  wp_apply (start_chan_spec d_prot with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %d Hd". wp_pures.
    wp_send (2) with "[//]". wp_pures.
    iEval (rewrite <-(involutive iProto_dual)) in "Hc".
    by wp_apply (link_spec with "[$Hd $Hc]"). }
  iIntros "!> %d Hd"; wp_pures.
  wp_recv as "_".
  by iApply "HΦ".
Qed.

End spec.

(* Use the adequacy theorem to find a closed proof that prog1 is safe and returns 3. *)
Lemma prog1_adequate σ : adequate NotStuck prog1 σ (λ v _, v = #3).
Proof.
  apply (chan_adequacy #[chanΣ; heapΣ])=> ??.
  iIntros "_ #?".
  by wp_apply prog1_spec.
Qed.
Print Assumptions prog1_adequate.
