From stdpp Require Import sorting.
From iris.heap_lang Require Import lib.assert.
From linking_actris.logic Require Import proofmode adequacy.

Definition prog_9 : val := λ: "c",
  let: "x" := recv "c" in
  let: "d" := recv "c" in
  send "d" "x";;
  link "c" "d".

Section spec.

Context `{!heapGS Σ, !chanGS Σ}.

Definition prog_9_prot : iProto Σ :=
  <? v> MSG v; <? d p> MSG d {{ d ↣ <!> MSG v; p }}; iProto_dual p.

Lemma prog_9_spec c :
  {{{ c ↣ prog_9_prot }}}
    prog_9 c
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  wp_lam.
  wp_recv (v) as "_".
  wp_recv (d p) as "Hd".
  wp_send with "[//]".
  wp_pures.
  wp_apply (link_spec with "[$Hc Hd]"); [|done].
  by rewrite (involutive iProto_dual). 
Qed.

End spec.
