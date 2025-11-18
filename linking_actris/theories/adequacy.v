From iris.heap_lang Require Export adequacy.
From linking_actris Require Export channel.
From iris.prelude Require Import options.

Definition chan_adequacy Σ `{!heapGpreS Σ, !chanG Σ} s e σ φ :
  (∀ `{!chanGS Σ, !heapGS Σ},
    ⊢ inv_heap_inv -∗ proto_chan_ctx -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply (heap_adequacy Σ); iIntros (?) "#?".
  iMod proto_chan_ctx_alloc as (?) "#?".
  by iApply Hwp.
Qed.
