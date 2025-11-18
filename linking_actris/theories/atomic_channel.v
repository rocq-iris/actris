From linking_actris Require Export atomic_lqueue.
From iris.prelude Require Import options.

(** * The definition of the message-passing connectives *)
Definition new_chan : val := λ: <>,
  let: "l" := new_queue #() in
  let: "r" := new_queue #() in
  ((Fst "l", Snd "r"), (Fst "r", Snd "l")).

Definition recv : val := λ: "c",
  let: "recv" := Fst "c" in
  dequeue "recv".

Definition send : val := λ: "c" "v",
  let: "send" := Snd "c" in
  enqueue "send" "v".

Definition link : val := λ: "c1" "c2",
  link_queue (Snd "c2") (Fst "c1");;
  link_queue (Snd "c1") (Fst "c2").

Local Definition is_chan_def `{heapGS Σ, lqueueG Σ} (γ : lqueue_inv_name)
    (c1 c2 : val) (vs1 vs2 : list val) : iProp Σ :=
  ∃ l1 l1' l2 l2' : loc,
    ⌜ c1 = (#l1,#l1')%V ⌝ ∗ ⌜ c2 = (#l2,#l2')%V ⌝ ∗
    is_lqueue γ l1 l2' vs1 ∗ is_lqueue γ l2 l1' vs2.
Local Definition is_chan_aux : seal (@is_chan_def). Proof. by eexists. Qed.
Definition is_chan := is_chan_aux.(unseal).
Local Definition is_chan_unseal :
  @is_chan = @is_chan_def := is_chan_aux.(seal_eq).
Global Arguments is_chan {Σ _ _} γ c1 c2 vs1 vs2.

Local Definition chan_handle_def `{heapGS Σ, lqueueG Σ} (c : val)  : iProp Σ :=
  ∃ l l' : loc, ⌜ c = (#l,#l')%V ⌝ ∗ dequeue_handle l ∗ enqueue_handle l'.
Local Definition chan_handle_aux : seal (@chan_handle_def).
Proof. by eexists. Qed.
Definition chan_handle := chan_handle_aux.(unseal).
Local Definition chan_handle_unseal :
  @chan_handle = @chan_handle_def := chan_handle_aux.(seal_eq).
Global Arguments chan_handle {Σ _ _} c.

Section chan.
  Context `{!heapGS Σ, !lqueueG Σ}.
  Implicit Types v w : val.

  Global Instance is_chan_timeless γ c1 c2 vs1 vs2 :
    Timeless (is_chan γ c1 c2 vs1 vs2).
  Proof. rewrite is_chan_unseal. apply _. Qed.
  Global Instance chan_handle_timeless c : Timeless (chan_handle c).
  Proof. rewrite chan_handle_unseal. apply _. Qed.

  Lemma is_chan_sym γ c1 c2 vs1 vs2 :
    is_chan γ c1 c2 vs1 vs2 ⊣⊢ is_chan γ c2 c1 vs2 vs1.
  Proof.
    rewrite is_chan_unseal.
    iSplit; iDestruct 1 as (l1 l1' l2 l2' -> ->) "[??]";
      iExists l2, l2', l1, l1'; by iFrame.
  Qed.
  Lemma is_chan_unique γ c1 c2 c2' vs1 vs1' vs2 vs2' :
    is_chan γ c1 c2 vs1 vs2 -∗ is_chan γ c1 c2' vs1' vs2' -∗ False.
  Proof.
    rewrite is_chan_unseal. iDestruct 1 as (l1 l1' l2 l2' ??) "[? _]";
      iDestruct 1 as (l3 l3' l4 l4' ??) "[? _]"; simplify_eq/=.
    iApply (is_lqueue_unique with "[$] [$]").
  Qed.
  Lemma is_chan_irr γ c vs1 vs2 : is_chan γ c c vs1 vs2 -∗ False.
  Proof.
    rewrite is_chan_unseal.
    iDestruct 1 as (l1 l1' l2 l2' ??) "[??]"; simplify_eq/=.
    iApply (is_lqueue_unique with "[$] [$]").
  Qed.

  Lemma new_chan_spec N γ :
    {{{ lqueue_ctx N γ }}}
      new_chan #()
    {{{ c1 c2, RET (c1, c2);
        is_chan γ c1 c2 [] [] ∗ chan_handle c1 ∗ chan_handle c2 ∗ £ 1 }}}.
  Proof.
    iIntros (Φ) "#? HΦ". unfold new_chan. wp_pure credit: "H£".
    wp_smart_apply (new_queue_lspec with "[//]") as (l1 l1') "(Hq1 & Hl1 & Hl1')".
    wp_smart_apply (new_queue_lspec with "[//]") as (l2 l2') "(Hq2 & Hl2 & Hl2')".
    wp_pures. iApply "HΦ". iFrame "H£". rewrite is_chan_unseal chan_handle_unseal.
    iModIntro. by iFrame "Hq1 Hq2 Hl1 Hl2' Hl2 Hl1'".
  Qed.

  Lemma recv_spec N γ c1 :
    lqueue_ctx N γ -∗
    chan_handle c1 -∗
    <<{ ∀∀ c2 vs1 vs2, is_chan γ c1 c2 vs1 vs2 }>>
      recv c1 @ ↑N
    <<{ ∃∃ v vs1', ⌜vs1 = v :: vs1'⌝ ∗ £3 ∗ is_chan γ c1 c2 vs1' vs2
      | RET v; chan_handle c1 }>>. 
  Proof.
    rewrite chan_handle_unseal is_chan_unseal.
    iIntros "#? (%l1 & %l1' & -> & Hl1 & Hl1') %Φ AU". wp_lam. wp_pures.
    awp_apply (dequeue_lspec with "[$] Hl1").
    iDestruct (aupd_aacc with "AU") as "AU".
    rewrite /atomic_acc /=. iMod "AU" as (c2 vs1 vs2) "[Hc AU]".
    iDestruct "Hc" as (?? l2 l2' [= <- <-] ->) "[$ Hq2]".
    iModIntro. iSplit.
    - iDestruct "AU" as "[AU _]". iIntros "Hq1".
      by iMod ("AU" with "[$Hq1 $Hq2 //]") as "$".
    - iDestruct "AU" as "[_ AU]". iIntros (v vs'') "(-> & H£ & Hq1)".
      iMod ("AU" with "[$Hq1 $Hq2 $H£ //]") as "HΦ".
      iIntros "!> Hl1". iApply "HΦ". by iFrame.
  Qed.

  Lemma send_spec `{time_receiptG Σ} Ntr γtr N γ c1 v :
    Ntr ## N →
    tr_ctx Ntr γtr -∗
    lqueue_ctx N γ -∗
    chan_handle c1 -∗
    <<{ ∀∀ c2 vs1 vs2 n, is_chan γ c1 c2 vs1 vs2 ∗ ⧗{γtr} n }>>
      send c1 v @ ↑Ntr ∪ ↑N
    <<{ is_chan γ c1 c2 vs1 (vs2 ++ [v]) ∗ ⧗{γtr} (S n) ∗ £ (S n)
      | RET #(); chan_handle c1 }>>.
  Proof.
    rewrite chan_handle_unseal is_chan_unseal.
    iIntros (?) "#? #? (%l1 & %l1' & -> & Hl1 & Hl1') %Φ AU". wp_lam. wp_pures.
    awp_apply (enqueue_lspec with "[$] [$] Hl1'"); first done.
    iDestruct (aupd_aacc with "AU") as "AU".
    rewrite /atomic_acc /=. iMod "AU" as (c2 vs1 vs2 n) "[[Hc $] AU]".
    iDestruct "Hc" as (?? l2 l2' [= <- <-] ->) "[Hq1 $]".
    iModIntro. iSplit.
    - iDestruct "AU" as "[AU _]". iIntros "[Hq2 Hlb]".
      by iMod ("AU" with "[$Hq2 $Hq1 $Hlb //]") as "$".
    - iDestruct "AU" as "[_ AU]". iIntros "(Hq2 & Hlb & H£)".
      iMod ("AU" with "[$Hq2 $Hq1 $H£ $Hlb //]") as "HΦ".
      iIntros "!> Hl1'". iApply "HΦ". by iFrame.
  Qed.

  Lemma link_spec `{time_receiptG Σ} Ntr γtr N γ c2 c3 :
    Ntr ## N →
    tr_ctx Ntr γtr -∗
    lqueue_ctx N γ -∗
    chan_handle c2 -∗ chan_handle c3 -∗
    <<{ ∀∀ (b : bool) c1 c4 vs1 vs2 vs3 vs4 n,
          is_chan γ c1 c2 vs1 vs2 ∗
          (if b then is_chan γ c3 c4 vs3 vs4
           else ⌜c1 = c3⌝ ∗ ⌜c2 = c4⌝ ∗ ⌜vs1 = vs3⌝ ∗ ⌜vs2 = vs4⌝) ∗
          ⧗{γtr} n }>>
      link c2 c3 @ ↑Ntr ∪ ↑N
    <<{ (if b then is_chan γ c1 c4 (vs1 ++ vs3) (vs4 ++ vs2) else True) ∗
        ⧗{γtr} (S n) ∗ £ (S n)
      | RET #(); True }>>.
  Proof.
    rewrite chan_handle_unseal is_chan_unseal.
    iIntros (?) "#? #? (%l2 & %l2' & -> & Hl2 & Hl2')
      (%l3 & %l3' & -> & Hl3 & Hl3') %Φ AU". wp_lam. do 2 wp_pure.
    
    wp_bind (Fst _). iDestruct (aupd_aacc with "AU") as "AU".
    iDestruct (fupd_mask_frame_r _ _ (↑Ntr ∪ ↑N) with "AU") as "AU"; first set_solver.
    rewrite left_id_L (comm_L (∪)) -union_difference_L //.
    iMod "AU" as (b c1 c4 vs1 vs2 vs3 vs4 n) "[(Hc1 & Hc4 & Hlb) [_ Hclose]]".
    iDestruct (tr_aacc _ _ _ (↑Ntr ∪ ↑N) with "[$] [$]") as "Htr"; first set_solver.
    rewrite /atomic_acc. iMod "Htr" as (?) "((%Hle & #Hlb) & Hcl)".
    iApply (wp_lb_update with "Hlb").
    iApply (twp_wp_step_lc _ _ _ _ True with "Hlb [//]"). wp_pure.
    iIntros "!> _ H£ !> {Hlb} Hlb".
    replace ((↑Ntr ∪ ↑N) ∖ ↑Ntr) with (↑N : coPset) by set_solver.
    iApply (fupd_trans _ (↑N)).

    iDestruct "Hc1" as (l1 l1' ?? -> [= <- <-]) "[Hq1 Hq2]". destruct b.
    - iDestruct "Hc4" as (?? l4 l4' [= <- <-] ->) "[Hq3 Hq4]".
      iMod (is_lqueue_llink with "[$] Hq1 Hq3") as "[Hll2 Hlq1]"; first done.
      iMod (is_lqueue_llink with "[$] Hq4 Hq2") as "[Hll3 Hlq4]"; first done.

      iMod ("Hcl" with "Hlb") as "H⧗".
      iDestruct ("Hclose" with "[$H⧗ H£ Hlq1 Hlq4]") as "Hclose".
      { iSplitR "H£"; [|iApply (lc_weaken with "[$]"); lia].
        by iFrame.
      }

      (* TODO: Can this be simplified? *)
      iApply (fupd_mask_intro); first set_solver; iIntros "Hcl".
      iMod "Hcl".
      iModIntro.
      iDestruct (fupd_mask_frame_r _ _ (↑Ntr ∪ ↑N) with "Hclose") as "HΦ"; first set_solver.
      rewrite left_id_L (comm_L (∪)) difference_union_L //.
      replace (⊤ ∪ (↑N ∪ ↑Ntr)) with (⊤ : coPset) by set_solver.
      iMod "HΦ".
      iModIntro.

      wp_smart_apply (link_queue_lspec with "[$] Hl3' Hl2 Hll3").
      wp_smart_apply (link_queue_lspec with "[$] [$] [$] [$]").
      by iApply "HΦ".
    - iDestruct "Hc4" as "(% & % & % & %)"; simplify_eq/=.
      iMod (is_lqueue_llink_self with "[$] Hq1") as "Hll2"; first done.
      iMod (is_lqueue_llink_self with "[$] Hq2") as "Hll3"; first done.

      iMod ("Hcl" with "Hlb") as "H⧗".
      iDestruct ("Hclose" with "[$H⧗ H£]") as "Hclose".
      { iApply (lc_weaken with "[$]"); lia. }

      (* TODO: Can this be simplified? *)
      iApply (fupd_mask_intro); first set_solver; iIntros "Hcl".
      iMod "Hcl".
      iModIntro.
      iDestruct (fupd_mask_frame_r _ _ (↑Ntr ∪ ↑N) with "Hclose") as "HΦ"; first set_solver.
      rewrite left_id_L (comm_L (∪)) difference_union_L //.
      replace (⊤ ∪ (↑N ∪ ↑Ntr)) with (⊤ : coPset) by set_solver.
      iMod "HΦ".
      iModIntro.

      wp_pures.
      wp_smart_apply (link_queue_lspec with "[$] Hl3' Hl2 Hll3").
      wp_smart_apply (link_queue_lspec with "[$] [$] [$] [$]").
      by iApply "HΦ".
  Qed.
End chan.
