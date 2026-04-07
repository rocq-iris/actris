From iris.base_logic Require Import lib.ghost_var.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export notation proofmode.
From iris.heap_lang Require Import array.
From linking_actris.logic Require Export time_receipts.
From iris.prelude Require Import options.

Local Definition tag_nil : Z := 0.
Local Definition tag_cons : Z := 1.
Local Definition tag_link : Z := 2.

Definition new_queue : val := λ: <>,
  let: "end" := AllocN #3 #() in
  ("end" +ₗ #0) <- #tag_nil;;
  (ref "end", ref "end").

Definition enqueue : val := λ: "t" "x",
  let: "node" := !"t" in

  let: "end" := AllocN #3 #() in
  ("end" +ₗ #0) <- #tag_nil;;

  ("node" +ₗ #1) <- "x";;
  ("node" +ₗ #2) <- "end";;
  ("node" +ₗ #0) <- #tag_cons;;

  "t" <- "end";;
  #().

Definition dequeue : val :=
  rec: "dequeue" "d" :=
    let: "node" := !"d" in
    if: !("node" +ₗ #0) = #tag_nil then
      "dequeue" "d"
    else if: !("node" +ₗ #0) = #tag_cons then
      "d" <- !("node" +ₗ #2);;
      !("node" +ₗ #1)
    else
      "d" <- !("node" +ₗ #2);;
      "dequeue" "d".

Definition link_queue : val := λ: "t" "h",
  let: "node" := !"t" in
  let: "lh" := !"h" in
  ("node" +ₗ #2) <- "lh";;
  ("node" +ₗ #0) <- #tag_link;;
  #().

Class queueG Σ := { #[local] queueG_enqueue_inG :: ghost_varG Σ loc }.
Definition queueΣ : gFunctors := #[ghost_varΣ loc].
Global Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.

Fixpoint is_queue_list `{heapGS Σ}
    (lh lt : loc) (mvs : list (option val)) : iProp Σ :=
  match mvs with
  | [] => ⌜lh = lt⌝
  | mv :: mvs => ∃ l : loc,
    match mv with
    | Some v' => lh ↦□ #tag_cons ∗ (lh +ₗ 1) ↦□ v' ∗ (lh +ₗ 2) ↦□ #l
    | None => lh ↦□ #tag_link ∗ (lh +ₗ 2) ↦□ #l
    end ∗ is_queue_list l lt mvs
  end.

Local Definition is_queue_def `{heapGS Σ, queueG Σ}
    (lhptr ltptr : loc) (vs : list val) : iProp Σ :=
  ∃ (γw : gname) (mvs : list (option val)) (lh lt : loc),
    meta ltptr nroot γw ∗
    ⌜ vs = omap id mvs ⌝ ∗
    lhptr ↦{#3/4} #lh ∗
    ghost_var_frac γw (1/2) lt ∗
    is_queue_list lh lt mvs ∗
    lt ↦ #tag_nil.
Local Definition is_queue_aux : seal (@is_queue_def). Proof. by eexists. Qed.
Definition is_queue := is_queue_aux.(unseal).
Local Definition is_queue_unseal :
  @is_queue = @is_queue_def := is_queue_aux.(seal_eq).
Global Arguments is_queue {Σ _ _} lhptr ltptr vs.

Local Definition enqueue_handle_def `{heapGS Σ, queueG Σ} (ltptr : loc) : iProp Σ :=
  ∃ (γw : gname) (lt : loc),
    meta ltptr nroot γw ∗
    ghost_var_frac γw (1/2) lt ∗
    ltptr ↦ #lt ∗
    (lt +ₗ 1) ↦ #() ∗
    (lt +ₗ 2) ↦ #().
Local Definition enqueue_handle_aux : seal (@enqueue_handle_def).
Proof. by eexists. Qed.
Definition enqueue_handle := enqueue_handle_aux.(unseal).
Local Definition enqueue_handle_unseal :
  @enqueue_handle = @enqueue_handle_def := enqueue_handle_aux.(seal_eq).
Global Arguments enqueue_handle {Σ _ _} ltptr.

Local Definition dequeue_handle_def `{heapGS Σ, queueG Σ} (lhptr : loc) : iProp Σ :=
  ∃ lh : loc, lhptr ↦{#1/4} #lh.
Local Definition dequeue_handle_aux : seal (@dequeue_handle_def).
Proof. by eexists. Qed.
Definition dequeue_handle := dequeue_handle_aux.(unseal).
Local Definition dequeue_handle_unseal :
  @dequeue_handle = @dequeue_handle_def := dequeue_handle_aux.(seal_eq).
Global Arguments dequeue_handle {Σ _ _} lhptr.

Section queue_spec.
  Context `{!heapGS Σ, !queueG Σ}.
  Implicit Types v : val.

  Local Instance is_queue_list_timeless lh lt (mvs : list (option val)) :
    Timeless (is_queue_list lh lt mvs).
  Proof. revert lh; induction mvs; simpl; apply _. Qed.

  Global Instance is_queue_timeless lhptr ltptr vs :
    Timeless (is_queue lhptr ltptr vs).
  Proof. rewrite is_queue_unseal. apply _. Qed.
  Global Instance enqueue_handle_timeless lhptr :
    Timeless (enqueue_handle lhptr).
  Proof. rewrite enqueue_handle_unseal. apply _. Qed.
  Global Instance dequeue_handle_timeless ltptr :
    Timeless (dequeue_handle ltptr).
  Proof. rewrite dequeue_handle_unseal. apply _. Qed.

  Lemma is_queue_unique lh lt lt' vs vs' :
    is_queue lh lt vs -∗ is_queue lh lt' vs' -∗ False.
  Proof.
    rewrite is_queue_unseal. iIntros "Hq1 Hq2".
    iDestruct "Hq1" as (????) "(_ & _ & Hlh & _)"; simplify_eq.
    iDestruct "Hq2" as (????) "(_ & _ & Hlh' & _)"; simplify_eq.
    by iDestruct (pointsto_valid_2 with "Hlh Hlh'") as %[[] ?].
  Qed.

  Lemma new_queue_spec:
    {{{ True }}}
      new_queue #()
    {{{ lhptr ltptr, RET (#lhptr, #ltptr);
        is_queue lhptr ltptr [] ∗
        dequeue_handle lhptr ∗ enqueue_handle ltptr }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite is_queue_unseal enqueue_handle_unseal dequeue_handle_unseal.
    wp_lam. wp_alloc l as "Hl /="; first by lia.
    wp_pures.
    iDestruct (array_cons with "Hl") as "[Hl0 Hl]".
    iDestruct (array_cons with "Hl") as "[Hl1 Hl]".
    iDestruct (array_cons with "Hl") as "[Hl2 Hl]".
    rewrite !Loc.add_assoc Loc.add_0.
    wp_store.

    wp_apply wp_alloc as (ltptr) "[Hltptr Hltptr_meta]"; first done.
    wp_alloc lhptr as "Hlhptr".
    iEval (rewrite -Qp.three_quarter_quarter) in "Hlhptr".
    iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".

    iMod (ghost_var_alloc l) as (γw) "[Hγe Hγe']".
    iMod (meta_set _ ltptr γw nroot with "Hltptr_meta") as "#?"; first done.

    wp_pures. iModIntro. iApply "HΦ". iFrame "∗ #". by iExists [].
  Qed.

  (* This specification additionally includes 3 later credits £3, which are
     necessary to eliminate 3 laters when updating the protocol in the protocol
     channel layer. *)
  Lemma dequeue_spec lhptr :
    dequeue_handle lhptr -∗
    <<{ ∀∀ ltptr vs, is_queue lhptr ltptr vs }>>
      dequeue #lhptr @ ∅
    <<{ ∃∃ v vs', ⌜vs = v :: vs'⌝ ∗ £3 ∗ is_queue lhptr ltptr vs'
      | RET v; dequeue_handle lhptr }>>.
  Proof.
    iIntros "Hh %Φ AU". rewrite is_queue_unseal dequeue_handle_unseal.
    iLöb as "IH". wp_rec.
    iDestruct "Hh" as (lh) "Hlhptr".
    wp_load.
    wp_pure credit:"H£1"; wp_pure credit:"H£2"; wp_pure credit:"H£3".
    iCombine "H£1 H£2 H£3" as "H£".
    wp_bind (!_)%E.
    iMod "AU" as (ltptr vs) "[Hqueue Hcl]".
    iDestruct "Hqueue" as (γw vsl lh' lt)
      "(HγwMeta & %Hvsl & Hlhptr' & Hγe & Hlist & Hlt)"; simplify_eq/=.
    iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
    destruct vsl as [|[v|] vsl]; simplify_eq/=; rewrite Loc.add_0.
    - iDestruct "Hlist" as "->".
      wp_load.
      iDestruct "Hcl" as "[Hcl _]".
      iMod ("Hcl" with "[-Hlhptr]") as "HΦ".
      { iFrame. by iExists []. }
      iModIntro. wp_pures.
      iApply ("IH" with "[Hlhptr] [$]"). by iExists _.
    - iDestruct "Hlist" as (l) "((#Hl0 & #Hl1 & #Hl2) & Hlist)".
      wp_load.
      iDestruct "Hcl" as "[Hcl _]".
      iMod ("Hcl" with "[- Hlhptr H£]") as "AU".
      { iExists _, (Some v :: vsl). eauto 10 with iFrame. }
      clear.
      iModIntro. wp_pures. rewrite Loc.add_0. do 2 wp_load. wp_bind (_ <- _)%E.
      iMod "AU" as (ltptr vs) "[Hqueue [_ Hcl]]".
      iDestruct "Hqueue" as (γw vsl lh' lt)
        "(HγwMeta & %Hvsl & Hlhptr' & Hγe & Hlist & Hlt)"; simplify_eq.
      iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
      destruct vsl as [|[v'|] vsl]; simplify_eq/=.
      { iDestruct "Hlist" as "->".
        iDestruct (pointsto_agree with "Hlt Hl0") as %[=]. }
      2: { iDestruct "Hlist" as (l'') "[[Hlh0 _] _]".
        iDestruct (pointsto_agree with "Hlh0 Hl0") as %[=]. }
      iDestruct "Hlist" as (l') "[(Hl0' & Hl1' & Hl2') Hlist]".
      iDestruct (pointsto_agree with "Hl1' Hl1") as %[=];
        iDestruct (pointsto_agree with "Hl2' Hl2") as %[=]; simplify_eq.
      iCombine "Hlhptr' Hlhptr" as "Hlhptr". rewrite Qp.three_quarter_quarter.
      wp_store.
      iEval (rewrite -Qp.three_quarter_quarter) in "Hlhptr".
      iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".
      iMod ("Hcl" with "[- Hlhptr']") as "HΦ".
      { by iFrame. }
      iModIntro. wp_load. iApply "HΦ". by iExists _.
    - iDestruct "Hlist" as (l) "([#Hl0 #Hl2] & Hlist)".
      wp_load.
      iDestruct "Hcl" as "[Hcl _]".
      iMod ("Hcl" with "[- Hlhptr H£]") as "AU".
      { iExists _, (None :: vsl). eauto 10 with iFrame. }
      clear.
      iModIntro. wp_pures. rewrite Loc.add_0. do 2 wp_load. wp_bind (_ <- _)%E.
      iMod "AU" as (ltptr vs) "[Hqueue [Hcl _]]".
      iDestruct "Hqueue" as (γw vsl lh' lt)
        "(HγwMeta & %Hvsl & Hlhptr' & Hγe & Hlist & Hlt)"; simplify_eq.
      iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
      destruct vsl as [|[v'|] vsl]; simplify_eq/=.
      { iDestruct "Hlist" as "->".
        iDestruct (pointsto_agree with "Hlt Hl0") as %[=]. }
      { iDestruct "Hlist" as (l'') "[[Hlh0 _] _]".
        iDestruct (pointsto_agree with "Hlh0 Hl0") as %[=]. }
      iDestruct "Hlist" as (l') "[[Hl0' Hl2'] Hlist]".
      iDestruct (pointsto_agree with "Hl2' Hl2") as %[=]; simplify_eq.
      iCombine "Hlhptr' Hlhptr" as "Hlhptr". rewrite Qp.three_quarter_quarter.
      wp_store.
      iEval (rewrite -Qp.three_quarter_quarter) in "Hlhptr".
      iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".
      iMod ("Hcl" with "[- Hlhptr']") as "AU".
      { by iFrame. }
      iModIntro. wp_pures.
      wp_apply ("IH" with "[Hlhptr'] AU").
      by iExists _.
  Qed.

  (* This specification uses non-persistent time receipts ⧗n to generate
     sufficient laters for updating the protocol state in the protocol channel
     layer. As Iris supports persistent time receipts (steps_lb) rather than
     the non-persistent variaeity, we model non-persistent time receipts using
     an invariant `tr_ctx` containing a persistent time receipt. See
     `time_receipts.v` for the definitions.
   *)
  Lemma enqueue_spec `{time_receiptG Σ} ltptr v γ N :
    tr_ctx N γ -∗
    enqueue_handle ltptr -∗
    <<{ ∀∀ lhptr vs n, is_queue lhptr ltptr vs ∗ ⧗{γ} n }>>
      enqueue #ltptr v @ ↑N
    <<{ is_queue lhptr ltptr (vs ++ [v]) ∗ ⧗{γ} (S n) ∗ £ (S n)
      | RET #(); enqueue_handle ltptr }>>.
  Proof.
    iIntros "#H⧗ctx Hh %Φ AU". rewrite is_queue_unseal enqueue_handle_unseal.
    iDestruct "Hh" as (γw lt) "(#HγwMeta & Hγe & Hltptr & Hlt1 & Hlt2)".
    wp_lam. wp_load.
    wp_alloc ltn as "Hltn"; first by lia.
    wp_pures.
    iDestruct (array_cons with "Hltn") as "[Hltn0 Hltn]".
    iDestruct (array_cons with "Hltn") as "[Hltn1 Hltn]".
    iDestruct (array_cons with "Hltn") as "[Hltn2 _]".
    rewrite Loc.add_assoc Loc.add_0.
    do 3 wp_store. wp_pures. rewrite Loc.add_0.

    (* Change from 'None' to 'Some' *)
    wp_bind (_ <- _)%E.
    iDestruct (aupd_aacc with "AU") as "AU".
    iDestruct (fupd_mask_frame_r _ _ (↑N) with "AU") as "AU"; first set_solver.
    rewrite left_id_L (comm_L (∪)) -union_difference_L //.
    iMod "AU" as (lhptr vs n) "((Hq & H⧗) & Hcl)".

    iDestruct (tr_aacc _ _ _ (↑N) with "H⧗ctx H⧗") as "Htr"; first done.
    rewrite /atomic_acc.
    iMod "Htr" as (m) "((%Hle & #Hsteps) & Hcl')".
    iDestruct "Hq" as (γw' vsl lh lt')
      "(HγwMeta' & %Hvsl & Hlhptr & Hγe' & Hlist & Hlt)"; simplify_eq.
    iDestruct (meta_agree with "HγwMeta' HγwMeta") as "->".

    iDestruct (ghost_var_agree with "Hγe' Hγe") as %[=]; simplify_eq.

    iApply (wp_lb_update with "Hsteps").
    wp_apply (wp_store_lc with "[$Hlt $Hsteps]") as "(Hlt & H£)".
    iIntros "{Hsteps} #Hsteps".

    iMod (pointsto_persist with "Hlt") as "Hlt0".
    iMod (pointsto_persist with "Hlt1") as "Hlt1".
    iMod (pointsto_persist with "Hlt2") as "Hlt2".
    iMod (ghost_var_update ltn with "[Hγe' Hγe]") as "[Hγe' Hγe]";
      first by iCombine "Hγe' Hγe" as "?".
    iMod ("Hcl'" with "[$Hsteps]") as "H⧗".
    iModIntro.
    iDestruct ("Hcl" with "[-Hltn1 Hltn2 Hltptr Hγe']") as "Hcl".
    { iFrame.
      iSplitR "H£"; [|iApply (lc_weaken with "[$]"); lia].
      iExists (vsl ++ [Some v]).
      iSplitR; first by rewrite omap_app.
      iInduction vsl as [|w ws] "IH" forall (lh); simpl.
      { iDestruct "Hlist" as "->". eauto with iFrame. }
      iDestruct "Hlist" as (l') "[Hl Hlist]". iExists l'. iFrame "Hl".
      by iApply ("IH" with "Hlist Hlt0 Hlt1 Hlt2").
    }

    iDestruct (fupd_mask_frame_r _ _ (↑N)
        with "Hcl") as "Hcl"; first set_solver.
    rewrite left_id_L (comm_L (∪)) -union_difference_L; [|done].
    iMod "Hcl" as "HΦ".
    iModIntro. wp_store. iApply "HΦ".
    by iFrame "∗ #".
  Qed.

  Lemma link_queue_spec ltptr1 lhptr2:
    enqueue_handle ltptr1 -∗
    dequeue_handle lhptr2 -∗
    <<{ ∀∀ (b : bool) lhptr1 ltptr2 vs1 vs2,
      is_queue lhptr1 ltptr1 vs1 ∗
      (if b then is_queue lhptr2 ltptr2 vs2
       else ⌜lhptr1 = lhptr2⌝ ∗ ⌜ltptr2 = ltptr1⌝ ∗ ⌜vs1 = vs2⌝)
    }>>
      link_queue #ltptr1 #lhptr2 @ ∅
    <<{ if b then is_queue lhptr1 ltptr2 (vs1 ++ vs2) else True
      | RET #() }>>.
  Proof.
    iIntros "He Hd %Φ AU".
    rewrite is_queue_unseal enqueue_handle_unseal dequeue_handle_unseal.
    iDestruct "He" as (γw lt) "(#HγwMeta & Hγe & Hltptr & Hlt1 & Hlt2)".
    iDestruct "Hd" as (lh) "Hlhptr".
    wp_lam. do 2 wp_load. wp_store. wp_pures.
    rewrite Loc.add_0.
    wp_bind (_ <- _)%E.
    iMod "AU" as (b lhptr1 ltptr2 vs1 vs2) "([Hq1 Hq2] & [_ Hcl])".

    iDestruct "Hq1" as (γw1' vsl1 lh1 lt1')
      "(HγwMeta' & %Hvsl1done & Hlhptr1 & Hγe' & Hlist1 & Hlt0)"; simplify_eq.
    iDestruct (meta_agree with "HγwMeta' HγwMeta") as "->".
    iDestruct (ghost_var_agree with "Hγe' Hγe") as %[=]; simplify_eq.

    wp_store.

    iMod (pointsto_persist with "Hlt0") as "Hlt0".
    iMod (pointsto_persist with "Hlt2") as "Hlt2".

    destruct b; simpl.
    - iDestruct "Hq2" as (γw2 vsl2 lh2' lt2)
        "(Hγw2Meta & %Hvsl2 & Hlhptr2' & Hγe2 & Hlist2 & Hlt2')"; simplify_eq.
      iDestruct (pointsto_agree with "Hlhptr2' Hlhptr") as %[=]; simplify_eq.
      iMod ("Hcl" with "[-]"); [|iModIntro; by wp_pures].
      iExists _, (vsl1 ++ [None] ++ vsl2).
      iFrame.
      iSplitR; first by rewrite omap_app.
      iInduction vsl1 as [|v1 vs1] "IH" forall (lh1); simpl.
      { iDestruct "Hlist1" as "->"; iExists _; iFrame. }
      iDestruct "Hlist1" as (l1') "[Hl1 Hlist1]". iExists l1'. iFrame "Hl1".
      iApply ("IH" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
    - iDestruct "Hq2" as "(-> & -> & <-)".
      iMod ("Hcl" with "[$]") as "HΦ".
      iModIntro; by wp_pures.
  Qed.
End queue_spec.
