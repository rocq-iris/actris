From iris.algebra Require Import auth gmultiset.
From iris.base_logic Require Import lib.ghost_map lib.invariants.
From linking_actris.logic Require Export time_receipts.
From linking_actris.logic Require Export atomic_simple_queue.
From iris.prelude Require Import options.

Class lqueueG Σ := {
  lqueueG_queueG :: queueG Σ;
  #[local] lqueueG_linksG :: inG Σ (auth (gmultiset (loc * loc)));
  #[local] lqueueG_mapG :: ghost_mapG Σ loc (loc * list val);
}.
Definition lqueueΣ : gFunctors :=
  #[queueΣ; GFunctor (authR (gmultiset (loc * loc)));
    ghost_mapΣ loc (loc * list val)].
Global Instance subG_lqueueΣ {Σ} : subG lqueueΣ Σ → lqueueG Σ.
Proof. solve_inG. Qed.

Local Fixpoint lchain `{!heapGS Σ, !lqueueG Σ}
    (L : list (loc * loc)) (lh lt : loc) (vs : list val) : iProp Σ :=
  match L with
  | [] => is_queue lh lt vs
  | (l1,l2) :: L => ∃ vs1 vs2,
     ⌜ vs = vs1 ++ vs2 ⌝ ∗ is_queue lh l1 vs1 ∗ lchain L l2 lt vs2
  end.

Local Definition lchain_headless `{!heapGS Σ, !lqueueG Σ}
    (L : list (loc * loc)) (lt lt' : loc) (vs : list val) : iProp Σ :=
  match L with
  | [] => ⌜ vs = [] ∧ lt = lt' ⌝
  | (l1,l2) :: L => ⌜ lt = l1 ⌝ ∗ lchain L l2 lt' vs
  end.

Local Fixpoint lchain_tailless `{!heapGS Σ, !lqueueG Σ}
    (L : list (loc * loc)) (lh lh' : loc) (vs : list val) : iProp Σ :=
  match L with
  | [] => ⌜ vs = [] ∧ lh = lh' ⌝
  | (l1,l2) :: L => ∃ vs1 vs2,
     ⌜ vs = vs1 ++ vs2 ⌝ ∗ is_queue lh l1 vs1 ∗ lchain_tailless L l2 lh' vs2
  end.

Local Definition lcycle `{!heapGS Σ, !lqueueG Σ} (L : list (loc * loc)) : iProp Σ :=
  match L with
  | [] => True
  | (l1,l2) :: L => ∃ vs, lchain L l2 l1 vs
  end.

Record lqueue_inv_name :=
  LQueueInvName { llinks_name : gname; lchains_name : gname }.

Local Definition flatten `{Countable A} : gmap loc (list A) → gmultiset A :=
  map_fold (λ _ xs, (list_to_set_disj xs ⊎.)) ∅.

Local Definition lqueue_inv `{!heapGS Σ, !lqueueG Σ}
    (γ : lqueue_inv_name) : iProp Σ :=
  ∃ (Ls : list (list (loc * loc)))
      (m : gmap loc (loc * list val * list (loc * loc))),
    own γ.(llinks_name) (● (list_to_set_disj (mjoin Ls) ⊎ flatten (snd <$> m))) ∗
    ghost_map_auth_frac γ.(lchains_name) 1 (fst <$> m) ∗
    ([∗ map] lh ↦ x ∈ m, lchain x.2 lh x.1.1 x.1.2) ∗
    ([∗ list] L ∈ Ls, lcycle L).

Definition lqueue_ctx `{!heapGS Σ, !lqueueG Σ} (N : namespace)
    (γ : lqueue_inv_name) : iProp Σ :=
  inv N (lqueue_inv γ).

Definition is_lqueue `{!heapGS Σ, !lqueueG Σ} (γ : lqueue_inv_name)
    (lh lt : loc) (vs : list val) : iProp Σ :=
  lh ↪[γ.(lchains_name)] (lt,vs).

Definition is_llink `{!heapGS Σ, !lqueueG Σ} (γ : lqueue_inv_name)
    (l1 l2 : loc) : iProp Σ :=
  own γ.(llinks_name) (◯ {[+ (l1,l2) +]}).

Section lqueue.
  Context `{!heapGS Σ, !lqueueG Σ}.
  Implicit Types v w : val.
  Implicit Types vs ws : list val.
  Implicit Types L : list (loc * loc).
  Implicit Types Ls : list (list (loc * loc)).

  Local Instance lchain_timeless L lh lt vs : Timeless (lchain L lh lt vs).
  Proof. revert vs lh. induction L as [|[??]]; apply _. Qed.
  Local Instance lcycle_timeless L : Timeless (lcycle L).
  Proof. destruct L as [|[??]]; apply _. Qed.

  Local Lemma lchain_join L1 L2 lh1 lh2 lt1 lt2 vs1 vs2 :
    lchain L1 lh1 lt1 vs1 -∗
    lchain L2 lh2 lt2 vs2 -∗
    lchain (L1 ++ (lt1,lh2) :: L2) lh1 lt2 (vs1 ++ vs2).
  Proof.
    iIntros "HL1 HL2".
    iInduction L1 as [|[l1 l2] L1] "IH" forall (lh1 vs1); simpl; [by iFrame|].
    iDestruct "HL1" as (vs1' vs1'' ->) "[$ HL1]".
    iExists (vs1'' ++ vs2). iSplit; [by rewrite assoc_L|].
    by iApply ("IH" with "[$]").
  Qed.

  Local Lemma lchain_recv L lh lt vs :
    lchain L lh lt vs -∗ ∃ lt' vs1 vs2,
      ⌜ vs = vs1 ++ vs2 ⌝ ∗ lchain_headless L lt' lt vs2 ∗ is_queue lh lt' vs1.
  Proof.
    iIntros "HL". destruct L as [|[l1 l2] L]; simpl.
    { iFrame. iExists []. by rewrite right_id_L. }
    by iDestruct "HL" as (vs' vs'' ->) "[$$]".
  Qed.

  Local Lemma lchain_headless_fill L lh lt' lt vs1 vs2 :
    lchain_headless L lt' lt vs2 -∗
    is_queue lh lt' vs1 -∗
    lchain L lh lt (vs1 ++ vs2).
  Proof.
    destruct L as [|[l1 l2] L]; simpl.
    { iIntros "[-> ->] ?". by rewrite right_id_L. }
    iIntros "[-> ?] ?"; by iFrame.
  Qed.

  Local Lemma lchain_send L lh lt vs :
    lchain L lh lt vs -∗ ∃ lh' vs1 vs2,
      ⌜ vs = vs1 ++ vs2 ⌝ ∗ lchain_tailless L lh lh' vs1 ∗ is_queue lh' lt vs2.
  Proof.
    iIntros "HL". iInduction L as [|[l1 l2] L] "IH" forall (lh vs); simpl.
    { iFrame "HL". by iExists []. }
    iDestruct "HL" as (vs' vs'' ->) "[$ HL1]".
    iDestruct ("IH" with "HL1") as (lh' vs1 vs2 ->) "[$ $]".
    iExists (vs' ++ vs1). by rewrite assoc_L.
  Qed.

  Local Lemma lchain_tailless_fill L lh lh' lt vs1 vs2 :
    lchain_tailless L lh lh' vs1 -∗
    is_queue lh' lt vs2 -∗
    lchain L lh lt (vs1 ++ vs2).
  Proof.
    iIntros "HL Hq". iInduction L as [|[l1 l2] L] "IH" forall (lh vs1); simpl.
    { by iDestruct "HL" as "[-> ->]". }
    iDestruct "HL" as (vs' vs'' ->) "[$ HL2]".
    iDestruct ("IH" with "HL2 Hq") as "$". by rewrite assoc_L.
  Qed.

  Local Lemma lchain_headtailless_join L1 L2 lh lt lh' lt' vs1 vs2 vs3 :
    lchain_tailless L1 lh lh' vs1 -∗
    is_queue lh' lt' vs2 -∗
    lchain_headless L2 lt' lt vs3 -∗
    lchain (L1 ++ L2) lh lt (vs1 ++ vs2 ++ vs3).
  Proof.
    iIntros "HL1 Hq HL2".
    iInduction L1 as [|[l1 l2] L1] "IH" forall (lh vs1); simpl.
    { iDestruct "HL1" as %[-> ->]. by iApply (lchain_headless_fill with "[$]"). }
    iDestruct "HL1" as (vs1' vs1'' ->) "[$ HL1]".
    iExists (vs1'' ++ vs2 ++ vs3). iSplit; [by rewrite !assoc_L|].
    by iApply ("IH" with "[$] [$]").
  Qed.

  Local Lemma lchain_link L1 L2 l1 l2 lh lt vs :
    lchain (L1 ++ (l1,l2) :: L2) lh lt vs -∗ ∃ lh' lt' vs1 vs2,
      is_queue lh' l1 vs1 ∗
      is_queue l2 lt' vs2 ∗
      (is_queue lh' lt' (vs1 ++ vs2) -∗ lchain (L1 ++ L2) lh lt vs)
      ∧
      (is_queue lh' l1 vs1 -∗ is_queue l2 lt' vs2 -∗
        lchain (L1 ++ (l1,l2) :: L2) lh lt vs).
  Proof.
    iIntros "HL". iInduction L1 as [|[l1' l2'] L1] "IH" forall (lh vs); simpl.
    { iDestruct "HL" as (vs1 vs2 ->) "[$ HL]".
      destruct L2 as [|[l1' l2'] L2]; simpl; first by auto 10 with iFrame.
      iDestruct "HL" as (vs2' vs2'' ->) "[$ HL]". iSplit.
      - iIntros "$". iFrame "HL". by rewrite assoc_L.
      - iIntros "Hl1 Hl2". auto with iFrame. }
    iDestruct "HL" as (vs1 vs2 ->) "[Hq HL]".
    iDestruct ("IH" with "HL") as (lh' lt' vs2' vs2'') "($ & $ & H)".
    iSplit.
    - iIntros "Hq' {$Hq}". iExists _. iSplit; [done|]. by iApply "H".
    - iIntros "?? {$Hq}". iExists _. iSplit; [done|]. iApply ("H" with "[$] [$]").
  Qed.

  Local Lemma lcycle_link L1 L2 l1 l2 :
    lcycle (L1 ++ (l1,l2) :: L2) -∗
      (∃ vs, ⌜ L1 = [] ⌝ ∗ ⌜ L2 = [] ⌝ ∗ is_queue l2 l1 vs) ∨
      (∃ lh' lt' vs1 vs2,
        is_queue lh' l1 vs1 ∗
        is_queue l2 lt' vs2 ∗
        (is_queue lh' lt' (vs1 ++ vs2) -∗ lcycle (L1 ++ L2))
        ∧
        (is_queue lh' l1 vs1 -∗ is_queue l2 lt' vs2 -∗
          lcycle (L1 ++ (l1,l2) :: L2))).
  Proof.
    iIntros "HL". destruct L1 as [|[l1' l2'] L1]; simpl.
    { iDestruct "HL" as (vs) "HL".
      destruct L2 as [|[l1' l2'] L2]; simpl; [iLeft; by iFrame|].
      iRight. iDestruct "HL" as (vs1 vs2 ->) "[$ HL]".
      iInduction L2 as [|[l1'' l2''] L2] "IH" forall (l2' vs2); simpl.
      { iFrame "HL". eauto 10 with iFrame. }
      iDestruct "HL" as (vs2' vs2'' ->) "[Hq HL]".
      iDestruct ("IH" with "HL") as (l1''' vs) "[$ H]". iSplit.
      - iDestruct "H" as "[H _]".
        iIntros "Hq' {$Hq}". iDestruct ("H" with "Hq'") as (vs') "$". eauto.
      - iDestruct "H" as "[_ H]". iIntros "Hq1 Hq2".
        iDestruct ("H" with "Hq1 Hq2") as (??? ->) "[$$]". eauto with iFrame. }
    iRight. iDestruct "HL" as (vs) "HL".
    iDestruct (lchain_link with "HL") as (????) "($ & $ & H)". iSplit.
    - iIntros "Hq". iExists _. by iApply "H".
    - iIntros "Hq1 Hq2". iExists _. iApply ("H" with "[$] [$]"). 
  Qed.

  Local Lemma flatten_insert `{Countable A} m l (xs : list A) :
    m !! l = None → flatten (<[l:=xs]> m) = list_to_set_disj xs ⊎ flatten m.
  Proof. apply: map_fold_insert_L; multiset_solver. Qed.
  Local Lemma flatten_insert_delete `{Countable A} m l (xs : list A) :
    flatten (<[l:=xs]> m) = list_to_set_disj xs ⊎ flatten (delete l m).
  Proof.
    rewrite -insert_delete_eq. by apply flatten_insert, lookup_delete_eq.
  Qed.
  Local Lemma flatten_delete `{Countable A} m l (xs : list A) :
    m !! l = Some xs → flatten m = list_to_set_disj xs ⊎ flatten (delete l m).
  Proof. apply: map_fold_delete_L; multiset_solver. Qed.

  Local Lemma flatten_lookup `{Countable A} m (x : A) :
    x ∈ flatten m → ∃ k xs, m !! k = Some xs ∧ x ∈ xs.
  Proof.
    induction m as [|i xs m ? IH] using map_ind; [multiset_solver|].
    rewrite flatten_insert // gmultiset_elem_of_disj_union.
    intros [?%elem_of_list_to_set_disj|(k&xs'&?&?)%IH].
    - exists i, xs. by rewrite lookup_insert_eq.
    - exists k, xs'. by rewrite lookup_insert_ne; last naive_solver.
  Qed.

  Local Lemma is_lqueue_new N E γ lh lt vs :
    ↑N ⊆ E →
    lqueue_ctx N γ -∗ is_queue lh lt vs ={E}=∗ is_lqueue γ lh lt vs.
  Proof.
    iIntros (?) "#Hinv Hq". iInv "Hinv" as (Ls m) ">(HL● & Hm● & Hm & $)".
    iAssert ⌜ ¬is_Some (m !! lh) ⌝%I as %Hlh%eq_None_not_Some.
    { iIntros ([[[lt' vs'] L] Hlh]).
      iDestruct (big_sepM_lookup with "Hm") as "Hc"; first done; simpl.
      iDestruct (lchain_recv with "Hc") as (lt'' ?? _) "[_ Hq'']".
      iDestruct (is_queue_unique with "[$] [$]") as %[]. }
    iMod (ghost_map_insert lh (lt, vs) with "Hm●") as "[Hm● $]".
    { by rewrite lookup_fmap Hlh. }
    iModIntro. iSplitL; [|done]. iModIntro.
    iExists (<[ lh := ((lt,vs),[]) ]> m).
    rewrite !fmap_insert /= flatten_insert; last (by rewrite lookup_fmap Hlh).
    rewrite /= left_id_L. iFrame "HL● Hm●".
    iApply big_sepM_insert; first done. iFrame.
  Qed.

  (** We can abort by letting [vs2' := vs2] *)
  Local Lemma is_lqueue_send N E γ lh lt vs :
    ↑N ⊆ E →
    lqueue_ctx N γ -∗
    is_lqueue γ lh lt vs ={E,E∖↑N}=∗ ∃ lh' vs1 vs2,
      ⌜ vs = vs1 ++ vs2 ⌝ ∗ is_queue lh' lt vs2 ∗
      (∀ vs2', is_queue lh' lt vs2' ={E∖↑N,E}=∗ is_lqueue γ lh lt (vs1 ++ vs2')).
  Proof.
    iIntros (?) "#Hinv Hlq".
    iInv "Hinv" as (Ls m) ">(HL● & Hm● & Hm & HL)" "Hclose". iModIntro.
    iDestruct (ghost_map_lookup with "Hm● Hlq") as %Hlh.
    rewrite lookup_fmap fmap_Some in Hlh.
    destruct Hlh as ([? L]&Hlh&?); simplify_eq/=.
    iDestruct (big_sepM_insert_acc with "Hm") as "[Hvs Hm]"; first done; simpl.
    iDestruct (lchain_send with "Hvs") as (lh' vs1 vs2) "($ & Htl & $)".
    iIntros (vs2') "Hq".
    iMod (ghost_map_update (lt, vs1 ++ vs2') with "Hm● Hlq") as "[Hm● $]".
    iApply "Hclose"; iModIntro.
    iExists Ls, (<[ lh := ((lt,vs1 ++ vs2'), L) ]> m).
    rewrite !fmap_insert /= (insert_id (snd <$> _)) ?lookup_fmap ?Hlh //.
    iFrame "HL● Hm● HL". iApply "Hm". by iApply (lchain_tailless_fill with "[$]").
  Qed.

  (** We can abort by letting [vs1' := vs1] *)
  Local Lemma is_lqueue_recv N E γ lh lt vs :
    ↑N ⊆ E →
    lqueue_ctx N γ -∗
    is_lqueue γ lh lt vs ={E,E∖↑N}=∗ ∃ lt' vs1 vs2,
      ⌜ vs = vs1 ++ vs2 ⌝ ∗ is_queue lh lt' vs1 ∗
      (∀ vs1', is_queue lh lt' vs1' ={E∖↑N,E}=∗ is_lqueue γ lh lt (vs1' ++ vs2)). 
  Proof.
    iIntros (?) "#Hinv Hlq".
    iInv "Hinv" as (Ls m) ">(HL● & Hm● & Hm & HL)" "Hclose". iModIntro.
    iDestruct (ghost_map_lookup with "Hm● Hlq") as %Hlh.
    rewrite lookup_fmap fmap_Some in Hlh.
    destruct Hlh as ([? L]&Hlh&?); simplify_eq/=.
    iDestruct (big_sepM_insert_acc with "Hm") as "[Hvs Hm]"; first done; simpl.
    iDestruct (lchain_recv with "Hvs") as (lt' vs1 vs2) "($ & Hhd & $)".
    iIntros (vs1') "Hq".
    iMod (ghost_map_update (lt, vs1' ++ vs2) with "Hm● Hlq") as "[Hm● $]".
    iApply "Hclose"; iModIntro.
    iExists Ls, (<[ lh := ((lt,vs1' ++ vs2), L) ]> m).
    rewrite !fmap_insert /= (insert_id (snd <$> _)) ?lookup_fmap ?Hlh //.
    iFrame "HL● Hm● HL". iApply "Hm". by iApply (lchain_headless_fill with "[$]").
  Qed.

  Local Lemma is_lqueue_link N E γ lh lt :
    ↑N ⊆ E →
    lqueue_ctx N γ -∗
    is_llink γ lt lh ={E,E∖↑N}=∗
      (∃ vs, is_queue lh lt vs ∗
        (|={E∖↑N,E}=> True) ∧
        (is_queue lh lt vs ={E∖↑N,E}=∗ is_llink γ lt lh)) ∨
      (∃ lh' lt' vs1 vs2,
        is_queue lh' lt vs1 ∗
        is_queue lh lt' vs2 ∗
        (is_queue lh' lt' (vs1 ++ vs2) ={E∖↑N,E}=∗ True) ∧
        (is_queue lh' lt vs1 -∗ is_queue lh lt' vs2 ={E∖↑N,E}=∗ is_llink γ lt lh)).
  Proof.
    iIntros (?) "#Hinv Hlq".
    iInv "Hinv" as (Ls m) ">(HL● & Hm● & Hm & HL)" "Hclose". iModIntro.
    iCombine "HL● Hlq" gives %[HLs%gmultiset_included _]%auth_both_valid_discrete.
    apply gmultiset_singleton_subseteq_l in HLs.
    apply gmultiset_elem_of_disj_union in HLs as [HLs|HLs].
    - apply elem_of_list_to_set_disj in HLs.
      apply list_elem_of_join in HLs
        as (L & (L1&L2&->)%list_elem_of_split & [i Hi]%list_elem_of_lookup).
      iDestruct (big_sepL_insert_acc with "HL") as "[Hvs HL]"; first done; simpl.
      iDestruct (lcycle_link with "Hvs")
        as "[(%vs & -> & -> & Hq)|Hvs]"; simplify_eq/=.
      { iLeft. iFrame "Hq". iSplit.
        + iAssert (|==> own (llinks_name γ) (● (list_to_set_disj
            (mjoin (<[i:=[]]> Ls)) ⊎ flatten (snd <$> m))))%I
            with "[HL● Hlq]" as ">HL●".
          { iApply (own_update_2 with "HL● Hlq").
            apply auth_update_dealloc, gmultiset_local_update.
            apply list_elem_of_split_length in Hi as (Ls1 & Ls2 & -> & ->).
            rewrite insert_app_r_alt // Nat.sub_diag /=.
            rewrite !join_app /= !list_to_set_disj_app /=. multiset_solver. }
          iApply "Hclose". iModIntro. iFrame "HL● Hm● Hm". by iApply "HL". 
        + iIntros "Hq {$Hlq}". iApply "Hclose". iModIntro. iFrame "HL● Hm● Hm".
          iSpecialize ("HL" $! [(lt, lh)] with "[$Hq]").
          by rewrite list_insert_id. }
      iRight. iDestruct "Hvs" as (lh' lt' vs1 vs2) "($ & $ & H)". iSplit.
      + iDestruct "H" as "[H _]". iIntros "Hq".
        iAssert (|==> own (llinks_name γ) (● (list_to_set_disj
          (mjoin (<[i:=L1 ++ L2]> Ls)) ⊎ flatten (snd <$> m))))%I
          with "[HL● Hlq]" as ">HL●".
        { iApply (own_update_2 with "HL● Hlq").
          apply auth_update_dealloc, gmultiset_local_update.
          apply list_elem_of_split_length in Hi as (Ls1 & Ls2 & -> & ->).
          rewrite insert_app_r_alt // Nat.sub_diag /=.
          rewrite !join_app /= !list_to_set_disj_app /=. multiset_solver. }
        iApply "Hclose". iModIntro. iFrame "HL● Hm● Hm".
        iApply "HL". by iApply "H".
      + iDestruct "H" as "[_ H]". iIntros "Hq1 Hq2 {$Hlq}".
        iApply "Hclose". iModIntro. iFrame "HL● Hm● Hm".
        iSpecialize ("HL" with "(H Hq1 Hq2)").
        by rewrite list_insert_id.
    - iRight. apply flatten_lookup in HLs
        as (l1 & ? & Hl1 & (L1&L2&->)%list_elem_of_split).
      rewrite lookup_fmap fmap_Some in Hl1.
      destruct Hl1 as ([[l2 vs] ?]&Hl1&?); simplify_eq/=.
      iDestruct (big_sepM_insert_acc with "Hm") as "[Hvs Hm]"; first done; simpl.
      iDestruct (lchain_link with "Hvs") as (l3 l4 vs1 vs2) "($ & $ & H)".
      iSplit.
      + iDestruct "H" as "[H _]". iIntros "Hq".
        iAssert (|==> own (llinks_name γ) (● (list_to_set_disj (mjoin Ls) ⊎
          flatten (<[l1:=L1 ++ L2]> (snd <$> m)))))%I with "[HL● Hlq]" as ">HL●".
        { iApply (own_update_2 with "HL● Hlq").
          apply auth_update_dealloc, gmultiset_local_update.
          rewrite flatten_insert_delete.
          rewrite (flatten_delete _ l1 (L1 ++ (lt, lh) :: L2));
            last by rewrite lookup_fmap Hl1.
          rewrite !list_to_set_disj_app /=. multiset_solver. }
        iApply "Hclose". iModIntro.
        iExists Ls, (<[ l1 := ((l2,vs), L1 ++ L2) ]> m).
        rewrite !fmap_insert /= (insert_id (fst <$> _));
          last by rewrite lookup_fmap Hl1 //.
        iFrame "HL Hm● HL●". iApply "Hm". by iApply "H".
      + iDestruct "H" as "[_ H]". iIntros "Hq1 Hq2 {$Hlq}".
        iApply "Hclose". iModIntro. iFrame "HL● Hm● HL".
        iSpecialize ("Hm" $! (_, _, _) with "(H Hq1 Hq2)").
        by rewrite insert_id.
  Qed.

  (** The public lemmas *)
  Global Instance is_lqueue_timeless γ lh lt vs :
    Timeless (is_lqueue γ lh lt vs).
  Proof. apply _. Qed.
  Global Instance is_llink_timeless γ lh lt : Timeless (is_llink γ lh lt).
  Proof. apply _. Qed.
  Global Instance lqueue_ctx_persistent N γ : Persistent (lqueue_ctx N γ).
  Proof. apply _. Qed.

  Lemma is_lqueue_unique γ lh lt lt' vs vs' :
    is_lqueue γ lh lt vs -∗ is_lqueue γ lh lt' vs' -∗ False.
  Proof. iIntros "Hq1 Hq2". by iCombine "Hq1 Hq2" gives %[[] ?]. Qed.

  (* To allocate and open invariants around Iris updates, the updates need
     a given mask. The update can be run when no invariants in the mask are
     currently open. *)
  Lemma lqueue_ctx_alloc E N : ⊢ |={E}=> ∃ γ, lqueue_ctx N γ.
  Proof.
    iMod (own_alloc (● ∅)) as (γL) "HL●"; first by apply auth_auth_valid.
    iMod ghost_map_alloc_empty as (γm) "Hm●".
    iExists (LQueueInvName γL γm). iApply inv_alloc. iModIntro.
    iExists [], ∅. iFrame; auto.
  Qed.

  (* Both is_lqueue_llink and is_lqueue_llink_self need to open and close the
  ghost linking queue invariant, and therefore need the namespace in the
  mask of the update. *)
  Lemma is_lqueue_llink N E γ lh1 lh2 lt1 lt2 vs1 vs2 :
    ↑N ⊆ E →
    lqueue_ctx N γ -∗
    is_lqueue γ lh1 lt1 vs1 -∗
    is_lqueue γ lh2 lt2 vs2 ={E}=∗
      is_llink γ lt1 lh2 ∗ is_lqueue γ lh1 lt2 (vs1 ++ vs2).
  Proof.
    iIntros (?) "#Hinv Hlq1 Hlq2".
    iInv "Hinv" as (Ls m) ">(HL● & Hm● & Hm & HL)" "Hclose".
    iDestruct (ghost_map_lookup with "Hm● Hlq2") as %Hlh2.
    rewrite lookup_fmap fmap_Some in Hlh2.
    destruct Hlh2 as ([? L2]&Hlh2&?); simplify_eq/=.
    iMod (ghost_map_delete with "Hm● Hlq2") as "Hm●". rewrite -fmap_delete.
    iDestruct (big_sepM_delete with "Hm") as "[Hvs2 Hm]"; first done; simpl.
    iDestruct (ghost_map_lookup with "Hm● Hlq1") as %Hlh1.
    rewrite lookup_fmap fmap_Some in Hlh1.
    destruct Hlh1 as ([? L1]&Hlh1&?); simplify_eq/=.
    iDestruct (big_sepM_insert_acc with "Hm") as "[Hvs1 Hm]"; first done; simpl.
    iDestruct (lchain_join with "Hvs1 Hvs2") as "Hvs".
    iAssert (|==> own (llinks_name γ) (● (list_to_set_disj (mjoin Ls) ⊎
      flatten (<[lh1:=L1 ++ (lt1, lh2) :: L2]> (snd <$> delete lh2 m)))
      ⋅ ◯ {[+ (lt1,lh2) +]}))%I with "[HL●]" as ">[HL● $]".
    { iApply (own_update with "HL●").
      apply auth_update_alloc, gmultiset_local_update.
      rewrite flatten_insert_delete.
      rewrite (flatten_delete (snd <$> m) lh2 L2);
        last by rewrite lookup_fmap Hlh2.
      rewrite (flatten_delete (delete _ _) lh1 L1);
        last by rewrite -fmap_delete lookup_fmap Hlh1.
      rewrite !list_to_set_disj_app /= fmap_delete. multiset_solver. }
    iMod (ghost_map_update (lt2, vs1 ++ vs2) with "Hm● Hlq1") as "[Hm● $]".
    iApply "Hclose". iModIntro.
    iExists Ls, (<[lh1:=((lt2,vs1++vs2), L1 ++ (lt1,lh2) :: L2)]> (delete lh2 m)).
    rewrite !fmap_insert /=. iFrame "HL Hm● HL●". by iApply "Hm".
  Qed.

  Lemma is_lqueue_llink_self N E γ lh lt vs :
    ↑N ⊆ E →
    lqueue_ctx N γ -∗
    is_lqueue γ lh lt vs ={E}=∗ is_llink γ lt lh.
  Proof.
    iIntros (?) "#Hinv Hlq".
    iInv "Hinv" as (Ls m) ">(HL● & Hm● & Hm & HL)" "Hclose".
    iDestruct (ghost_map_lookup with "Hm● Hlq") as %Hlh.
    rewrite lookup_fmap fmap_Some in Hlh.
    destruct Hlh as ([? L]&Hlh&?); simplify_eq/=.
    iMod (ghost_map_delete with "Hm● Hlq") as "Hm●". rewrite -fmap_delete.
    iDestruct (big_sepM_delete with "Hm") as "[Hvs Hm]"; first done; simpl.
    iMod (own_update with "HL●") as "[HL● Hlq]".
    { apply auth_update_alloc,
        (gmultiset_local_update_alloc _ _ ({[+ (lt,lh) +]})). }
    rewrite left_id_L /=. iFrame "Hlq".
    iApply "Hclose". iModIntro. iExists (((lt,lh) :: L) :: Ls), (delete lh m).
    iEval (rewrite -(comm_L _ {[+ _ +]}) assoc_L) in "HL●".
    iFrame "HL Hm● Hvs Hm".
    rewrite fmap_delete /= (flatten_delete (snd <$> m) lh L);
      last by rewrite lookup_fmap Hlh.
    rewrite list_to_set_disj_app.
    by rewrite (comm_L _ (list_to_set_disj L) (list_to_set_disj _)) -!assoc_L.
  Qed.

  Lemma new_queue_lspec N γ :
    {{{ lqueue_ctx N γ }}}
      new_queue #()
    {{{ lh lt, RET (#lh, #lt);
        is_lqueue γ lh lt [] ∗
        dequeue_handle lh ∗ enqueue_handle lt }}}.
  Proof.
    iIntros (Φ) "#? HΦ". iApply wp_fupd.
    wp_apply (new_queue_spec with "[//]") as (l1 l1') "(Hq & Hl & Hl')".
    iMod (is_lqueue_new with "[$] Hq") as "Hq"; first done.
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma dequeue_lspec N γ lh :
    lqueue_ctx N γ -∗
    dequeue_handle lh -∗
    <<{ ∀∀ lt vs, is_lqueue γ lh lt vs }>>
      dequeue #lh @ ↑N
    <<{ ∃∃ v vs', ⌜vs = v :: vs'⌝ ∗ £3 ∗ is_lqueue γ lh lt vs'
      | RET v; dequeue_handle lh }>>.
  Proof.
    iIntros "#? Hlh %Φ AU". awp_apply (dequeue_spec with "Hlh").
    iDestruct (aupd_aacc with "AU") as "AU".
    iDestruct (fupd_mask_frame_r _ _ (↑N) with "AU") as "AU"; first set_solver.
    rewrite left_id_L (comm_L (∪)) -union_difference_L // difference_empty_L.
    rewrite /atomic_acc /=. iMod "AU" as (lt vs) "[Hlt AU]".
    iMod (is_lqueue_recv with "[$] Hlt")
      as (lt' vs1' vs1'' ->) "[$ H]"; first done.
    rewrite difference_diag_L. iModIntro. iSplit.
    - iDestruct "AU" as "[AU _]". iIntros "Hq". iMod ("H" with "Hq") as "Hlq".
      iDestruct (fupd_mask_frame_r _ _ (↑N)
        with "(AU Hlq)") as "AU"; first set_solver.
      by rewrite left_id_L (comm_L (∪)) -union_difference_L.
    - iDestruct "AU" as "[_ AU]". iIntros (v vs'') "(->&H£&Hq)".
      iMod ("H" with "Hq") as "Hlq".
      iDestruct (fupd_mask_frame_r _ _ (↑N)
        with "(AU [$Hlq $H£ //])") as "AU"; first set_solver.
      by rewrite left_id_L (comm_L (∪)) -union_difference_L.
  Qed.

  (* The enqueue specification uses two invariants: tr_ctx on the queue layer
  and lqueue_ctx on this layer. To allow both invariants to be opened at the
  sane time, their namespaces must be disjoint. *)
  Lemma enqueue_lspec `{time_receiptG Σ} Ntr γtr N γ lt v :
    Ntr ## N →
    tr_ctx Ntr γtr -∗
    lqueue_ctx N γ -∗
    enqueue_handle lt -∗
    <<{ ∀∀ lh vs n, is_lqueue γ lh lt vs ∗ ⧗{γtr} n }>>
      enqueue #lt v @ ↑Ntr ∪ ↑N
    <<{ is_lqueue γ lh lt (vs ++ [v]) ∗ ⧗{γtr} (S n) ∗ £ (S n)
      | RET #(); enqueue_handle lt }>>.
  Proof.
    iIntros (HN) "#? #? Hlt %Φ AU". awp_apply (enqueue_spec with "[$] Hlt").
    iDestruct (aupd_aacc with "AU") as "AU".
    iDestruct (fupd_mask_frame_r _ _ (↑N) with "AU") as "AU"; first set_solver.
    rewrite left_id_L (comm_L (∪)) -difference_difference_l_L -union_difference_L //; [|set_solver].
    rewrite /atomic_acc /=. iMod "AU" as (lh vs n) "[[Hlh $] AU]".
    iMod (is_lqueue_send with "[$] Hlh")
      as (lt' vs1' vs1'' ->) "[$ H]"; first done.
    rewrite difference_diag_L. iModIntro. iSplit.
    - iDestruct "AU" as "[AU _]". iIntros "[Hq Hlb]".
      iMod ("H" with "Hq") as "Hlq".
      iDestruct (fupd_mask_frame_r _ _ (↑N)
        with "(AU [$Hlq $Hlb //])") as "AU"; first set_solver.
      rewrite left_id_L (comm_L (∪)) -union_difference_L; [done|set_solver].
    - iDestruct "AU" as "[_ AU]". iIntros "(Hq&Hlb&H£)".
      iMod ("H" with "Hq") as "Hlq". rewrite assoc_L.
      iDestruct (fupd_mask_frame_r _ _ (↑N)
        with "(AU [$Hlq $H£ $Hlb //])") as "AU"; first set_solver.
      rewrite left_id_L (comm_L (∪)) -union_difference_L; [done|set_solver].
  Qed.

  (* The specification for linking ghost linking queues is in the same style as
     start_chan, as it is easier to apply using Iris proof mode than a Hoare
     style specification. *)
  Lemma link_queue_lspec N γ lt lh Φ :
    lqueue_ctx N γ -∗
    enqueue_handle lt -∗
    dequeue_handle lh -∗
    is_llink γ lt lh -∗
    Φ #() -∗
    WP link_queue #lt #lh {{ Φ }}.
  Proof.
    iIntros "#? Hlt Hlh Hll HΦ". iMod steps_lb_0 as "#Hlb". wp_pures.
    awp_apply (link_queue_spec with "Hlt Hlh").
    rewrite /atomic_acc /= difference_empty_L.
    iMod (is_lqueue_link with "[$] Hll") as "H"; first done.
    iApply fupd_mask_intro; [set_solver|]; iIntros "Hclose".
    iDestruct "H" as "[(%vs & $ & H)|H]".
    { iExists false, _, _; iSplit; [done|]. iSplit.
      { (* abort *) iIntros "(Hq & _ & _)". iDestruct "H" as "[_ H]".
        iMod "Hclose" as "_". by iMod ("H" with "Hq") as "$". }
      iIntros "_". iMod "Hclose" as "_". by iDestruct "H" as "[>H _]". }
    iExists true.
    iDestruct "H" as (lh' lt' vs1 vs2) "($ & $ & H)". iSplit.
    { (* abort *) iIntros "(Hq1 & Hq2)". iDestruct "H" as "[_ H]".
      iMod "Hclose" as "_". by iMod ("H" with "Hq1 Hq2") as "$". }
    iIntros "Hq". iDestruct "H" as "[H _]". iMod "Hclose" as "_".
    by iMod ("H" with "Hq").
  Qed.
End lqueue.
