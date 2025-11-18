From iris.algebra Require Import gset auth gmultiset.
From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From iris.bi.lib Require Import atomic.

Local Set Default Proof Using "Type*".

Definition pairing `{Countable A} (L : gmap A (A * bool)) :=
  ∀ (a b : A) (s : bool), L !! a = Some (b, s) → L !! b = Some (a, negb s).

Section pairing.
  Context `{Countable A}.
  Implicit Types a : A.
  Implicit Types L : gmap A (A * bool).

  Lemma pairing_get L a:
    pairing L →
    a ∈ dom L →
    ∃ b s, L !! a = Some (b, s) ∧ L !! b = Some (a, negb s) ∧ a ≠ b.
  Proof.
    unfold pairing. intros Hpair [[b s] Hlookup]%elem_of_dom.
    destruct s; naive_solver.
  Qed.

  Lemma pairing_empty : pairing (∅ : gmap A (A * bool)).
  Proof. done. Qed.

  Lemma pairing_singleton a b s :
    a ≠ b →
    pairing ({[a := (b, s); b := (a, negb s)]}).
  Proof.
    intros ? a' b' s'. rewrite !lookup_insert_Some !lookup_empty.
    destruct s, s'; naive_solver.
  Qed.

  Lemma pairing_join L L' :
    pairing L →
    pairing L' →
    L ##ₘ L' →
    pairing (L ∪ L').
  Proof.
    unfold pairing. intros ??? a b s.
    rewrite !lookup_union_Some //. naive_solver.
  Qed.

  Lemma pairing_extend L a b :
    pairing L →
    a ≠ b →
    a ∉ dom L →
    b ∉ dom L →
    pairing ({[a := (b, true); b := (a, false)]} ∪ L).
  Proof.
    intros Hpairing Hne Ha Hb. apply pairing_join.
    - by apply pairing_singleton.
    - done.
    - rewrite map_disjoint_dom. set_solver.
  Qed.

  Lemma pairing_split L L' :
    pairing L →
    pairing L' →
    L' ⊆ L →
    pairing (L ∖ L').
  Proof.
    rewrite /pairing map_subseteq_spec. intros ??? a b s.
    rewrite !lookup_difference_Some. destruct (L' !! b) eqn:?; naive_solver.
  Qed.
End pairing.

Class PairPred {Σ A} (R : A → A → iProp Σ) := {
  pairpred_irr a a' : R a a' -∗ ⌜a ≠ a'⌝;
  pairpred_sym a b : R a b ⊣⊢ R b a;
  pairpred_unique a b b' : R a b -∗ R a b' -∗ False;
}.

Class pairingG Σ A `{Countable A} := {
  #[local] paitingG_inG :: inG Σ (auth (gset_disj A))
}.
Definition pairingΣ A `{Countable A} :=
  #[ GFunctor (authR (gset_disj A)) ].
Global Instance subG_pairingΣ {Σ} `{Countable A} :
  subG (pairingΣ A) Σ → pairingG Σ A.
Proof. solve_inG. Qed.

Definition pairing_resources `{Countable A, !invGS Σ}
    (R : A → A → iProp Σ) (L : gset A) : iProp Σ :=
  ∃ M,
    ⌜ L = dom M ⌝ ∗
    ⌜ pairing M ⌝ ∗
    [∗ map] a ↦ bs ∈ M, if bs.2 : bool then R a bs.1 else True.

Record pairing_inv_name := PairingInvName { dom_name : gname }.

(* The `set_auth γ L` token in the paper is modeled using the
`own γ.(dom_name) (● (GSet L))` ghost state in the Coq formalization. *)
Definition pairing_inv `{pairingG Σ A, invGS Σ}
    (R : A → A → iProp Σ) (γ : pairing_inv_name) : iProp Σ :=
  ∃ L : gset A,
    own γ.(dom_name) (● (GSet L)) ∗
    pairing_resources R L.

Definition pairing_ctx `{pairingG Σ A, invGS Σ}
    (R : A → A → iProp Σ) (N : namespace) (γ : pairing_inv_name) : iProp Σ :=
  inv N (pairing_inv R γ).

(* The `set_own γ a` token in the paper is modeled using the
`own γ.(dom_name) (◯ (GSet {[ a ]}))` ghost state in the Coq formalization. *)
Definition is_pairing_element `{pairingG Σ A}
    (γ : pairing_inv_name) (a : A) : iProp Σ :=
  own γ.(dom_name) (◯ (GSet {[ a ]})).

Section pairing_inv.
  Context `{pairingG Σ A, invGS Σ, !@PairPred Σ A R}.

  Local Lemma gset_frag_included γ X Y :
    own γ (● (GSet X)) -∗ own γ (◯ (GSet Y)) -∗ ⌜Y ⊆ X⌝.
  Proof.
    iIntros "H● H◯". iCombine "H● H◯" gives %?%auth_both_valid_discrete.
    iPureIntro. set_solver.
  Qed.

  Lemma gset_frag_disj γ X Y :
    own γ (◯ (GSet X)) -∗ own γ (◯ (GSet Y)) -∗ ⌜ X ## Y ⌝.
  Proof.
    iIntros "H◯1 H◯2". iCombine "H◯1 H◯2" gives %Hval.
    rewrite auth_frag_op_valid in Hval.
    by apply gset_disj_valid_op in Hval.
  Qed.

  Local Lemma pairing_resources_notin'  L a b :
    R a b -∗ pairing_resources R L -∗ ⌜ a ∉ L ⌝.
  Proof.
    iIntros "HR (%M & -> & %Hpair & Hres)".
    destruct (decide (a ∈ dom M)) as [Hin|Hnin]; [|done].
    apply pairing_get in Hin as (b' & s & Ha & Hb & Hne); [|done].
    destruct s; simpl.
    - iDestruct (big_sepM_lookup with "Hres") as "H"; first apply Ha.
      simpl.
      iDestruct (pairpred_unique with "HR H") as %[].
    - iDestruct (big_sepM_lookup with "Hres") as "H"; first apply Hb.
      simpl.
      iDestruct (pairpred_sym with "H") as "H".
      iDestruct (pairpred_unique with "HR H") as %[].
  Qed.

  Lemma pairing_resources_notin L a b :
    R a b -∗ pairing_resources R L -∗ ⌜{[ a; b ]} ## L⌝.
  Proof.
    iIntros "HR Hres".
    iDestruct (pairing_resources_notin' with "[$] [$]") as %Hnin.
    iDestruct (pairpred_sym with "HR") as "HR".
    iDestruct (pairing_resources_notin' with "[$] [$]") as %Hnin'.
    iPureIntro. set_solver.
  Qed.

  Lemma pairing_resources_add L a b :
    R a b -∗
    pairing_resources R L -∗
    pairing_resources R (L ∪ {[ a; b ]}).
  Proof.
    iIntros "HR Hres".
    iDestruct (pairpred_irr with "HR") as %Hne.
    iDestruct (pairing_resources_notin with "[$] [$]") as %Hnin.
    iDestruct "Hres" as (M -> Hpair) "Hres".
    iExists ({[a := (b, true); b := (a, false)]} ∪ M).
    assert ({[a := (b, true); b := (a, false)]} ##ₘ M) as Hdis'.
    { apply map_disjoint_dom; set_solver. }
    repeat iSplit.
    - iPureIntro. set_solver.
    - iPureIntro. apply pairing_join; try done.
      by apply pairing_singleton.
    - iApply big_sepM_union; first done.
      iFrame.
      iApply big_sepM_insert.
      { by rewrite lookup_insert_ne ?lookup_empty. }
      iFrame; iApply big_sepM_insert.
      { by rewrite lookup_empty. }
      iSplitR; first done.
      by iApply big_sepM_empty.
  Qed.

  Lemma pairing_resources_remove L a :
    a ∈ L →
    pairing_resources R L -∗
    ∃ b, ⌜ b ∈ L ⌝ ∗ R a b ∗ pairing_resources R (L ∖ {[ a; b ]}).
  Proof.
    iIntros (Hain) "(%M & -> & %HpairM & Hres)".
    apply pairing_get in Hain as (b & s & HMa & HMb & Hne); [|done].
    iExists b.
    assert ({[a := (b, s); b := (a, negb s)]} ⊆ M).
    { apply map_subseteq_spec. intros a' bs'.
      rewrite !lookup_insert_Some lookup_empty. naive_solver. }
    assert ({[a := (b, s); b := (a, negb s)]} ∪
      M ∖ {[a := (b, s); b := (a, negb s)]} = M) as <-.
    { by apply map_difference_union. }
    iDestruct (big_sepM_union with "Hres") as "[Hres Hres']".
    { apply map_disjoint_dom. set_solver. }
    iSplitR; first (iPureIntro; set_solver).
    iSplitL "Hres".
    - iDestruct (big_sepM_insert with "Hres") as "[Hab Hres]".
      { by rewrite lookup_insert_ne ?lookup_empty. }
      iDestruct (big_sepM_insert with "Hres") as "[Hba _]"; first done.
      destruct s; simpl.
      + by iFrame.
      + by iApply pairpred_sym.
    - iExists (M ∖ {[a := (b, s); b := (a, negb s)]}).
      iSplitR.
      { iPureIntro. rewrite !dom_union_L. set_solver. }
      iSplitR.
      { iPureIntro. apply pairing_split; try done.
        by apply pairing_singleton. }
      destruct s; eauto with iFrame.
  Qed.

  Lemma pairing_ctx_alloc N E :
    ⊢ |={E}=> ∃ γ, pairing_ctx R N γ.
  Proof.
    iMod (own_alloc (● (GSet ∅))) as (γ) "H●".
    { by apply auth_auth_valid. }
    iExists (PairingInvName γ).
    iApply inv_alloc. iFrame. iExists ∅. auto.
  Qed.

  (* As the pairing invariant is obtained by opening the invariant in the
     pairing context `pairing_ctx`, it has a later. As laters and updates
     ={E}=∗ do not commute, these laters must be added to the rules. *)
  Lemma pairing_new E γ a b :
    ▷ pairing_inv R γ -∗
    ▷ R a b ={E}=∗
    is_pairing_element γ a ∗ is_pairing_element γ b ∗ ▷ pairing_inv R γ.
  Proof.
    iIntros "(%L & >H● & Hres) HR".

    iAssert (R a b -∗ R a b ∗ ⌜ a ≠ b ⌝)%I as "H".
    { iIntros "HR". iDestruct (pairpred_irr with "HR") as %Hne'. by iFrame. }
    iDestruct ("H" with "HR") as "(HR & >%Hne)". iClear "H".

    destruct (decide (a ∈ L)).
    { iDestruct (pairing_resources_remove with "Hres") as "H"; first done.
      iMod (bi.later_exist_except_0 with "H") as "(%b' & ? & Hab' & _)".
      iDestruct (pairpred_unique (R:=R) with "HR Hab'") as ">[]". }
    destruct (decide (b ∈ L)).
    { iDestruct (pairpred_sym (R:=R) with "HR") as "HR".
      iDestruct (pairing_resources_remove with "Hres") as "H"; first done.
      iMod (bi.later_exist_except_0 with "H") as "(%b' & ? & Hab' & _)".
      iDestruct (pairpred_unique (R:=R) with "HR Hab'") as ">[]". }
    assert ({[a; b]} ## L) as Hdis by set_solver.
    iMod (own_unit (auth (gset_disj A)) (dom_name γ)) as "H◯a".
    iMod (own_unit (auth (gset_disj A)) (dom_name γ)) as "H◯b".

    iMod (own_update_2 with "H● H◯a") as "[H● H◯a]".
    { apply auth_update, (gset_disj_alloc_empty_local_update _ {[ a ]}).
      set_solver. }

    iMod (own_update_2 with "H● H◯b") as "[H● H◯b]".
    { apply auth_update, (gset_disj_alloc_empty_local_update _ {[ b ]}).
      set_solver. }

    replace ({[b]} ∪ ({[a]} ∪ L)) with (L ∪ {[a ; b]}) by set_solver.
    iModIntro.
    iSplitL "H◯a"; first done.
    iSplitL "H◯b"; first done.
    iNext.
    iExists (L ∪ {[a ; b]}). iFrame.
    by iApply (pairing_resources_add with "[$]").
  Qed.

  Lemma pairing_update E γ a :
    ▷ pairing_inv R γ -∗
    is_pairing_element γ a ={E}=∗
    ∃ b, ▷ R a b ∗ (▷ R a b ={E}=∗ is_pairing_element γ a ∗ ▷ pairing_inv R γ).
  Proof.
    iIntros "(%L & >H● & Hres) H◯a". unfold is_pairing_element.
    iDestruct (gset_frag_included with "H● H◯a") as %?%singleton_subseteq_l.
    iDestruct (pairing_resources_remove with "Hres") as "H"; first done.
    iMod (bi.later_exist_except_0 with "H") as (b) "(>%Hin & HR & Hres)".
    iModIntro; iExists b.
    iFrame. iIntros "HR".
    iDestruct (pairing_resources_add with "HR Hres") as "Hres".
    replace (L ∖ {[a; b]} ∪ {[a; b]}) with L.
    2: { rewrite difference_union_L. set_solver. }
    by iFrame.
  Qed.

  Lemma pairing_update_2 E γ b c :
    ▷ pairing_inv R γ -∗
    is_pairing_element γ b ∗
    is_pairing_element γ c ={E}=∗
    (∃ a d, ▷ R b a ∗ ▷ R c d ∗
      (▷ R b a -∗ ▷ R c d ={E}=∗ is_pairing_element γ b ∗ is_pairing_element γ c ∗ ▷ pairing_inv R γ)
      ∧ (▷ R a d ={E}=∗ ▷ pairing_inv R γ)) ∨
    (▷ R b c ∗
      (▷ R b c ={E}=∗ is_pairing_element γ b ∗ is_pairing_element γ c ∗ ▷ pairing_inv R γ)
      ∧ (True ={E}=∗ ▷ pairing_inv R γ)).
  Proof.
    iIntros "(%L & >H● & Hres) (H◯b & H◯c)".
    iDestruct (gset_frag_included with "H● H◯b") as %Hbin%singleton_subseteq_l.
    iDestruct (gset_frag_included with "H● H◯c") as %Hcin%singleton_subseteq_l.

    iDestruct (pairing_resources_remove with "Hres") as "H"; first apply Hbin.
    iMod (bi.later_exist_except_0 with "H") as (a) "(>%Hin & HR & Hres)".

    iAssert (∀ a b, R a b -∗ R a b ∗ ⌜ a ≠ b ⌝)%I as "Hirr".
    { iIntros (a' b') "HR". iDestruct (pairpred_irr with "HR") as %Hne'. by iFrame. }
    iDestruct ("Hirr" with "HR") as "(HR & >%Hne)".

    destruct (decide (a = c)).
    - iModIntro; iRight; simplify_eq.
      iFrame "HR". iSplit.
      + iIntros "HR".
        iDestruct (pairing_resources_add with "HR Hres") as "Hres".
        replace (L ∖ {[b; c]} ∪ {[b; c]}) with L.
        2: { rewrite difference_union_L. set_solver. }
        by iFrame.
      + iIntros.
        iMod (own_update_2 with "H● H◯b") as "H●".
        { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
        iMod (own_update_2 with "H● H◯c") as "H●".
        { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
        replace (L ∖ {[b]} ∖ {[c]}) with (L ∖ {[b; c]}) by set_solver.
        by iFrame.
    - iDestruct (gset_frag_disj with "H◯b H◯c") as %Hdisj.
      assert (c ∈ L ∖ {[b; a]}) by set_solver.
      iDestruct (pairing_resources_remove with "Hres") as "H'"; first done.
      iMod (bi.later_exist_except_0 with "H'") as (d) "(>%Hin' & HR' & Hres')".
      iDestruct ("Hirr" with "HR'") as "(HR' & >%Hne')".
      iModIntro.
      iLeft. iExists a, d. iFrame "HR HR'".
      iSplit.
      + iIntros "HR HR'".
        iDestruct (pairing_resources_add with "HR Hres'") as "Hres".
        iDestruct (pairing_resources_add with "HR' Hres") as "Hres".
        replace (L ∖ {[b; a]} ∖ {[c; d]} ∪ {[b; a]} ∪ {[c; d]}) with L.
        2: { rewrite difference_difference_l_L.
             rewrite <-(assoc_L (∪)).
             rewrite difference_union_L.
             set_solver. }
        by iFrame.
      + iIntros "HR".
        iDestruct (pairing_resources_add with "HR Hres'") as "Hres".
        iMod (own_update_2 with "H● H◯b") as "H●".
        { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
        iMod (own_update_2 with "H● H◯c") as "H●".
        { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
        replace (L ∖ {[b]} ∖ {[c]}) with (L ∖ {[b; c]}) by set_solver.

        iModIntro. iFrame.
        replace (L ∖ {[b; a]} ∖ {[c; d]} ∪ {[a; d]})
          with (L ∖ {[b; c]}); first done.
        { rewrite !difference_difference_l_L.
          replace ({[b; a]} ∪ {[c; d]} : gset A)
            with ({[b; c]} ∪ {[a; d]} : gset A) by set_solver.
          rewrite <-(difference_difference_l_L _ {[b; c]}).
          rewrite difference_union_L.
          rewrite <-(subseteq_union_1_L {[a; d]} (L ∖ {[b; c]})); [set_solver|].
          set_solver. }
Qed.

End pairing_inv.
