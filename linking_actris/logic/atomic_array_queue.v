From iris.base_logic Require Import lib.ghost_var lib.mono_nat.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export notation proofmode.
From iris.heap_lang Require Import array.
From linking_actris.logic Require Export time_receipts.
From iris.prelude Require Import options.

Local Definition START := 0.
Local Definition END := 1.
Local Definition NEXT := 2.
Local Definition BUFFER := 3.
Local Definition NODESIZE := 1024.
Local Definition SIZE := NODESIZE - BUFFER.
Opaque NODESIZE.

(* This file contains an alternative implementation of queues using arrays that
   has the same specification as the linked list variant in
   `atomic_simple_queue`.

   The queue consists of multiple arrays of length `NODESIZE`, where each array
   contains a START and END index describing the segment of the array filled
   with values, as well as a NEXT pointer which points to the next array when
   either the current array is full or the queue is linked.

   Below is an example queue segment containing the values 4 and 2.

                         ↓ START = 3
   ┌───┬───┬───┬───┬───┬───┬───┬───┬─╌╌─┐
   │ 3 │ 5 │   │ x │ x │ 4 │ 2 │   │    │
   └───┴───┴───┴───┴───┴───┴───┴───┴─╌╌─┘
             ↑ NEXT = null       ↑ END = 5
  
  When an array is full, a new array is allocated and the `NEXT` index in the
  current array is set to a pointer to the new array. When linking, we
  similarly set the NEXT pointer to the first array of the other queue.

  The dequeue handle of the queue points to the first array making up the
  queue, whereas the enqueue handle points to the last array.

  Note that when dequeueing we have to consider 3 cases:
  - If START < END we can dequeue the next value in this array.
  - If START = END and NEXT ≠ nill then we move to the next array and coninue
    dequeueing from there.
  - If START = END and NEXT = nill then the queue was empty, so we wait for the
    next element by trying to dequeue again.
  
  Note that due to linking, the current array may not be completely filled
  before setting the NEXT array, hence we have to check the NEXT pointer when
  the current array has no more values, even if it is not yet full.
*)

Lemma size_pos : 0 < SIZE.
Proof. compute_done. Qed.
Lemma nodesize_eq : NODESIZE = BUFFER + SIZE.
Proof. done. Qed.

Definition new_queue : val := λ: <>,
  let: "node" := AllocN #NODESIZE #() in
  ("node" +ₗ #START) <- #0;;
  ("node" +ₗ #END) <- #0;;
  ("node" +ₗ #NEXT) <- NONE;;
  (ref "node", ref "node").

Definition enqueue : val := λ: "t" "x",
  let: "node" := !"t" in
  let: "end" := !("node" +ₗ #END) in
  if: "end" < #SIZE then
    ("node" +ₗ (#BUFFER + "end")) <- "x";;
    ("node" +ₗ #END) <- "end" + #1
  else
    let: "nnode" := AllocN #NODESIZE #() in
    ("nnode" +ₗ #START) <- #0;;
    ("nnode" +ₗ #END) <- #1;;
    ("nnode" +ₗ #NEXT) <- NONE;;
    ("nnode" +ₗ #BUFFER) <- "x";;
    ("node" +ₗ #NEXT) <- SOME "nnode";;
    "t" <- "nnode".

Definition dequeue : val :=
  rec: "dequeue" "h" :=
    let: "node" := !"h" in
    let: "start" := !("node" +ₗ #START) in
    let: "end" := !("node" +ₗ #END) in
    if: "start" < "end" then
      ("node" +ₗ #START) <- "start" + #1;;
      !("node" +ₗ (#BUFFER + "start"))
    else
      match: !("node" +ₗ #NEXT) with
        NONE => "dequeue" "h"
      | SOME "next" =>
         (* Note that as `end` and `next` are not read at the same time,
            another thread could have enqueued (incrementing `end`) and then
            linked (setting `next`) before we read `next` here. Hence we need
            to recheck `end` here to verify no elements were enqueued to this
            array in the meantime. *)
         let: "end" := !("node" +ₗ #END) in
         if: "start" < "end" then
           ("node" +ₗ #START) <- "start" + #1;;
           !("node" +ₗ (#BUFFER + "start"))
         else
           "h" <- "next";;
           "dequeue" "h"
       end.

Definition link_queue : val := λ: "t" "h",
  let: "nodet" := !"t" in
  let: "nodeh" := !"h" in
  ("nodet" +ₗ #NEXT) <- SOME "nodeh";;
  #().

Class queueG Σ := {
  #[local] queueG_mono_nat_inG :: mono_natG Σ;
  #[local] queueG_enqueue_inG :: ghost_varG Σ loc
}.
Definition queueΣ : gFunctors := #[mono_natΣ; ghost_varΣ loc].
Global Instance subG_queueΣ {Σ} : subG queueΣ Σ → queueG Σ.
Proof. solve_inG. Qed.

Fixpoint is_queue_list `{heapGS Σ, queueG Σ}
    (is_start : bool) (lh lt : loc) (vss : list (list val)) : iProp Σ :=
  match vss with
  | [] => False
  | vs :: vss => ∃ (γlh : gname) (start : nat),
    let is_end := bool_decide (vss = []) in
    ⌜ length vs ≤ SIZE ⌝ ∗
    (lh +ₗ START) ↦{#if is_start then (1/2)%Qp else 1%Qp} #start ∗
    (lh +ₗ END) ↦{if is_end then DfracOwn (1/2) else DfracDiscarded}
      #(start + length vs)%nat ∗
    meta lh nroot γlh ∗
    mono_nat_auth_own γlh 1 (start + length vs) ∗
    (if is_end
     then ⌜lh = lt⌝ ∗ (lh +ₗ NEXT) ↦ NONEV
     else ∃ l : loc, (lh +ₗ NEXT) ↦□ SOMEV #l ∗ is_queue_list false l lt vss) ∗
    (lh +ₗ (BUFFER + start)) ↦∗□ vs
  end.

Local Definition is_queue_def `{heapGS Σ, queueG Σ}
    (lhptr ltptr : loc) (vs : list val) : iProp Σ :=
  ∃ (γlt : gname) (vss : list (list val)) (lh lt : loc),
    ⌜ vs = mjoin vss ⌝ ∗
    meta ltptr nroot γlt ∗
    lhptr ↦{#3/4} #lh ∗
    ghost_var γlt (1/2) lt ∗
    is_queue_list true lh lt vss.
Local Definition is_queue_aux : seal (@is_queue_def). Proof. by eexists. Qed.
Definition is_queue := is_queue_aux.(unseal).
Local Definition is_queue_unseal :
  @is_queue = @is_queue_def := is_queue_aux.(seal_eq).
Global Arguments is_queue {Σ _ _} lhptr ltptr vs.

Local Definition enqueue_handle_def `{heapGS Σ, queueG Σ} (ltptr : loc) : iProp Σ :=
  ∃ (γw : gname) (lt : loc) (eend : nat) (uninit : list val),
    ⌜ (eend + length uninit = SIZE)%nat ⌝ ∗
    meta ltptr nroot γw ∗
    ghost_var γw (1/2) lt ∗
    ltptr ↦ #lt ∗
    (lt +ₗ END) ↦{#1/2} #eend ∗
    (lt +ₗ (BUFFER + eend)) ↦∗ uninit.
Local Definition enqueue_handle_aux : seal (@enqueue_handle_def).
Proof. by eexists. Qed.
Definition enqueue_handle := enqueue_handle_aux.(unseal).
Local Definition enqueue_handle_unseal :
  @enqueue_handle = @enqueue_handle_def := enqueue_handle_aux.(seal_eq).
Global Arguments enqueue_handle {Σ _ _} ltptr.

Local Definition dequeue_handle_def `{heapGS Σ, queueG Σ} (lhptr : loc) : iProp Σ :=
  ∃ (lh : loc) (start : nat),
    lhptr ↦{#1/4} #lh ∗
    (lh +ₗ START) ↦{#1/2} #start.
Local Definition dequeue_handle_aux : seal (@dequeue_handle_def).
Proof. by eexists. Qed.
Definition dequeue_handle := dequeue_handle_aux.(unseal).
Local Definition dequeue_handle_unseal :
  @dequeue_handle = @dequeue_handle_def := dequeue_handle_aux.(seal_eq).
Global Arguments dequeue_handle {Σ _ _} lhptr.

Section queue_spec.
  Context `{!heapGS Σ, !queueG Σ}.
  Implicit Types v : val.
  Implicit Types vs : list val.
  Implicit Types vss : list (list val).

  Local Instance is_queue_list_timeless is_start lh lt vss :
    Timeless (is_queue_list is_start lh lt vss).
  Proof.
    revert is_start lh.
    induction vss as [|v vss]; simpl; repeat case_bool_decide; apply _.
  Qed.

  Lemma is_queue_list_start lh lt vss :
    is_queue_list false lh lt vss -∗
    ∃ start : nat, (lh +ₗ START) ↦{#1/2} #start ∗ is_queue_list true lh lt vss.
  Proof.
    iIntros "Hlist". destruct vss as [|vs vss]; simpl; first done.
    by iDestruct "Hlist" as (γlh start' ?) "[[$$] $]".
  Qed.

  Lemma is_queue_list_unstart lh lt vss start :
    is_queue_list true lh lt vss -∗
    (lh +ₗ START) ↦{#1/2} #start -∗
    is_queue_list false lh lt vss.
  Proof.
    iIntros "Hlist Hstart". destruct vss as [|vs vss]; simpl; first done.
    iDestruct "Hlist" as (γlh start' ?) "[Hstart' $]".
    iCombine "Hstart' Hstart" as "Hstart" gives %[_ ?]; simplify_eq/=.
    rewrite dfrac_op_own /= Qp.half_half. by iFrame.
  Qed.

  Lemma is_queue_get_end lh lt vss :
    is_queue_list true lh lt vss -∗
    ∃ dq γlh (eend : nat),
      (lh +ₗ END) ↦{dq} #eend ∗
      meta lh nroot γlh ∗
      mono_nat_lb_own γlh eend ∗
      ((lh +ₗ END) ↦{dq} #eend -∗ is_queue_list true lh lt vss).
  Proof.
    iIntros "Hlist". destruct vss as [|vs vss]; simpl; first done.
    iDestruct "Hlist" as (γlh start ?)
      "(Hstart & $ & #Hmeta & Hmono & Hnext & Hbuf)".
    iDestruct (mono_nat_lb_own_get with "Hmono") as "#Hlb".
    iIntros "{$Hmeta $Hlb} Hend {$Hstart $Hend $Hmeta $Hmono $Hnext $Hbuf} //".
  Qed.

  Lemma is_queue_get_end_persist lh lt vss l :
    is_queue_list true lh lt vss -∗
    (lh +ₗ NEXT) ↦□ InjRV #l -∗
    ∃ (eend : nat), (lh +ₗ END) ↦□ #eend.
  Proof.
    iIntros "Hlist Hnext". destruct vss as [|vs vss]; simpl; first done.
    iDestruct "Hlist" as (γlh start ?)
      "(_ & Hend & _ & _ & Hnext' & _)".
    case_bool_decide; simplify_eq/=; last by eauto.
    iDestruct "Hnext'" as "[_ Hnext']".
    by iCombine "Hnext' Hnext" gives %[_ ?].
  Qed.

  Lemma is_queue_dequeue eend lh lt vss start :
    start < eend →
    is_queue_list true lh lt vss -∗
    (lh +ₗ START) ↦{#1/2} #start -∗
    ((lh +ₗ END) ↦□ #eend ∨ ∃ γlh, meta lh nroot γlh ∗ mono_nat_lb_own γlh eend) ==∗
    ∃ v vs vss',
      ⌜ vss = (v :: vs) :: vss' ⌝ ∗
      (lh +ₗ START) ↦ #start ∗
      (lh +ₗ (BUFFER + start)) ↦□ v ∗
      ((lh +ₗ START) ↦{#1/2} #(start + 1) -∗ is_queue_list true lh lt (vs :: vss')).
  Proof.
    iIntros (?) "Hlist Hstart Hend'".
    destruct vss as [|vs vss]; simpl; first done.
    iDestruct "Hlist" as (γlh' start' ?)
      "(Hstart' & Hend & #Hmeta & Hmono & Hnext & Hbuf)".
    iCombine "Hstart' Hstart" as "Hstart" gives %[_ ?]; simplify_eq/=.
    rewrite dfrac_op_own /= Qp.half_half.
    destruct vs as [|v vs]; simplify_eq/=.
    - iDestruct "Hend'" as "[Hend'|(%γlh & Hmeta' & Hlb)]".
      + iCombine "Hend' Hend" gives %[_ ?]; simplify_eq/=. lia.
      + iDestruct (meta_agree with "Hmeta' Hmeta") as "->".
        iDestruct (mono_nat_lb_own_valid with "Hmono Hlb") as %[_ ?]. lia.
    - iExists v, vs, vss.
      iDestruct (array_cons with "Hbuf") as "[Hv Hbuf]".
      iMod (pointsto_persist with "Hv") as "$".
      iIntros "!> {$Hstart}". iSplit; [done|]. iIntros "Hstart".
      rewrite Loc.add_assoc -Nat.add_succ_comm -Z.add_assoc.
      replace (start + 1)%Z with (Z.of_nat (S start)) by lia.
      auto with lia iFrame.
  Qed.

  Lemma is_queue_dequeue_get_next lh lt vss :
    is_queue_list true lh lt vss -∗
    ((lh +ₗ NEXT) ↦ NONEV ∗
     ((lh +ₗ NEXT) ↦ NONEV -∗ is_queue_list true lh lt vss))
    ∨
    (∃ l : loc, (lh +ₗ NEXT) ↦□ SOMEV #l ∗ is_queue_list true lh lt vss).
  Proof.
    iIntros "Hlist". destruct vss as [|vs vss]; simpl; first done.
    iDestruct "Hlist" as (γlh start ?)
      "(Hstart & Hend & #Hmeta & Hmono & Hnext & Hbuf)".
    case_bool_decide; simplify_eq/=.
    - iLeft. iDestruct "Hnext" as (->) "$". auto 10 with iFrame.
    - iRight. iDestruct "Hnext" as (l) "[#? Hlist]". auto 10 with iFrame.
  Qed.

  Lemma is_queue_dequeue_node lh lt vss start eend (l : loc) :
    eend ≤ start →
    is_queue_list true lh lt vss -∗
    (lh +ₗ START) ↦{#1/2} #start -∗
    (lh +ₗ END) ↦□ #eend -∗
    (lh +ₗ NEXT) ↦□ SOMEV #l -∗
    ∃ vss' (n : nat),
      ⌜ vss = [] :: vss' ⌝ ∗
      (l +ₗ START) ↦{#1/2} #n ∗
      is_queue_list true l lt vss'.
  Proof.
    iIntros (?) "Hlist Hstart #Hend #Hnext".
    destruct vss as [|vs vss]; simpl; first done.
    iDestruct "Hlist" as (γlh' start' ?)
      "(Hstart' & Hend' & #Hmeta' & Hmono & Hnext' & Hbuf)".
    iCombine "Hstart' Hstart" as "Hstart" gives %[_ ?]; simplify_eq/=.
    rewrite dfrac_op_own /= Qp.half_half.
    case_bool_decide; simplify_eq/=.
    { iDestruct "Hnext'" as "[_ Hnext']".
      by iCombine "Hnext' Hnext" gives %[_ ?]. }
    iDestruct "Hnext'" as (l') "[#Hnext' Hlist]".
    iCombine "Hnext' Hnext" gives %[_ ?]; simplify_eq/=.
    iCombine "Hend' Hend" gives %[_ ?]; simplify_eq/=.
    destruct vs; simplify_eq/=; last lia.
    by iDestruct (is_queue_list_start with "[$]") as (?) "[$$]".
  Qed.

  Lemma is_queue_list_enqueue_elem is_start lh lt vss eend :
    eend < SIZE →
    is_queue_list is_start lh lt vss -∗
    (lt +ₗ END) ↦{#1/2} #eend -∗
    ∃ vs vss',
      ⌜ vss = vss' ++ [vs] ⌝ ∗
      (lt +ₗ END) ↦{#1} #eend ∗
      (∀ v,
         (lt +ₗ END) ↦{#1/2} #(S eend) -∗
         (lt +ₗ (BUFFER + eend)) ↦□ v ==∗
         is_queue_list is_start lh lt (vss' ++ [vs ++ [v]])).
  Proof.
    iIntros (?) "Hlist Hend".
    iInduction vss as [|vs vss] "IH" forall (is_start lh); simpl; first done.
    iDestruct "Hlist" as (γlh start ?)
      "(Hstart & Hend' & Hmeta & Hmono & Hnext & Hbuf)".
    case_bool_decide; simplify_eq/=.
    - iDestruct "Hnext" as (->) "Hnext".
      iCombine "Hend' Hend" as "Hend" gives %[_ ?]; simplify_eq/=.
      rewrite dfrac_op_own /= Qp.half_half.
      iExists vs, []. iSplit; [done|]. iIntros "{$Hend}" (v) "Hend Hv /=".
      iExists γlh, start.
      rewrite app_length /= !Nat.add_1_r !Nat.add_succ_r.
      iEval (replace (BUFFER + (start + length vs)%nat)%Z
        with ((BUFFER + start) + length vs)%Z by lia) in "Hv".
      rewrite array_app array_singleton Loc.add_assoc /=.
      iMod (mono_nat_own_update (S (start + length vs)) with "Hmono")
        as "[Hmono _]"; first lia. auto with lia iFrame.
    - iDestruct "Hnext" as (l) "[#Hnext Hlist]".
      iDestruct ("IH" with "[$] [$]") as (vs' vss' ->) "[$ Hlist]".
      iExists _, (_ :: _); iSplit; [done|].
      iIntros (v) "Hend Hv /=".
      iMod ("Hlist" with "[$] [$]").
      iFrame. rewrite bool_decide_false; last by destruct vss'.
      auto with iFrame.
  Qed.

  Lemma is_queue_list_enqueue_node is_start lh lt vss eend :
    is_queue_list is_start lh lt vss -∗
    (lt +ₗ END) ↦{#1/2} #eend -∗
      (lt +ₗ NEXT) ↦ NONEV ∗
      (∀ (l : loc) v,
         (lt +ₗ NEXT) ↦ SOMEV #l -∗
         meta_token l ⊤ -∗
         (l +ₗ START) ↦ #0 -∗
         (l +ₗ END) ↦{#1/2} #1 -∗
         (l +ₗ NEXT) ↦ NONEV -∗
         (l +ₗ BUFFER) ↦□ v ==∗
         is_queue_list is_start lh l (vss ++ [[v]])).
  Proof.
    iIntros "Hlist Hend".
    iInduction vss as [|vs vss] "IH" forall (is_start lh); simpl; first done.
    iDestruct "Hlist" as (γlh start ?)
      "(Hstart & Hend' & #Hmeta & Hmono & Hnext & Hbuf)".
    case_bool_decide; simplify_eq/=.
    - iDestruct "Hnext" as (->) "$".
      iCombine "Hend' Hend" as "Hend" gives %[_ ?]; simplify_eq/=.
      rewrite dfrac_op_own /= Qp.half_half.
      iIntros (l v) "Hnext Hlmeta Hstart' Hend' Hnext' #Hv".
      iMod (mono_nat_own_alloc 1) as (γl) "[Hγl _]".
      iMod (meta_set _ l γl nroot with "Hlmeta") as "$"; first done.
      iMod (pointsto_persist with "Hend") as "$".
      iMod (pointsto_persist with "Hnext") as "$".
      iModIntro. iFrame "Hstart Hmeta Hmono Hbuf". iSplit; [done|].
      iExists 0. rewrite Z.add_0_r array_singleton.
      pose proof size_pos. auto with iFrame lia.
    - iDestruct "Hnext" as (l) "[#Hnext Hlist]".
      iDestruct ("IH" with "[$] [$]") as "[$ Hlist]".
      iIntros (l' v) "Hnext' Hlmeta Hstart' Hend'' Hnext'' Hv".
      iMod ("Hlist" with "[$] [$] [$] [$] [$] [$]") as "Hlist".
      rewrite bool_decide_false; last by destruct vss.
      auto 10 with iFrame.
  Qed.

  Lemma is_queue_list_link is_start lh1 lt1 vss1 : 
    is_queue_list is_start lh1 lt1 vss1 -∗
    (lt1 +ₗ NEXT) ↦ NONEV ∗
    (∀ (lh2 lt2 : loc) vss2 start,
      (lt1 +ₗ NEXT) ↦ SOMEV #lh2 -∗
      (lh2 +ₗ START) ↦{#1/2} #start -∗
      is_queue_list true lh2 lt2 vss2 ==∗
      is_queue_list is_start lh1 lt2 (vss1 ++ vss2)).
  Proof.
    iIntros "Hlist".
    iInduction vss1 as [|vs1 vss1] "IH" forall (is_start lh1); simpl; first done.
    iDestruct "Hlist" as (γlh start ?)
      "(Hstart & Hend & Hmeta & Hmono & Hnext & Hbuf)".
    case_bool_decide; simplify_eq.
    - iDestruct "Hnext" as (->) "$".
      iIntros (lh2 lt2 vss2 start2) "Hnext Hstart2 Hlist".
      iFrame. case_bool_decide; simplify_eq/=; first done.
      iDestruct (is_queue_list_unstart with "Hlist Hstart2") as "$".
      iMod (pointsto_persist with "Hend") as "$".
      by iMod (pointsto_persist with "Hnext") as "$".
    - iDestruct "Hnext" as (l) "[Hnext Hlist]".
      iDestruct ("IH" with "Hlist") as "[$ Hlist]".
      iIntros (lh2 lt2 vss2 start2) "Hnext2 Hstart2 Hlist2".
      rewrite bool_decide_false; last by destruct vss1.
      iMod ("Hlist" with "[$] [$] [$]") as "?". auto with iFrame.
  Qed.

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

  Lemma new_queue_spec :
    {{{ True }}}
      new_queue #()
    {{{ lhptr ltptr, RET (#lhptr, #ltptr);
        is_queue lhptr ltptr [] ∗
        dequeue_handle lhptr ∗ enqueue_handle ltptr }}}.
  Proof.
    iIntros (Φ) "_ HΦ". pose proof size_pos.
    rewrite is_queue_unseal enqueue_handle_unseal dequeue_handle_unseal.
    wp_lam. wp_apply (wp_allocN with "[//]").
    { rewrite nodesize_eq /=; lia. }
    iIntros (l) "[Hl Hmeta]". rewrite nodesize_eq /= Nat2Z.id /= Loc.add_0.
    iDestruct "Hmeta" as "[Hlmeta _]".
    wp_pures.
    iAssert ((l +ₗ START) ↦ #() ∗ (l +ₗ END) ↦ #() ∗ (l +ₗ NEXT) ↦ #() ∗
      (l +ₗ BUFFER) ↦∗ replicate SIZE #())%I
      with "[Hl]" as "(Hstart & Hend & Hnext & Hbuf)".
    { iDestruct (array_cons with "Hl") as "[Hl0 Hl]".
      iDestruct (array_cons with "Hl") as "[Hl1 Hl]".
      iDestruct (array_cons with "Hl") as "[Hl2 Hl]".
      rewrite !Loc.add_assoc Loc.add_0. iFrame. }
    wp_store. wp_store. wp_store.
    iDestruct "Hstart" as "[Hstart Hstart']". iDestruct "Hend" as "[Hend Hend']".

    wp_apply wp_alloc as (ltptr) "[Hltptr Hltmeta]"; first done.
    wp_alloc lhptr as "Hlhptr".
    iEval (rewrite -Qp.three_quarter_quarter) in "Hlhptr".
    iDestruct "Hlhptr" as "[Hlhptr Hlhptr']".

    iMod (ghost_var_alloc l) as (γw) "[Hγe Hγe']".
    iMod (meta_set _ ltptr γw nroot with "Hltmeta") as "#Hltmeta"; first done.

    iMod (mono_nat_own_alloc 0) as (γl) "[Hγl _]".
    iMod (meta_set _ l γl nroot with "Hlmeta") as "#Hlmeta"; first done.

    wp_pures. iModIntro. iApply "HΦ". iSplitL "Hstart Hend Hnext Hlhptr Hγe Hγl".
    { iExists γw, [[]], l, l. iFrame "Hltmeta Hlhptr Hγe". iSplit; [done|].
      iExists γl, 0. rewrite /= array_nil. iFrame; auto with lia. }
    iSplitL "Hstart' Hlhptr'".
    { iExists _, 0. by iFrame. }
    iExists _, _, 0, (replicate SIZE #()).
    rewrite replicate_length. auto with iFrame.
  Qed.

  Lemma dequeue_spec lhptr :
    dequeue_handle lhptr -∗
    <<{ ∀∀ ltptr vs, is_queue lhptr ltptr vs }>>
      dequeue #lhptr @ ∅
    <<{ ∃∃ v vs', ⌜vs = v :: vs'⌝ ∗ £3 ∗ is_queue lhptr ltptr vs'
      | RET v; dequeue_handle lhptr }>>.
  Proof.
    iIntros "Hh %Φ AU". rewrite is_queue_unseal dequeue_handle_unseal.
    iLöb as "IH". wp_rec.
    iDestruct "Hh" as (lh start) "[Hlhptr Hstart]".
    do 2 wp_load.
    wp_pure credit:"H£1"; wp_pure credit:"H£2"; wp_pure credit:"H£3".
    iCombine "H£1 H£2 H£3" as "H£"; simpl.

    wp_bind (!_)%E.
    iMod "AU" as (ltptr vs) "[Hq Hcl]".
    iDestruct "Hq" as (γw vss lh' lt' ->) "(Hmeta' & Hlhptr' & Hγe' & Hlist)".
    iDestruct (is_queue_get_end with "Hlist")
      as (dq γlt eend) "(Hend & #Hlb & #Hlmeta & Hlist)".
    iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
    wp_load.
    iDestruct ("Hlist" with "[$]") as "Hlist".
    iDestruct "Hcl" as "[Hcl _]".
    iMod ("Hcl" with "[$Hmeta' $Hγe' $Hlist $Hlhptr' //]") as "AU".
    clear dq ltptr γw vss lt'.

    iModIntro. wp_pures. case_bool_decide as Hend; wp_pures.
    { wp_bind (_ <- _)%E. iMod "AU" as (ltptr vs) "[Hq Hcl]".
      iDestruct "Hq" as (γw vss lh' lt' ->) "(Hmeta' & Hlhptr' & Hγe' & Hlist)".
      iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
      iMod (is_queue_dequeue eend with "Hlist [$] []")
        as (v vs vss' ->) "(Hstart & #Hv & Hlist)"; [lia|by auto|].
      wp_store. iDestruct "Hstart" as "[Hstart Hstart']".
      iDestruct ("Hlist" with "Hstart'") as "Hlist".
      iDestruct "Hcl" as "[_ Hcl]".
      iMod ("Hcl" with "[-Hlhptr Hstart]") as "HΦ"; first by iFrame.
      iModIntro. wp_load. iApply "HΦ".
      replace (start + 1)%Z with (Z.of_nat (S start)) by lia. by iFrame. }

    wp_bind (!_)%E.
    iMod "AU" as (ltptr vs) "[Hq Hcl]".
    iDestruct "Hq" as (γw vss lh' lt' ->) "(Hmeta' & Hlhptr' & Hγe' & Hlist)".
    iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
    iDestruct (is_queue_dequeue_get_next with "Hlist")
      as "[[Hnext Hlist]|(%l & #Hnext & Hlist)]".
    { wp_load.
      iDestruct ("Hlist" with "Hnext") as "Hlist".
      iDestruct "Hcl" as "[Hcl _]".
      iMod ("Hcl" with "[$Hmeta' $Hγe' $Hlist $Hlhptr' //]") as "AU".
      iModIntro. wp_pures. iApply ("IH" with "[$] AU"). }

    wp_load.
    iDestruct "Hcl" as "[Hcl _]".
    iMod ("Hcl" with "[$Hmeta' $Hγe' $Hlist $Hlhptr' //]") as "AU".
    clear ltptr γw vss lt'. iModIntro. wp_pures.
    iClear (eend Hend γlt) "Hlb Hlmeta".

    wp_bind (!_)%E.
    iMod "AU" as (ltptr vs) "[Hq Hcl]".
    iDestruct "Hq" as (γw vss lh' lt' ->) "(Hmeta' & Hlhptr' & Hγe' & Hlist)".
    iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
    iDestruct (is_queue_get_end_persist with "Hlist Hnext") as (eend) "#Hend".
    wp_load.
    iDestruct "Hcl" as "[Hcl _]".
    iMod ("Hcl" with "[$Hmeta' $Hγe' $Hlist $Hlhptr' //]") as "AU".
    clear ltptr γw vss lt'.

    iModIntro. wp_pures. case_bool_decide as Hend; wp_pures.
    { (* A new value was enqueued to this array in the meantime. *)
      wp_bind (_ <- _)%E. iMod "AU" as (ltptr vs) "[Hq Hcl]".
      iDestruct "Hq" as (γw vss lh' lt' ->) "(Hmeta' & Hlhptr' & Hγe' & Hlist)".
      iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
      iMod (is_queue_dequeue eend with "Hlist [$] []")
        as (v vs vss' ->) "(Hstart & #Hv & Hlist)"; [lia|by auto|].
      wp_store. iDestruct "Hstart" as "[Hstart Hstart']".
      iDestruct ("Hlist" with "Hstart'") as "Hlist".
      iDestruct "Hcl" as "[_ Hcl]".
      iMod ("Hcl" with "[-Hlhptr Hstart]") as "HΦ"; first by iFrame.
      iModIntro. wp_load. iApply "HΦ".
      replace (start + 1)%Z with (Z.of_nat (S start)) by lia. by iFrame. }

    wp_bind (_ <- _)%E. iMod "AU" as (ltptr vs) "[Hq Hcl]".
    iDestruct "Hq" as (γw vss lh' lt' ->) "(Hmeta' & Hlhptr' & Hγe' & Hlist)".
    iDestruct (pointsto_agree with "Hlhptr' Hlhptr") as %[=]; simplify_eq.
    iCombine "Hlhptr' Hlhptr" as "Hlhptr". rewrite Qp.three_quarter_quarter.
    wp_store.
    iEval (rewrite -Qp.three_quarter_quarter) in "Hlhptr".
    iDestruct "Hlhptr" as "[Hlhptr' Hlhptr]".
    iDestruct (is_queue_dequeue_node with "Hlist [$] [$] [$]")
      as (vss' n ->) "[Hstart Hlist]"; first lia.
    iDestruct "Hcl" as "[Hcl _]".
    iMod ("Hcl" with "[$Hmeta' $Hγe' $Hlist $Hlhptr' //]") as "AU".
    iModIntro. wp_pures. iApply ("IH" with "[$] AU").
  Qed.

  Lemma enqueue_spec `{time_receiptG Σ} ltptr v γ N :
    tr_ctx N γ -∗
    enqueue_handle ltptr -∗
    <<{ ∀∀ lhptr vs n, is_queue lhptr ltptr vs ∗ ⧗{γ} n }>>
      enqueue #ltptr v @ ↑N
    <<{ is_queue lhptr ltptr (vs ++ [v]) ∗ ⧗{γ} (S n) ∗ £ (S n)
      | RET #(); enqueue_handle ltptr }>>.
  Proof.
    iIntros "#H⧗ctx Hh %Φ AU". pose proof size_pos.
    rewrite is_queue_unseal enqueue_handle_unseal.
    iDestruct "Hh" as (γw lt eend uninit Hsize)
      "(#Hmeta & Hγe & Hltptr & Hend & Hbuf)".
    wp_lam. do 2 wp_load. wp_pures. case_bool_decide; wp_pures.
    - (* The current array is not yet full. *)
      destruct uninit as [|u uninit]; simplify_eq/=; first lia.
      iDestruct (array_cons with "Hbuf") as "[Hv Hbuf]".
      wp_store. wp_pures. rewrite Loc.add_assoc.
      replace (BUFFER + eend + 1)%Z with (BUFFER + S eend)%Z by lia.
      iMod (pointsto_persist with "Hv") as "#Hv".

      iDestruct (aupd_aacc with "AU") as "AU".
      iDestruct (fupd_mask_frame_r _ _ (↑N) with "AU") as "AU"; first set_solver.
      rewrite left_id_L (comm_L (∪)) -union_difference_L //.
      iMod "AU" as (lhptr vs n) "((Hq & H⧗) & Hcl)".

      iDestruct (tr_aacc _ _ _ (↑N) with "H⧗ctx H⧗") as "Htr"; first done.
      rewrite /atomic_acc /=.
      iMod "Htr" as (m) "((%Hle & #Hsteps) & Hcl')".
      iDestruct "Hq" as (γw' vss lh lt' ->)
        "(Hmeta' & Hlhptr & Hγe' & Hlist)".
      iDestruct (meta_agree with "Hmeta' Hmeta") as "->".
      iDestruct (ghost_var_agree with "Hγe' Hγe") as %[=]; simplify_eq.

      iDestruct (is_queue_list_enqueue_elem with "Hlist Hend")
        as (vs vss' ->) "[Hend Hlist]"; first by lia.

      iApply (wp_lb_update with "Hsteps").
      wp_apply (wp_store_lc with "[$Hend $Hsteps]") as "([Hend Hend'] & H£)".
      replace (eend + 1)%Z with (Z.of_nat (S eend)) by lia.
      iIntros "{Hsteps} #Hsteps".
      iMod ("Hlist" with "Hend' Hv") as "Hlist".

      iMod ("Hcl'" with "[$Hsteps]") as "H⧗".
      iModIntro.
      iDestruct ("Hcl" with "[-Hbuf Hend Hltptr Hγe']") as "Hcl".
      { iFrame. iSplit; first by rewrite !join_app /= !right_id_L !assoc_L.
        iApply (lc_weaken with "[$]"); lia. }

      iDestruct (fupd_mask_frame_r _ _ (↑N)
          with "Hcl") as "Hcl"; first set_solver.
      rewrite left_id_L (comm_L (∪)) -union_difference_L; [|done].
      iMod "Hcl" as "HΦ".
      iModIntro. iApply "HΦ". iExists γw, lt, (S eend), uninit.
      iFrame "∗ #". iPureIntro. lia.
    - (* The current array is full. Allocate and enqueue to a new array node. *)
      wp_apply (wp_allocN with "[//]"); first (rewrite nodesize_eq /=; lia).
      rewrite nodesize_eq /= Nat2Z.id /=.
      iIntros (l) "[Hl [Hlmeta _]]". rewrite Loc.add_0.

      wp_pures.
      iAssert ((l +ₗ START) ↦ #() ∗ (l +ₗ END) ↦ #() ∗ (l +ₗ NEXT) ↦ #() ∗
        (l +ₗ BUFFER) ↦∗ replicate SIZE #())%I
        with "[Hl]" as "(Hnstart & Hnend & Hnnext & Hnbuf)".
      { iDestruct (array_cons with "Hl") as "[Hl0 Hl]".
        iDestruct (array_cons with "Hl") as "[Hl1 Hl]".
        iDestruct (array_cons with "Hl") as "[Hl2 Hl]".
        rewrite !Loc.add_assoc Loc.add_0. iFrame. }
      wp_store. wp_store. wp_store. iDestruct "Hnend" as "[Hnend Hnend']".

      replace SIZE with (S (SIZE - 1)) by lia; simpl.
      iDestruct (array_cons with "Hnbuf") as "[Hv Hnbuf]".
      rewrite Loc.add_assoc. wp_store. wp_pures.
      iMod (pointsto_persist with "Hv") as "Hv".

      wp_bind (_ <- _)%E.
      iDestruct (aupd_aacc with "AU") as "AU".
      iDestruct (fupd_mask_frame_r _ _ (↑N) with "AU") as "AU"; first set_solver.
      rewrite left_id_L (comm_L (∪)) -union_difference_L //.
      iMod "AU" as (lhptr vs n) "((Hq & H⧗) & Hcl)".

      iDestruct (tr_aacc _ _ _ (↑N) with "H⧗ctx H⧗") as "Htr"; first done.
      rewrite /atomic_acc /=.
      iMod "Htr" as (m) "((%Hle & #Hsteps) & Hcl')".
      iDestruct "Hq" as (γw' vss lh lt' ->)
        "(Hmeta' & Hlhptr & Hγe' & Hlist)".
      iDestruct (meta_agree with "Hmeta' Hmeta") as "->".
      iDestruct (ghost_var_agree with "Hγe' Hγe") as %[=]; simplify_eq.

      iDestruct (is_queue_list_enqueue_node with "Hlist Hend") as "[Hnext Hlist]".
      iApply (wp_lb_update with "Hsteps").
      wp_apply (wp_store_lc with "[$Hnext $Hsteps]") as "(Hnext & H£)".
      iIntros "{Hsteps} #Hsteps".

      iMod ("Hlist" with "[$] [$] [$] [$] [$] [$]") as "Hlist".

      iMod (ghost_var_update l with "[Hγe' Hγe]") as "[Hγe' Hγe]";
        first by iCombine "Hγe' Hγe" as "?".
      iMod ("Hcl'" with "[$Hsteps]") as "H⧗".
      iModIntro.
      iDestruct ("Hcl" with "[-Hnend Hnbuf Hltptr Hγe']") as "Hcl".
      { iFrame. iSplit; first by rewrite !join_app.
        iApply (lc_weaken with "[$]"); lia. }

      iDestruct (fupd_mask_frame_r _ _ (↑N)
          with "Hcl") as "Hcl"; first set_solver.
      rewrite left_id_L (comm_L (∪)) -union_difference_L; [|done].
      iMod "Hcl" as "HΦ".
      iModIntro. wp_store. iApply "HΦ". iExists γw, l, 1, (replicate (SIZE - 1) #()).
      iFrame. rewrite replicate_length. auto with lia.
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
    iDestruct "He" as (γlt1 lt1 eend1 uninit1 ?)
      "(#Hmeta1 & Hγe1 & Hltptr1 & Hend1 & Hbuf1)".
    iDestruct "Hd" as (lh2 start2) "[Hlhptr2 Hstart2]".
    wp_lam. do 2 wp_load. wp_pures.
    wp_bind (_ <- _)%E.
    iMod "AU" as (b lhptr1 ltptr2 vs1 vs2) "([Hq1 Hq2] & [_ Hcl])".

    iDestruct "Hq1" as (γw1' vss1 lh1 lt1' ->)
      "(Hmeta1' & Hlhptr1 & Hγe1' & Hlist1)".
    iDestruct (meta_agree with "Hmeta1' Hmeta1") as "->".
    iDestruct (ghost_var_agree with "Hγe1' Hγe1") as %[=]; simplify_eq.
    iDestruct (is_queue_list_link with "Hlist1") as "[Hnext1 Hlist]".
    wp_store.

    destruct b; simpl.
    - iDestruct "Hq2" as (γw2' vss2 lh2' lt2' ->)
        "(Hmeta2' & Hlhptr2' & Hγe2' & Hlist2)".
      iDestruct (pointsto_agree with "Hlhptr2' Hlhptr2") as %[=]; simplify_eq.
      iMod ("Hlist" with "[$] [$] [$]") as "Hlist".
      iMod ("Hcl" with "[-]"); [|iModIntro; by wp_pures].
      iExists _, (vss1 ++ vss2). iFrame. by rewrite join_app.
    - iDestruct "Hq2" as "(-> & -> & <-)".
      iMod ("Hcl" with "[$]") as "HΦ".
      iModIntro; by wp_pures.
  Qed.
End queue_spec.
