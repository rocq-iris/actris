From stdpp Require Import sorting.
From iris.heap_lang Require Import lib.assert.
From linking_actris.logic Require Import proofmode adequacy.

Definition service : val :=
  rec: "service" "d" "sum" :=
    let: "n" := recv "d" in
    if: #0 < "n"
    then "service" "d" ("sum" + "n")
    else send "d" "sum".

Definition prog2 : expr :=
  let: "c" := start_chan (λ: "c'", service "c'" #0) in
  send "c" #20;; send "c" #22;; send "c" #0;;
  assert: (recv "c" = #42).

Context `{!heapGS Σ, !chanGS Σ}.

Definition service_proto : iProto Σ :=
  <!> MSG #20%Z; <!> MSG #22%Z; <!> MSG #0%Z; <?> MSG #42; END.

Lemma service_spec d :
  {{{ d ↣ iProto_dual service_proto }}}
    service d #0
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hd HΦ".
  do 3 (wp_rec; wp_recv as "_"; wp_pures).
  wp_send with "[//]".
  by iApply "HΦ".
Qed.

Lemma prog2_spec :
  {{{ proto_chan_ctx }}}
    prog2
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ". unfold prog2. wp_pures.
  wp_apply (start_chan_spec with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %c Hc". wp_pures.
    by wp_apply (service_spec with "Hc"). }
  iIntros "!> %c Hc". wp_pures.
  do 3 (wp_send with "[//]"; wp_pures).
  wp_smart_apply wp_assert.
   wp_recv as "_".
  wp_pures; iModIntro; iSplit; [done|iModIntro].
  by iApply "HΦ".
Qed.

Definition prog3 : expr :=
  let: "c" := start_chan (λ: "c'", service "c'" #0) in
  let: "d" := start_chan (λ: "d'", send "c" #20;; link "c" "d'") in
  send "d" #22;; send "d" #0;;
  assert: (recv "d" = #42).

Lemma prog3_spec :
  {{{ proto_chan_ctx }}}
    prog3
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ". unfold prog3. wp_pures.

  wp_apply (start_chan_spec with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %c Hc". wp_pures.
    by wp_apply (service_spec with "Hc"). }
  iIntros "!> %c Hc"; wp_pures.

  wp_apply (start_chan_spec with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %d Hd". wp_pures.
    wp_send with "[//]"; wp_pures; simpl.
    by wp_apply (link_spec with "[$Hc $Hd]"). }
  iIntros "!> %d Hd"; wp_pures.

  do 2 (wp_send with "[//]"; wp_pures).
  wp_smart_apply wp_assert.
   wp_recv as "_".
  wp_pures; iModIntro; iSplit; [done|iModIntro].
  by iApply "HΦ".
Qed.

(* Define the recursive quantified version of the protocol. *)
Definition service_proto_rec_rec (rec : Z -d> iProto Σ) : Z -d> iProto Σ :=
  λ s : Z,
    (<! (n : Z)> MSG #n;
      if decide (0 < n)%Z
      then rec (s + n)%Z
      else <?> MSG #s; END)%proto.

Instance service_proto_rec_rec_contractive : Contractive service_proto_rec_rec.
Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.

Definition service_proto_rec : Z -d> iProto Σ := fixpoint service_proto_rec_rec.
Global Instance service_proto_rec_unfold n :
  ProtoUnfold (service_proto_rec n) (service_proto_rec_rec service_proto_rec n).
Proof. apply proto_unfold_eq, (fixpoint_unfold service_proto_rec_rec). Qed.

(* Specifications using the recursive quantified protocol. *)
Lemma service_spec_rec d s :
  {{{ d ↣ iProto_dual (service_proto_rec s) }}}
    service d #s
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hd HΦ".
  iLöb as "IH" forall (s).
  wp_rec.
  wp_recv (n) as "n"; wp_pures.
  case_decide.
  - rewrite bool_decide_true; [|done].
    wp_pures.
    wp_apply ("IH" with "Hd HΦ").
  - rewrite bool_decide_false; [|done].
    wp_pures. wp_send with "[//]". by iApply "HΦ".
Qed.

Lemma prog2_spec_rec :
  {{{ proto_chan_ctx }}}
    prog2
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ". unfold prog2. wp_pures.
  wp_apply (start_chan_spec (service_proto_rec 0) with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %c Hc". wp_pures.
    by wp_apply (service_spec_rec with "Hc"). }
  iIntros "!> %c Hc". wp_pures.
  do 3 (wp_send with "[//]"; wp_pures).
  wp_smart_apply wp_assert.
   wp_recv as "_".
  wp_pures; iModIntro; iSplit; [done|iModIntro].
  by iApply "HΦ".
Qed.

Lemma prog3_spec_rec :
  {{{ proto_chan_ctx }}}
    prog3
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ". unfold prog3. wp_pures.

  wp_apply (start_chan_spec (service_proto_rec 0) with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %c Hc". wp_pures.
    by wp_apply (service_spec_rec with "Hc"). }
  iIntros "!> %c Hc"; wp_pures.

  wp_apply (start_chan_spec (service_proto_rec 20%Z) with "[$] [-HΦ] [HΦ]").
  { iIntros "!> %d Hd". wp_pures.
    wp_send with "[//]"; wp_pures.
    by wp_apply (link_spec with "[$Hc $Hd]"). }
  iIntros "!> %d Hd"; wp_pures.

  do 2 (wp_send with "[//]"; wp_pures).
  wp_smart_apply wp_assert.
   wp_recv as "_".
  wp_pures; iModIntro; iSplit; [done|iModIntro].
  by iApply "HΦ".
Qed.

Definition prog4 : val := λ: "c",
  let: "l" := recv "c" in
  "l" <- !"l" + #1;;
  send "c" #true.

Definition prog4_c_prot : iProto Σ :=
  <? (l : loc) (n : Z)> MSG #l {{ l ↦ #n }}; <! (b : bool)> MSG #b {{ l ↦ #(n + 1) }}; END.

Lemma prog4_spec c :
  {{{ c ↣ prog4_c_prot }}}
    prog4 c
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hc HΦ". wp_lam. wp_pures.
  wp_recv (l n) as "Hl"; wp_pures.
  wp_load; wp_store; wp_pures.
  wp_send with "[$Hl]". by iApply "HΦ".
Qed.
