(* The first version of insertion sort in which a None request returns all values *)
From stdpp Require Import sorting.
From iris.heap_lang Require Import lib.assert.
From linking_actris.logic Require Import proofmode adequacy.

(* Shorter notation for link *)
Notation "'$' x ':=' y" := (link y x) (at level 200, format "'$' x  ':='  y").

Definition elem : val :=
  rec: "elem" "x" "t" := start_chan (λ: "c",
    match: recv "c" with
      SOME "y" =>
        if: "y" ≤ "x" then
          $"c" := "elem" "y" ("elem" "x" "t")
        else
          send "t" (SOME "y");;
          $"c" := "elem" "x" "t"
    | NONE =>
      send "t" NONE;;
      send "c" (SOME "x");;
      $"c" := "t"
    end).

Definition empty : val :=
  rec: "empty" <> := start_chan (λ: "c",
    match: recv "c" with
      SOME "x" =>
        $"c" := elem "x" ("empty" #())
    | NONE =>
      send "c" NONE
    end).

Definition client : expr :=
  let: "c" := empty #() in
  send "c" (SOME #5);;
  send "c" (SOME #2);;
  send "c" (SOME #3);;
  send "c" NONE;;
  assert: (recv "c" = SOME #2);;
  assert: (recv "c" = SOME #3);;
  assert: (recv "c" = SOME #5);;
  assert: (recv "c" = NONE).

Section spec.

Context `{!heapGS Σ, !chanGS Σ}.

Fixpoint insert_sorted x ls :=
  match ls with
  | [] => [x]
  | y :: ls => if decide (x ≤ y)%Z then x :: y :: ls else y :: insert_sorted x ls
  end.

Definition option_Z_val (o : option Z) : val :=
  match o with
  | Some v => SOMEV #v
  | None => NONEV
  end.

Fixpoint recv_proto (xs : list Z) : iProto Σ :=
  match xs with
  | [] => <?> MSG NONEV; END
  | x :: xs => <?> MSG (SOMEV #x); recv_proto xs
  end.

Definition sort_proto_rec (rec : list Z -d> iProto Σ) : list Z -d> iProto Σ :=
  λ ls : list Z,
    (<! on> MSG (option_Z_val on);
      match on with
      | Some n => rec (insert_sorted n ls)
      | None => recv_proto ls
      end)%proto.

Instance sort_proto_rec_contractive : Contractive sort_proto_rec.
Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.
Definition sort_proto : list Z → iProto Σ := fixpoint sort_proto_rec.
Global Instance sort_proto_unfold ls : ProtoUnfold (sort_proto ls) (sort_proto_rec sort_proto ls).
Proof. apply proto_unfold_eq, (fixpoint_unfold sort_proto_rec). Qed.

Lemma elem_spec x ls t :
  proto_chan_ctx -∗
  {{{ t ↣ sort_proto ls }}}
    elem #x t
  {{{ c, RET c; c ↣ sort_proto (x :: ls) }}}.
Proof.
  iIntros "#Hinv".
  iLöb as "IH" forall (x ls t).
  iIntros (Φ) "!> Htail HΦ".
  wp_rec; wp_pures.
  wp_apply (start_chan_spec with "[$] [-HΦ] [$HΦ]").
  iIntros "!> %c Hc"; wp_pures.
  wp_recv ([n|]) as "_"; wp_pures.
  - case_decide.
    + rewrite bool_decide_true; last lia. wp_pures.
      wp_apply ("IH" with "[$]") as (?) "?".
      wp_apply ("IH" with "[$]") as (?) "?".
      by wp_apply (link_spec with "[$]").
    + rewrite bool_decide_false; last lia.
      wp_pures.
      wp_send ((Some n)) with "[//]"; wp_pures.
      wp_apply ("IH" with "[$]") as (?) "?".
      by wp_apply (link_spec with "[$]").
  - wp_send (None) with "[//]"; wp_pures.
    wp_send with "[//]"; wp_pures.
    by wp_apply (link_spec with "[$Htail $Hc]").
Qed.

Lemma empty_spec :
  {{{ proto_chan_ctx }}}
    empty #()
  {{{ c, RET c; c ↣ sort_proto [] }}}.
Proof.
  iLöb as "IH".
  iIntros (Φ) "#Hinv HΦ".
  wp_rec; wp_pures.
  wp_apply (start_chan_spec with "[$] [-HΦ] [$HΦ]").
  iIntros "!> %c Hc"; wp_pures.
  wp_recv ([n|]) as "_"; wp_pures.
  - wp_apply ("IH" with "[//]") as (?) "?".
    wp_apply (elem_spec with "[$] [$]") as (?) "?". 
    by wp_apply (link_spec with "[$]").
  - by wp_send with "[//]".
Qed.

Lemma client_spec :
  {{{ proto_chan_ctx }}}
    client
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ". unfold client.
  wp_apply (empty_spec with "[$]"); iIntros (c) "Hc"; wp_pures.
  do 3 (wp_send ((Some (_%Z))) with "[//]").
  wp_send ((None)) with "[//]".
  do 4 (wp_smart_apply wp_assert; wp_recv as "_";
    wp_pures; iModIntro; iSplit; [done|iModIntro]).
  by iApply "HΦ".
Qed.

End spec.

(** Make sure we can use adequacy to get safety *)
Lemma client_adequate σ : adequate NotStuck client σ (λ _ _, True).
Proof.
  apply (chan_adequacy #[chanΣ; heapΣ])=> ??.
  iIntros "_ #?".
  by wp_apply client_spec.
Qed.
Print Assumptions client_adequate.
