From iris.algebra Require Import auth.
From iris.program_logic Require Import atomic.
From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import primitive_laws.
From iris.prelude Require Import options.

(* This file contains a model of non-persistent time receipts (Mevel et al. 2019)
   using the steps lower bound provided by Iris (similar to persistent timereceipts),
   and an Iris invariant. The non-persistent time receipts are additive and can hence
   be added when merging two channel pedicates, unlike the steps lower bound.

   The idea is that we can use a single persistent time receipt ⧖n to equal to the
   sum of all non-persistent time receipts (⧗n). When taking an atomic step, we can
   then use ⧗n to retrieve a persistent time receipt ⧖m of at least n, create m + 1
   later credits and (⧖(m+1)), which we then put back and create an additional ⧗1.
*)

Record time_receipt_inv_name := TimeReceiptName { time_receipt_name : gname }.

(** The ghost state for time receipts *)
Class time_receiptG (Σ : gFunctors) := {
  #[local] time_receiptG_inG :: inG Σ (auth nat)
}.
Definition time_receiptΣ := #[ GFunctor (authR nat) ].
Global Instance subG_time_receiptΣ {Σ} :
  subG time_receiptΣ Σ → time_receiptG Σ.
Proof. solve_inG. Qed.

Definition tr_ub_def `{time_receiptG Σ} (γ : time_receipt_inv_name)
    (n : nat) : iProp Σ :=
  own (time_receipt_name γ) (● n).
Local Definition tr_ub_aux : seal (@tr_ub_def). Proof. by eexists. Qed.
Definition tr_ub := tr_ub_aux.(unseal).
Local Definition tr_ub_unseal : @tr_ub = @tr_ub_def := tr_ub_aux.(seal_eq).
Global Arguments tr_ub {Σ _} _ n.

Global Instance tr_ub_timeless `{!time_receiptG Σ} γ n : Timeless (tr_ub γ n).
Proof. rewrite tr_ub_unseal. apply _. Qed. 

(* The time receipt invariant consists of an upper bound on the number of
   non-persistent time receipts, and a persistent time receipt of that amount. *)
Definition time_receipt_inv `{!heapGS Σ, !time_receiptG Σ}
    (γ : time_receipt_inv_name) : iProp Σ :=
  ∃ n, tr_ub γ n ∗ steps_lb n.

Definition tr_def `{time_receiptG Σ} (γ : time_receipt_inv_name)
    (n : nat) : iProp Σ :=
  own (time_receipt_name γ) (◯ n).
Local Definition tr_aux : seal (@tr_def). Proof. by eexists. Qed.
Definition tr := tr_aux.(unseal).
Local Definition tr_unseal : @tr = @tr_def := tr_aux.(seal_eq).
Global Arguments tr {Σ _} _ n.

Notation "'⧗{' γ '}' n" := (tr γ n) (at level 1, format "'⧗{' γ '}'  n").

Definition tr_ctx `{!heapGS Σ, !time_receiptG Σ} (N : namespace)
    (γ : time_receipt_inv_name) : iProp Σ :=
  inv N (time_receipt_inv γ).

Section tr.
  Context `{!heapGS Σ, !time_receiptG Σ}.

  Global Instance tr_timeless γ n : Timeless (⧗{γ} n).
  Proof. rewrite tr_unseal. apply _. Qed.
  Global Instance tr_0_persistent γ : Persistent (⧗{γ} 0).
  Proof. rewrite tr_unseal. apply _. Qed.

  Lemma tr_ctx_alloc N E : ⊢ |={E}=> ∃ γ, tr_ctx N γ.
  Proof.
    iMod (own_alloc (● 0)) as (γ) "Hsetpsauth".
    { by apply auth_auth_valid. }
    iMod (steps_lb_0) as "Hsteps".
    iExists (TimeReceiptName γ).
    iApply inv_alloc.
    iFrame. by rewrite tr_ub_unseal.
  Qed.

  (* Non-persistent time receipts are additive. *)
  Lemma tr_split γ n m : ⧗{γ} (n + m) ⊣⊢ ⧗{γ} n ∗ ⧗{γ} m.
  Proof.
    rewrite tr_unseal /tr_def.
    rewrite -own_op auth_frag_op //=.
  Qed.

  Lemma tr_zero γ : ⊢ |==> ⧗{γ} 0.
  Proof. rewrite tr_unseal /tr_def. iApply own_unit. Qed.

  Lemma tr_succ γ n : ⧗{γ} (S n) ⊣⊢ ⧗{γ} 1 ∗ ⧗{γ} n.
  Proof. rewrite -tr_split //=. Qed.

  Lemma tr_weaken γ {n} m : m ≤ n → ⧗{γ} n -∗ ⧗{γ} m.
  Proof.
    intros [k ->]%Nat.le_sum. rewrite tr_split. iIntros "[$ _]".
  Qed.

  Lemma tr_ub_valid γ n m : tr_ub γ n -∗ ⧗{γ} m -∗ ⌜ m ≤ n ⌝.
  Proof.
    rewrite tr_unseal tr_ub_unseal /tr_def /tr_ub_def. iIntros "Hn Hauth".
    by iDestruct (own_valid_2 with "Hn Hauth")
      as %[Hle%nat_included _]%auth_both_valid_discrete.
  Qed.

  (** Make sure that the rule for [+] is used before [S], otherwise Coq's
  unification applies the [S] hint too eagerly. See Iris issue #470. *)
  Global Instance from_sep_tr_add γ n m :
    FromSep (⧗{γ} (n + m)) (⧗{γ} n) (⧗{γ} m) | 0.
  Proof. by rewrite /FromSep tr_split. Qed.
  Global Instance from_sep_tr_S γ n :
    FromSep (⧗{γ} (S n)) (⧗{γ} 1) (⧗{γ} n) | 1.
  Proof. by rewrite /FromSep (tr_succ γ n). Qed.
  (** When combining later credits with [iCombine], the priorities are
  reversed when compared to [FromSep] and [IntoSep]. This causes
  [⧗{γ} n] and [⧗{γ} 1] to be combined as [⧗{γ} (S n)], not as [⧗{γ} (n + 1)]. *)
  Global Instance combine_sep_tr_add γ n m :
    CombineSepAs (⧗{γ} n) (⧗{γ} m) (⧗{γ} (n + m)) | 1.
  Proof. by rewrite /CombineSepAs tr_split. Qed.
  Global Instance combine_sep_tr_S_l γ n :
    CombineSepAs (⧗{γ} n) (⧗{γ} 1) (⧗{γ} (S n)) | 0.
  Proof. by rewrite /CombineSepAs comm (tr_succ _ n). Qed.

  Global Instance into_sep_tr_add γ n m :
    IntoSep (⧗{γ} (n + m)) (⧗{γ} n) (⧗{γ} m) | 0.
  Proof. by rewrite /IntoSep tr_split. Qed.
  Global Instance into_sep_tr_S γ n :
    IntoSep (⧗{γ} (S n)) (⧗{γ} 1) (⧗{γ} n) | 1.
  Proof. by rewrite /IntoSep (tr_succ _ n). Qed.

  Local Lemma auth_frag_incr γ' n m :
    own γ' (● n) -∗ own γ' (◯ m) ==∗ own γ' (● (S n)) ∗ own γ' (◯ (S m)).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ _ with "Hγ● Hγ◯") as "[$$]".
    { apply auth_update, nat_local_update. lia. }
    done.
  Qed.

  Local Lemma tr_ub_incr γ n : tr_ub γ n ==∗ tr_ub γ (S n) ∗ ⧗{γ} 1.
  Proof.
    rewrite tr_unseal tr_ub_unseal /tr_def /tr_ub_def.
    iIntros "Hauth".
    iMod own_unit as "Hfrag".
    by iMod (auth_frag_incr with "Hauth Hfrag") as "$".
  Qed.

  (* This lemma states that we can give up n non-persistent time receipts to
     get a steps_lb of at least that amount for the duration of an atomic
     operation. This lower bound can be used to generate $S(n)$ later credits
     and an updated lower bound of $S(m)$. By giving up a copy of the updated
     lower bound, we receive one more than the original amount of
     non-persistent time receipts. Alternatively we can abort to get back the
     original n non-persistent time receipts. *)
  Lemma tr_aacc γ n N E:
    ↑N ⊆ E →
    tr_ctx N γ -∗
    ⧗{γ} n -∗
    AACC <{ ∃∃ m, ⌜n ≤ m⌝ ∗ steps_lb m, ABORT ⧗{γ} n }> @ E, (E∖↑N)
         <{ steps_lb (S m), COMM ⧗{γ} (S n) }>.
  Proof.
    iIntros (?) "#Hinv Hn".
    iInv N as (m) ">[Hauth Hsteps]".
    iDestruct (tr_ub_valid with "Hauth Hn") as %Hle.
    iAaccIntro with "[Hsteps]".
    { instantiate (1:=[tele_arg _]). by iFrame. }
    - (* ABORT *)
      iIntros "[_ Hsteps] !>".
      iFrame.
    - (* COMM *)
      simpl; iIntros "Hsteps".
      rewrite /time_receipt_inv tr_unseal tr_ub_unseal /tr_def /tr_ub_def.
      iMod (auth_frag_incr with "Hauth Hn") as "[Hauth Hn]".
      by iFrame.
  Qed.
End tr.
