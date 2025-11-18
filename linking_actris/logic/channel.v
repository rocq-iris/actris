From iris.algebra Require Import excl_auth.
From iris.bi.lib Require Import atomic.
From iris.base_logic Require Import invariants.
From iris.heap_lang Require Export notation proofmode.
From linking_actris.logic Require Import atomic_channel.
From linking_actris.logic Require Export proto.
From linking_actris.logic Require Import pairing time_receipts.
From iris.prelude Require Import options.

Set Default Proof Using "Type".

Definition new_chan := atomic_channel.new_chan.
Definition send := atomic_channel.send.
Definition recv := atomic_channel.recv.
Definition link := atomic_channel.link.

Definition start_chan : val := λ: "f",
  let: "cc" := new_chan #() in
  Fork ("f" (Snd "cc"));; Fst "cc".

Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

(** * Setup of Iris's cameras *)
Class chanG Σ := {
  #[local] chanG_lqueueG :: lqueueG Σ;
  #[local] chanG_protoG :: protoG Σ val;
  #[local] chanG_pairingG :: pairingG Σ (val * gname);
  #[local] chanG_trG :: time_receiptG Σ;
}.
Definition chanΣ :=
  #[ lqueueΣ; protoΣ val; pairingΣ (val * gname); time_receiptΣ ].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Local Definition proto_pairing `{!heapGS Σ, !chanG Σ}
    (γl : lqueue_inv_name) (γtr : time_receipt_inv_name)
    (cγ1 cγ2 : val * gname) : iProp Σ :=
  ∃ vs1 vs2,
    ⧗{γtr} (length vs1) ∗
    ⧗{γtr} (length vs2) ∗
    is_chan γl cγ1.1 cγ2.1 vs1 vs2 ∗
    iProto_ctx cγ1.2 cγ2.2 vs2 vs1.

Local Instance proto_pairing_pairpred `{!heapGS Σ, !chanG Σ} γl γtr :
  PairPred (proto_pairing γl γtr).
Proof.
  split.
  - iIntros ([c1 γ1] [c2 γ2]) "(%vs1 & %vs2 & _ & _ & ? & ?) %"; simplify_eq/=.
    by iApply is_chan_irr.
  - intros [c1 γ1] [c2 γ2]; iSplit;
      iIntros "(%vs1 & %vs2 & ? & ? & Hc & Hp)"; iExists vs2, vs1; simpl;

      iFrame; iSplitL "Hc";
      first [by iApply is_chan_sym|by iApply iProto_ctx_sym].
  - iIntros ([c1 γ1] [c2 γ2] [c3 γ3])
      "(%vs1 & %vs2 & _ & _ & ? & ?) (%vs3 & %vs4 & _ & _ & ? & ?)"; simplify_eq/=.
    by iApply (is_chan_unique with "[$]").
Qed.

Record proto_chan_ctx_name := ProtoChanCtxName {
  lqueue_inv_name : lqueue_inv_name;
  tr_inv_name : time_receipt_inv_name;
  pairing_inv_name : pairing_inv_name
}.

Class chanGS Σ := ChanGS {
  chanGS_chanG :: chanG Σ; 
  chanGS_name : proto_chan_ctx_name
}.

Local Definition Ntr := nroot .@ "tr".
Local Definition Nlqueue := nroot .@ "lqueue".
Local Definition Npairing := nroot .@" pairing".

(* The channel context also contains the `tr_ctx` which is used to model
   non-persistent time receipts using the persistent time receipts of Iris
   and an invariant (tr_ctx). See time_receipts.v for more details. *)
Definition proto_chan_ctx `{!heapGS Σ, !chanGS Σ} : iProp Σ :=
  let γtr := chanGS_name.(tr_inv_name) in
  let γlqueue := chanGS_name.(lqueue_inv_name) in
  let γpair := chanGS_name.(pairing_inv_name) in
  tr_ctx Ntr γtr ∗
  lqueue_ctx Nlqueue γlqueue ∗
  pairing_ctx (proto_pairing γlqueue γtr) Npairing γpair.

(* The specific ghost names and invariant names are captured by the `chanGS`
   typeclass instance which is implicitly passed. Note that this is the only
   lemma using `chanG`, which does not yet contain a shared the channel context
   ghost name, which is allocated by this lemma.
*)
Lemma proto_chan_ctx_alloc `{!heapGS Σ, !chanG Σ} E :
  ⊢ |={E}=> ∃ _ : chanGS Σ, proto_chan_ctx.
Proof.
  iMod tr_ctx_alloc as (γtr) "Htr".
  iMod lqueue_ctx_alloc as (γl) "Hlqueue".
  iMod (pairing_ctx_alloc (R:=proto_pairing γl γtr)) as (γpair) "Hpair".
  iExists (ChanGS _ _ (ProtoChanCtxName γl γtr γpair)). by iFrame.
Qed.

Global Instance proto_chan_ctx_persistent `{!heapGS Σ, !chanGS Σ} :
  Persistent (proto_chan_ctx).
Proof. apply _. Qed.

Definition iProto_mapsto_def `{!heapGS Σ, !chanGS Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ,
    proto_chan_ctx ∗
    is_pairing_element chanGS_name.(pairing_inv_name) (c,γ) ∗
    chan_handle c ∗
    iProto_own γ p.

Definition iProto_mapsto_aux : seal (@iProto_mapsto_def). by eexists. Qed.
Definition iProto_mapsto := iProto_mapsto_aux.(unseal).
Definition iProto_mapsto_eq :
  @iProto_mapsto = @iProto_mapsto_def := iProto_mapsto_aux.(seal_eq).
Arguments iProto_mapsto {_ _ _} _ _%_proto.
Global Instance: Params (@iProto_mapsto) 5 := {}.
Notation "c ↣ p" := (iProto_mapsto c p) (at level 20, format "c  ↣  p").

Global Instance iProto_mapsto_contractive `{!heapGS Σ, !chanGS Σ} c :
  Contractive (iProto_mapsto c).
Proof. rewrite iProto_mapsto_eq. solve_contractive. Qed.

Definition iProto_choice {Σ} (a : action) (P1 P2 : iProp Σ)
    (p1 p2 : iProto Σ) : iProto Σ :=
  (<a @ (b : bool)> MSG #b {{ if b then P1 else P2 }}; if b then p1 else p2)%proto.
Global Typeclasses Opaque iProto_choice.
Arguments iProto_choice {_} _ _%_I _%_I _%_proto _%_proto.
Global Instance: Params (@iProto_choice) 2 := {}.
Infix "<{ P1 }+{ P2 }>" := (iProto_choice Send P1 P2) (at level 85) : proto_scope.
Infix "<{ P1 }&{ P2 }>" := (iProto_choice Recv P1 P2) (at level 85) : proto_scope.
Infix "<+{ P2 }>" := (iProto_choice Send True P2) (at level 85) : proto_scope.
Infix "<&{ P2 }>" := (iProto_choice Recv True P2) (at level 85) : proto_scope.
Infix "<{ P1 }+>" := (iProto_choice Send P1 True) (at level 85) : proto_scope.
Infix "<{ P1 }&>" := (iProto_choice Recv P1 True) (at level 85) : proto_scope.
Infix "<+>" := (iProto_choice Send True True) (at level 85) : proto_scope.
Infix "<&>" := (iProto_choice Recv True True) (at level 85) : proto_scope.

Section channel.
  Context `{!heapGS Σ, !chanGS Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Global Instance iProto_mapsto_ne c : NonExpansive (iProto_mapsto c).
  Proof. rewrite iProto_mapsto_eq. solve_proper. Qed.
  Global Instance iProto_mapsto_proper c  : Proper ((≡) ==> (≡)) (iProto_mapsto c).
  Proof. apply (ne_proper _). Qed.

  Lemma iProto_mapsto_le c p1 p2 : c ↣ p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
  Proof.
    rewrite iProto_mapsto_eq /iProto_mapsto_def.
    iIntros "(%γ & $ & Hpair & $ & ?) Hle {$Hpair}".
    by iApply (iProto_own_le with "[$]").
  Qed.

  Global Instance iProto_choice_contractive n a :
    Proper (dist n ==> dist n ==>
            dist_later n ==> dist_later n ==> dist n) (@iProto_choice Σ a).
  Proof. solve_contractive. Qed.
  Global Instance iProto_choice_ne n a :
    Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) (@iProto_choice Σ a).
  Proof. solve_proper. Qed.
  Global Instance iProto_choice_proper a :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (@iProto_choice Σ a).
  Proof. solve_proper. Qed.

  Lemma iProto_choice_equiv a1 a2 (P11 P12 P21 P22 : iProp Σ)
        (p11 p12 p21 p22 : iProto Σ) :
    ⌜a1 = a2⌝ -∗ ((P11 ≡ P12):iProp Σ) -∗ (P21 ≡ P22) -∗
    ▷ (p11 ≡ p12) -∗ ▷ (p21 ≡ p22) -∗
    iProto_choice a1 P11 P21 p11 p21 ≡ iProto_choice a2 P12 P22 p12 p22.
  Proof.
    iIntros (->) "#HP1 #HP2 #Hp1 #Hp2".
    rewrite /iProto_choice. iApply iProto_message_equiv; [ eauto | | ].
    - iIntros "!>" (b) "H". iExists b. iSplit; [ done | ].
      destruct b;
        [ iRewrite -"HP1"; iFrame "H Hp1" | iRewrite -"HP2"; iFrame "H Hp2" ].
    - iIntros "!>" (b) "H". iExists b. iSplit; [ done | ].
      destruct b;
        [ iRewrite "HP1"; iFrame "H Hp1" | iRewrite "HP2"; iFrame "H Hp2" ].
  Qed.

  Lemma iProto_dual_choice a P1 P2 p1 p2 :
    iProto_dual (iProto_choice a P1 P2 p1 p2)
    ≡ iProto_choice (action_dual a) P1 P2 (iProto_dual p1) (iProto_dual p2).
  Proof.
    rewrite /iProto_choice iProto_dual_message /= iMsg_dual_exist.
    f_equiv; f_equiv=> -[]; by rewrite iMsg_dual_base.
  Qed.

  Lemma iProto_app_choice a P1 P2 p1 p2 q :
    (iProto_choice a P1 P2 p1 p2 <++> q)%proto
    ≡ (iProto_choice a P1 P2 (p1 <++> q) (p2 <++> q))%proto.
  Proof.
    rewrite /iProto_choice iProto_app_message /= iMsg_app_exist.
    f_equiv; f_equiv=> -[]; by rewrite iMsg_app_base.
  Qed.

  Lemma iProto_le_choice a P1 P2 p1 p2 p1' p2' :
    (P1 -∗ P1 ∗ ▷ (p1 ⊑ p1')) ∧ (P2 -∗ P2 ∗ ▷ (p2 ⊑ p2')) -∗
    iProto_choice a P1 P2 p1 p2 ⊑ iProto_choice a P1 P2 p1' p2'.
  Proof.
    iIntros "H". rewrite /iProto_choice. destruct a;
      iIntros (b) "HP"; iExists b; destruct b;
      iDestruct ("H" with "HP") as "[$ ?]"; by iModIntro.
  Qed.

  (* ** Specifications of channel operations *)

  (* The specification of new_chan differs from that in §2.2, instead matching
     the specification in §6.2 which includes the shared channel invariant. The
     name 𝛾 of the channel context is implicitly passed as part of the context
     in chanGS.
     
     The channel context is instantiated in the adequacy lemma in adequacy.v.
     *)
  Lemma new_chan_spec p :
    {{{ proto_chan_ctx }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); c1 ↣ p ∗ c2 ↣ iProto_dual p }}}.
  Proof.
    iIntros (Φ) "#(? & ? & ?) HΦ". iApply wp_fupd.
    wp_apply (atomic_channel.new_chan_spec with "[$]").
    iIntros (c1 c2) "(Hc & Hh1 & Hh2 & H£)". iApply "HΦ".
    iMod (iProto_init p) as (γ1 γ2) "(Hctx & Hc1 & Hc2)".
    iMod tr_zero as "#Htr".
    iInv (Npairing) as "Hpair".
    iMod (pairing_new _ _ (c1,γ1) (c2,γ2) with "[$] [$Hc $Hctx $Htr]")
      as "(Hel1 & Hel2 & Hpair)".
    rewrite iProto_mapsto_eq. by iFrame "∗ #".
  Qed.

  (* The start_chan specification is defined using weakest precondition rather
     than hoare triples. This allows the specification to be applied in the
     Iris proof mode without first explicitly combining all resources for the
     forked thread into a single resource $P$.
  *)
  Lemma start_chan_spec p Φ (f : val) :
    proto_chan_ctx -∗
    ▷ (∀ c, c ↣ iProto_dual p -∗ WP f c {{ _, True }}) -∗
    ▷ (∀ c, c ↣ p -∗ Φ c) -∗
    WP start_chan f {{ Φ }}.
  Proof.
    iIntros "#? Hfork HΦ". wp_lam.
    wp_smart_apply (new_chan_spec p with "[$]"); iIntros (c1 c2) "[Hc1 Hc2]".
    wp_smart_apply (wp_fork with "[Hfork Hc2]").
    { iNext. wp_smart_apply ("Hfork" with "Hc2"). }
    wp_pures. iApply ("HΦ" with "Hc1").
  Qed.

  Lemma send_spec c v p :
    {{{ c ↣ <!> MSG v; p }}}
      send c v
    {{{ RET #(); c ↣ p }}}.
  Proof.
    rewrite iProto_mapsto_eq.
    iIntros (Φ) "(%γ & #(? & ? & ?) & Hpairel & Hc & Hγ) HΦ".
    awp_apply (atomic_channel.send_spec with "[$] [$] [$]"); first solve_ndisj.
    
    iInv Npairing as "Hpair".
    iMod (pairing_update with "[$] [$]") as "(%b & (% & % & >H⧗1 & >H⧗2 & >Hc & Hproto) & Hcl)".
    destruct b as (c' & γ').
    iCombine "Hc H⧗1" as "H".
    iAaccIntro with "H"; simpl.
    - (* Abort *)
      iIntros "[Hc H⧗1]".
      iMod ("Hcl" with "[- Hγ HΦ]") as "[Hpair Hinv]".
      { iNext. iExists _, _. iFrame. }
      iModIntro.
      iFrame.
    - (* Commit *)
      iIntros "(Hc & (H⧗1 & H⧗) & H£1 & H£)".
      iApply (lc_fupd_add_later with "H£1"); iNext.
      iMod (iProto_send with "[$] [$] []") as "[Hctx Hown]".
      { rewrite iMsg_base_eq /=; auto. }
      iApply (lc_fupd_add_laterN with "[$]"); iNext.
      iMod ("Hcl" with "[- Hown HΦ]") as "[Hpair Hinv]".
      { iNext. iExists _, _. iFrame.
        rewrite length_app length_cons length_nil.
        iApply (tr_split); iFrame. }
      iModIntro; iFrame.
      iIntros "Hhandle".
      iApply "HΦ"; iFrame "# ∗".
  Qed.

  Lemma send_spec_tele {TT} c (tt : TT)
        (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ):
    {{{ c ↣ (<!.. x > MSG v x {{ P x }}; p x) ∗ P tt }}}
      send c (v tt)
    {{{ RET #(); c ↣ (p tt) }}}.
  Proof.
    iIntros (Φ) "(Hc & HP)".
    iDestruct (iProto_mapsto_le _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
      as "Hc".
    { iIntros "!>".
      iApply iProto_le_trans;
      first iApply iProto_le_texist_intro_l.
      by iFrame "HP". }
    by iApply send_spec.
  Qed.

  Lemma recv_spec {TT} c (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ) :
    {{{ c ↣ <?.. x> MSG v x {{ ▷ P x }}; p x }}}
      recv c
    {{{ x, RET v x; c ↣ p x ∗ P x }}}.
  Proof.
    rewrite iProto_mapsto_eq.
    iIntros (Φ) "(%γ & #(? & ? & ?) & Hpairel & Hc & Hγ) HΦ".
    awp_apply (atomic_channel.recv_spec with "[$] [$]").
    
    iInv Npairing as "Hpair".
    iMod (pairing_update with "[$] [$]") as "(%b & (% & % & >H⧗1 & >H⧗2 & >Hc & Hproto) & Hcl)".
    destruct b as (c' & γ').
    iCombine "Hc" as "H".
    iAaccIntro with "H"; simpl.
    - (* Abort *)
      iIntros "Hc".
      iMod ("Hcl" with "[- Hγ HΦ]") as "[Hpair Hinv]".
      { iNext. iExists _, _. iFrame. }
      iModIntro.
      iFrame.
    - (* Commit *)
      iIntros (v1 vs1') "(-> & (H£1 & H£2 & H£3) & Hc)".
      iApply (lc_fupd_add_later with "H£1"); iNext.
      iMod (iProto_recv with "[$] [$]") as (q') "(Hctx & Hown & Hm)".
      rewrite iMsg_base_eq.
      iMod (lc_fupd_elim_later with "H£2 Hm") as "Hm".
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      iApply (lc_fupd_add_later with "H£3"); iNext.
      iMod ("Hcl" with "[- Hown HΦ Hp HP]") as "[Hpair Hinv]".
      { iNext. iExists _, _. iFrame.
        by iDestruct "H⧗1" as "(_ & H⧗1)". }
      iModIntro; iFrame.
      iIntros "Hhandle".
      iApply "HΦ"; iFrame "# ∗".
      by iRewrite "Hp".
  Qed.

  (** ** Specifications for choice *)
  Lemma select_spec c (b : bool) P1 P2 p1 p2:
    {{{ c ↣ (p1 <{P1}+{P2}> p2) ∗ if b then P1 else P2 }}}
      send c #b
    {{{ RET #(); c ↣ (if b then p1 else p2) }}}.
  Proof.
    iIntros (Φ) "(Hc & HP) HΦ".
    rewrite /iProto_choice.
    iApply (send_spec with "[Hc HP] HΦ").
    iApply (iProto_mapsto_le with "Hc").
    iIntros "!>". iExists b. by iFrame "HP".
  Qed.

  Lemma branch_spec c P1 P2 p1 p2:
    {{{ c ↣ (p1 <{P1}&{P2}> p2) }}}
      recv c
    {{{ b, RET #b; c ↣ (if b : bool then p1 else p2) ∗ if b then P1 else P2 }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". rewrite /iProto_choice.
    iApply (recv_spec _ (tele_app _)
      (tele_app (TT:=[tele _ : bool]) (λ b, if b then P1 else P2))%I
      (tele_app _) with "[Hc]").
    { iApply (iProto_mapsto_le with "Hc").
      iIntros "!> /=" (b) "HP". iExists b. by iSplitL. }
    rewrite -bi_tforall_forall.
    iIntros "!>" (x) "[Hc H]". iApply "HΦ". iFrame.
  Qed.

  Lemma link_spec c1 c3 p:
    {{{ c1 ↣ p ∗ c3 ↣ iProto_dual p }}}
      link c1 c3
    {{{ RET #(); True }}}.
  Proof.
    rewrite iProto_mapsto_eq. iIntros (Φ) "(Hc1 & Hc3) HΦ".
    iDestruct "Hc1" as "(%γ1 & #(? & ? & ?) & Hpairel1 & Hc1 & Hγ1)".
    iDestruct "Hc3" as "(%γ3 & #(? & ? & ?) & Hpairel3 & Hc3 & Hγ3)".
    awp_apply (atomic_channel.link_spec with "[$] [$] Hc1 Hc3");
      first solve_ndisj.
    
    iInv Npairing as "Hpair".

    iMod (pairing_update_2 with "[$] [$]") as "[(%a & %d & Hc & Hc' & Hcl) | (Hc & Hcl)]".
    - (* Two Channels *)
      iDestruct "Hc" as "(% & % & >H⧗1 & >H⧗2 & >Hc1 & Hproto1) /=".
      iDestruct "Hc'" as "(% & % & >H⧗3 & >H⧗4 & >Hc3 & Hproto3) /=".
      iDestruct (is_chan_sym with "Hc3") as "Hc4".
      iCombine "H⧗3 H⧗1" as "H⧗".
      iAaccIntro with "[Hc1 Hc4 H⧗]"; simpl.
      { instantiate (1:= [tele_arg true; _; _; _; _; _; _; _]); simpl.
        iFrame. }
      + (* Abort *)
        iIntros "(Hc34 & Hc21 & H⧗3 & H⧗1)".
        iDestruct (is_chan_sym with "Hc34") as "Hc43".
        iFrame.
        iDestruct "Hcl" as "[Hcl _]".
        iMod ("Hcl" with "[Hc21 Hproto1 H⧗1 H⧗2] [Hc43 Hproto3 H⧗3 H⧗4]") as "(Hel1 & Hel2 & Hinv)".
        { iNext. iExists _, _. iFrame "Hc21". iFrame. }
        { iNext. iExists _, _. iFrame "Hc43". iFrame. }
        iModIntro. iFrame. 
      + (* Commit *)
        simpl.
        iIntros "(Hc24 & (H⧗ & H⧗0 & H⧗1) & H£1 & H£2)".
        iApply (lc_fupd_add_later with "H£1"); iNext.
        iMod (iProto_join with "Hproto1 [$] [$] [Hγ1]") as "Hctx".
        { by rewrite (involutive iProto_dual). }
        (* { by rewrite (involutive iProto_dual). } *)
        iApply (lc_fupd_add_laterN with "[$]"); iNext.
        iDestruct "Hcl" as "[_ Hcl]".
        iMod ("Hcl" with "[- HΦ]") as "Hpair".
        2: { iModIntro. by iSplitL "Hpair". }
        iNext. iExists _, _.
        iDestruct (is_chan_sym with "Hc24") as "Hc24".
        iFrame "Hc24 Hctx".
        rewrite !length_app.
        iCombine "H⧗2 H⧗0" as "$".
        iCombine "H⧗4 H⧗1" as "$".
    - (* One Channel *)
      iDestruct "Hc" as "(% & % & >H⧗1 & >H⧗2 & >Hc1 & Hproto1) /=".
      (* iDestruct (is_chan_sym with "Hc1") as "Hc3". *)
      iMod tr_zero as "H⧗0".
      iAaccIntro with "[Hc1 H⧗0]"; simpl.
      { instantiate (1:= [tele_arg false; _; _; _; _; _; _; _]); simpl.
        by iFrame. }
      + (* Abort *)
        simpl.
        iIntros "(Hc & _)".
        iDestruct "Hcl" as "[Hcl _]".
        iMod ("Hcl" with "[Hc Hproto1 H⧗1 H⧗2]") as "(Hel1 & Hel2 & Hinv)".
        { iNext. iExists _, _. iFrame "Hc". iFrame. }
        iModIntro. iFrame.
      + (* Commit *)
        iIntros "(Hc & _ & H£1)".
        iApply (lc_fupd_add_later with "H£1"); iNext.
        iDestruct "Hcl" as "[_ Hcl]".
        iMod ("Hcl" with "[//]") as "Hpair".
        iModIntro.
        iFrame.
  Qed.
End channel.
