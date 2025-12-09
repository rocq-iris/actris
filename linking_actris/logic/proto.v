From iris.proofmode Require Import proofmode.
From actris.channel Require Export proto.
Set Default Proof Using "Type".

(** * Proofs *)
Section proto.
  Context `{!protoG Σ V}.
  Implicit Types v : V.
  Implicit Types p pl pr : iProto Σ V.
  Implicit Types m : iMsg Σ V.

  Lemma iProto_app_recvs_le (vs : list V) p p' :
    p ⊑ p' -∗ iProto_app_recvs vs p ⊑ iProto_app_recvs vs p'.
  Proof.
    iIntros "Hlt". iInduction vs as [|v vs] "IH"; simpl; first done.
    iApply iProto_le_base. by iApply "IH".
  Qed.

  Lemma iProto_app_recvs_app (v1 : list V) (v2 : list V) p :
    iProto_app_recvs (v1 ++ v2) p ≡ iProto_app_recvs v1 (iProto_app_recvs v2 p).
  Proof.
    induction v1 as [|v v1]; simpl; first done.
    by rewrite IHv1.
  Qed.

  Lemma iProto_recvs_recv v p pl mr :
    (<?> MSG v; p) ⊑ (<?> mr) -∗
    ∃ pr, iMsg_car mr v (Next pr) ∗ ▷ (p ⊑ pr).
  Proof.
    iIntros "Hle".
    iDestruct (iProto_le_recv_inv with "Hle") as (m) "[#Hm Hle]".
    iDestruct (iProto_message_equivI with "Hm") as (_) "{Hm} #Hm".
    iDestruct ("Hle" $! v p with "[]")
      as (pr'') "[Hler Hle]".
    { iRewrite -("Hm" $! v (Next p)).
      rewrite iMsg_base_eq; auto. }
    iExists pr''.
    eauto with iFrame.
  Qed.

  Lemma iProto_swap_lst vs vsend p1 p :
    iProto_app_recvs vs p1 ⊑ (<!> MSG vsend; p) -∗
    ∃ pt,
      ▷^(length vs) (p1 ⊑ <!> MSG vsend; pt) ∗
      ▷ (iProto_app_recvs vs pt ⊑ p).
  Proof.
    iIntros "Hrecv".
    iInduction vs as [|v vs] "IH" forall (p); simpl.
    { iExists p; iFrame. iApply iProto_le_refl. }
    iDestruct (iProto_le_recv_send_inv with "Hrecv [] []")
      as "(%p' & Hrecvs & Hend)"; [by rewrite iMsg_base_eq /=..|].
    setoid_rewrite <-bi.later_sep. iApply @bi.later_exist. iModIntro.
    iDestruct ("IH" with "Hrecvs") as "(%pt & $ & Hrecvs)".
    iApply (iProto_le_trans with "[-Hend] Hend"). by iApply iProto_le_base.
  Qed.

  Lemma iProto_join_exists vs1 vs2 p1 p2 p :
    iProto_app_recvs vs2 p2 ⊑ p -∗
    iProto_app_recvs vs1 p1 ⊑ iProto_dual p -∗
    ▷^(length vs1 + length vs2) ∃ p',
      iProto_app_recvs vs2 p' ⊑ iProto_dual p1 ∗
      iProto_app_recvs vs1 (iProto_dual p') ⊑ iProto_dual p2.
  Proof.
    iIntros "Hrecv1 Hrecv2".
    iInduction (vs1) as [|v1 vs1] "IH" forall (vs2 p p1 p2); simpl.
    { iDestruct (iProto_le_dual_r with "Hrecv2") as "Hrecv2".
      iDestruct (iProto_le_trans with "Hrecv1 Hrecv2") as "$".
      iApply iProto_le_refl. }
    destruct vs2 as [|v2 vs2]; simpl.
    { iDestruct (iProto_le_dual with "Hrecv1") as "Hrecv1".
      iDestruct (iProto_le_trans with "Hrecv2 Hrecv1") as "Hrecv".
      iExists (iProto_dual p1); iSplitR; first iApply iProto_le_refl.
      by rewrite (involutive iProto_dual). }

    iDestruct (iProto_le_dual with "Hrecv1") as "Hrecv1".
    iDestruct (iProto_le_trans with "Hrecv2 Hrecv1") as "Hrecv".
    rewrite iProto_dual_message; simpl.
    rewrite iMsg_dual_base.

    iDestruct (iProto_le_recv_send_inv with "Hrecv [] []")
      as "(%pt & Hrecv1 & Hrecv2)"; [by rewrite iMsg_base_eq /=..|].

    iNext.
    iDestruct (iProto_le_dual_r with "Hrecv2") as "Hrecv2".
    rewrite iProto_dual_message; simpl.
    rewrite iMsg_dual_base.
    iDestruct (iProto_swap_lst with "Hrecv1") as "(%p1' & Hp1' & Hrecv1)".
    iDestruct (iProto_swap_lst with "Hrecv2") as "(%p2' & Hp2' & Hrecv2)".

    rewrite Nat.add_succ_r /=. iNext.
    iEval (rewrite <-(involutive iProto_dual pt)) in "Hrecv1".
    iDestruct ("IH" with "Hrecv2 Hrecv1") as "Hrecv".
    iNext.
    iDestruct "Hrecv" as "(%p' & Hrecvs2 & Hrecvs1)".
    iExists p'.
    iSplitL "Hp1' Hrecvs2".
    - iDestruct (iProto_le_dual with "Hp1'") as "Hp1'".
      rewrite iProto_dual_message iMsg_dual_base; simpl.
      iApply (iProto_le_trans with "[-Hp1'] Hp1'").
      iApply iProto_le_recv.
      rewrite iMsg_base_eq.
      iIntros (v' p'') "(->&Hp&$)".
      iExists (iProto_dual p1').
      iSplitL; [|done].
      iNext.
      by iRewrite "Hp" in "Hrecvs2".
    - iDestruct (iProto_le_dual with "Hp2'") as "Hp2'".
      rewrite iProto_dual_message iMsg_dual_base; simpl.
      iApply (iProto_le_trans with "[-Hp2'] Hp2'").
      iApply iProto_le_recv.
      rewrite iMsg_base_eq.
      iIntros (v' p'') "(->&Hp&$)".
      iExists (iProto_dual p2').
      iSplitL; [|done].
      iNext.
      by iRewrite "Hp" in "Hrecvs1".
  Qed.

  Lemma iProto_interp_join vs2from1 vs1from2 p p2 vs4from3 vs3from4 p4 :
    iProto_interp vs2from1 vs1from2 p p2 -∗
    iProto_interp vs4from3 vs3from4 (iProto_dual p) p4 -∗
    ▷^(length vs2from1 + length vs4from3)
     iProto_interp (vs1from2 ++ vs4from3) (vs3from4 ++ vs2from1) p2 p4.
  Proof.
    iIntros "Hinterp12 Hinterp34".
    iDestruct (iProto_interp_sym with "Hinterp12") as "Hinterp21".
    iDestruct "Hinterp21" as "(%p12 & H1to2 & H2to1)".
    iDestruct "Hinterp34" as "(%p34 & H4to3 & H3to4)".

    iDestruct (iProto_join_exists with "H4to3 [H2to1]") as "Hjoin".
    { by rewrite (involutive iProto_dual p). }
    iDestruct "Hjoin" as "(%p' & Hp1' & Hp2')".
    iNext.

    iExists p'.
    iSplitR "H3to4 Hp2'".
    - rewrite iProto_app_recvs_app.
      iApply (iProto_le_trans with "[-H1to2] H1to2").
      iApply iProto_app_recvs_le.
      by rewrite (involutive iProto_dual _).
    - rewrite iProto_app_recvs_app.
      iApply (iProto_le_trans with "[-H3to4] H3to4").
      by iApply iProto_app_recvs_le.
  Qed.

  Lemma iProto_join γp1 γp2 vs2from1 vs1from2 γp3 γp4 vs4from3 vs3from4 p :
    iProto_ctx γp1 γp2 vs2from1 vs1from2 -∗
    iProto_ctx γp3 γp4 vs4from3 vs3from4 -∗
    iProto_own γp1 p -∗
    iProto_own γp3 (iProto_dual p) ==∗
    ▷^(length vs2from1 + length vs4from3)
      iProto_ctx γp2 γp4 (vs1from2 ++ vs4from3) (vs3from4 ++ vs2from1).
  Proof.
    iIntros "Hctx1 Hctx3 Hown1 Hown3". unfold iProto_ctx, iProto_own.
    iDestruct "Hctx1" as (p1 p2) "(H●1 & $ & Hinterp12)".
    iDestruct "Hctx3" as (p3 p4) "(H●3 & $ & Hinterp34)".
    iDestruct "Hown1" as (pl1) "[Hle1 H◯1]".
    iDestruct "Hown3" as (pl3) "[Hle3 H◯3]".
    iDestruct (iProto_own_auth_agree with "H●1 H◯1") as "#Hp1".
    iDestruct (iProto_own_auth_agree with "H●3 H◯3") as "#Hp3".
    iModIntro. iApply bi.laterN_later. iNext.
    iRewrite "Hp1" in "Hinterp12".
    iDestruct (iProto_interp_le_l with "Hinterp12 Hle1") as "Hinterp12".
    iRewrite "Hp3" in "Hinterp34".
    iDestruct (iProto_interp_le_l with "Hinterp34 Hle3") as "Hinterp34".
    by iApply (iProto_interp_join with "Hinterp12").
  Qed.
End proto.
