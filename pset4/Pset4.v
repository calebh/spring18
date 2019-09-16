Add LoadPath "/Users/caleb/Documents/spring18/pset4".

Require Import Frap Pset4Sig.
Require Import OrdersFacts.

(* Before beginning this problem set, please see Pset4Sig.v,
 * which contains the instructions.
 *)

(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset4Sig).
Include (OrderedTypeTest Pset4Sig).
(* Print OrderedTypeFacts. *)
(* Print OrderedTypeTest. *)

(* Our solution only needs (at most) the following facts from the above libraries.
 * But it is certainly okay if you use facts beyond these! 
 *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.

Theorem insert_member: forall t n, BST t -> member n (insert n t) = true.
Proof.
  intros.
  induction t.
  simplify.
  pose proof compare_refl n.
  rewrite H0.
  reflexivity.
  unfold insert. fold insert.
  cases (compare n d).
  - simplify.
    rewrite Heq.
    reflexivity.
  - unfold member. fold member.
    cases (compare n d).
    reflexivity.
    unfold BST in H. fold BST in H.
    destruct H. destruct H0. destruct H1.
    propositional.
    equality.
  - unfold member. fold member.
    cases (compare n d).
    reflexivity.
    equality.
    unfold BST in H. fold BST in H.
    destruct H. destruct H0. destruct H1.
    propositional.
Qed.


Lemma lt_insert: forall t n d, BST t /\ compare n d = Lt /\
    tree_lt d t /\ BST (insert n t) -> tree_lt d (insert n t).
Proof.
  intros. destruct H. destruct H0. destruct H1.  
  induct t.
  simplify.
  unfold Singleton.
  unfold tree_lt. unfold tree_forall.
  repeat split; try trivial.
  pose proof compare_lt_iff n d.
  propositional.

  simplify.

  cases (compare n d).
  - assumption.
  - unfold tree_lt. unfold tree_forall. fold tree_forall.
    repeat split.
    
    unfold tree_lt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    assumption.
    
    pose proof (IHt1 n d0).
    propositional.
    unfold tree_lt in H1.
    unfold tree_forall in H1. fold tree_forall in H1.
    unfold tree_lt in H3.
    destruct H1.
    destruct H6.
    propositional.
    unfold BST in H2. fold BST in H2.
    destruct H2.
    propositional.

    pose proof (IHt2 n d0).
    propositional.
    unfold tree_lt in H1.
    unfold tree_forall in H1. fold tree_forall in H1.
    unfold tree_lt in H3.
    destruct H1.
    destruct H6.
    propositional.
  - unfold tree_lt. unfold tree_forall. fold tree_forall.
    repeat split.

    unfold tree_lt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    assumption.

    unfold tree_lt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    destruct H3.
    assumption.

    pose proof (IHt2 n d0).
    propositional.
    unfold tree_lt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    destruct H6.
    unfold tree_lt in H3.
    propositional.
    unfold BST in H2.
    fold BST in H2.
    destruct H2.
    destruct H3.
    destruct H10.
    propositional.
Qed.


Lemma gt_insert: forall t n d, BST t /\ compare n d = Gt /\
    tree_gt d t /\ BST (insert n t) -> tree_gt d (insert n t).
Proof.
  intros. destruct H. destruct H0. destruct H1.  
  induct t.
  simplify.
  unfold Singleton.
  unfold tree_gt. unfold tree_forall.
  repeat split; try trivial.
  pose proof compare_gt_iff n d.
  propositional.

  simplify.

  cases (compare n d).
  - assumption.
  - unfold tree_gt. unfold tree_forall. fold tree_forall.
    repeat split.
    
    unfold tree_gt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    assumption.
    
    pose proof (IHt1 n d0).
    propositional.
    unfold tree_gt in H1.
    unfold tree_forall in H1. fold tree_forall in H1.
    unfold tree_gt in H3.
    destruct H1.
    destruct H6.
    propositional.
    unfold BST in H2. fold BST in H2.
    destruct H2.
    propositional.

    pose proof (IHt2 n d0).
    propositional.
    unfold tree_gt in H1.
    unfold tree_forall in H1. fold tree_forall in H1.
    unfold tree_gt in H3.
    destruct H1.
    destruct H6.
    propositional.
  - unfold tree_gt. unfold tree_forall. fold tree_forall.
    repeat split.

    unfold tree_gt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    assumption.

    unfold tree_gt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    destruct H3.
    assumption.

    pose proof (IHt2 n d0).
    propositional.
    unfold tree_gt in H1.
    unfold tree_forall in H1.
    fold tree_forall in H1.
    destruct H1.
    destruct H6.
    unfold tree_gt in H3.
    propositional.
    unfold BST in H2.
    fold BST in H2.
    destruct H2.
    destruct H3.
    destruct H10.
    propositional.
Qed.

Theorem insert_ok: forall t n, BST t -> BST (insert n t).
Proof.
  intros.
  induction t.
  simplify.
  repeat split; try trivial.
  unfold insert. fold insert.
  unfold BST in H. fold BST in H.

  cases (compare n d).
  - assumption.
  - unfold BST. fold BST.
    destruct H. destruct H0. destruct H1. propositional.
    apply (lt_insert t1 n d).
    propositional.
  - unfold BST. fold BST.
    destruct H. destruct H0. destruct H1. propositional.
    apply (gt_insert t2 n d).
    propositional.
Qed.

Lemma bst_recursive : forall n t1 t2, BST (Node n t1 t2) -> BST t1 /\ BST t2.
Proof.
  intros.
  simplify.
  split; propositional.
Qed.

Lemma tree_gt_recursive : forall d n t1 t2, tree_gt d (Node n t1 t2) -> tree_gt d t1 /\ tree_gt d t2.
Proof.
  intros.
  unfold tree_gt in H.
  unfold tree_forall in H.
  fold tree_forall in H.
  unfold tree_gt.
  unfold tree_forall.
  fold tree_forall.
  propositional.
Qed.

Lemma delete_rightmost_gt: forall d t, tree_gt d t -> tree_gt d (delete_rightmost t).
Proof.
  intros.
  induct t.

  simplify.
  assumption.
  
  pose proof (tree_gt_recursive d d0 t1 t2).
  propositional.
  unfold delete_rightmost. fold delete_rightmost.
  cases t2.
  - assumption.
  - unfold tree_gt. unfold tree_forall. fold tree_forall.
    repeat split.
    unfold tree_gt in H. unfold tree_forall in H. fold tree_forall in H.
    propositional.
    unfold tree_gt in H0.
    assumption.
    unfold tree_gt in H3.
    assumption.
Qed.

Lemma tree_lt_recursive : forall d n t1 t2, tree_lt d (Node n t1 t2) -> tree_lt d t1 /\ tree_lt d t2.
Proof.
  intros.
  unfold tree_lt in H.
  unfold tree_forall in H.
  fold tree_forall in H.
  unfold tree_lt.
  unfold tree_forall.
  fold tree_forall.
  propositional.
Qed.

Lemma delete_rightmost_lt: forall d t, tree_lt d t -> tree_lt d (delete_rightmost t).
Proof.
  intros.
  induct t.

  simplify.
  assumption.
  
  pose proof (tree_lt_recursive d d0 t1 t2).
  propositional.
  unfold delete_rightmost. fold delete_rightmost.
  cases t2.
  - assumption.
  - unfold tree_lt. unfold tree_forall. fold tree_forall.
    repeat split.
    unfold tree_lt in H. unfold tree_forall in H. fold tree_forall in H.
    propositional.
    unfold tree_lt in H0.
    assumption.
    unfold tree_lt in H3.
    assumption.
Qed.

Lemma delete_rightmost_ok : forall t, BST t -> BST (delete_rightmost t).
Proof.
  intros.
  induct t.

  simplify.
  trivial.

  pose proof bst_recursive d t1 t2.
  propositional.

  simplify.
  cases t2.
  - assumption.
  - unfold BST. fold BST.
    repeat split.
    assumption.
    destruct H.
    destruct H4.
    assumption.
    assumption.
    destruct H.
    destruct H4.
    destruct H5.
    
    pose proof (delete_rightmost_gt d (Node d0 t2_1 t2_2)).
    propositional.
Qed.

Lemma tree_lt_trans: forall t d n, BST t -> tree_lt d t -> lt d n -> tree_lt n t.
Proof.
  intros.
  induction t.
  unfold tree_lt.
  simplify.
  trivial.

  unfold tree_lt.
  unfold tree_forall.
  fold tree_forall.

  repeat split.
  
  - unfold tree_lt in H0.
    unfold tree_forall in H0. fold tree_forall in H0.
    propositional.
    apply (lt_trans H2 H1).
  
  - pose proof (tree_lt_recursive d d0 t1 t2).
    unfold BST in H. fold BST in H.
    propositional.
  
  - pose proof (tree_lt_recursive d d0 t1 t2).
    unfold BST in H. fold BST in H.
    propositional.
Qed.

Lemma tree_gt_trans: forall t n d, BST t -> tree_gt d t -> lt n d -> tree_gt n t.
Proof.
  intros.
  induction t.
  unfold tree_gt.
  simplify.
  trivial.

  unfold tree_gt.
  unfold tree_forall.
  fold tree_forall.
  
  repeat split.

  - unfold tree_gt in H0.
    unfold tree_forall in H0. fold tree_forall in H0.
    propositional.
    apply (lt_trans H1 H2).

  - pose proof (tree_gt_recursive d d0 t1 t2).
    unfold BST in H. fold BST in H.
    propositional.

  - pose proof (tree_gt_recursive d d0 t1 t2).
    unfold BST in H. fold BST in H.
    propositional.
Qed.

Lemma rightmost_with_delete: forall t n, BST t -> rightmost t = Some n -> tree_lt n (delete_rightmost t).
Proof.
  intros.
  induction t.
  simplify.
  equality.
  simplify.
  cases t2.
  - simplify.
    invert H0.
    propositional.
  
  - propositional.
    unfold tree_lt.
    unfold tree_forall. fold tree_forall.
    repeat split.

    * simplify.
      cases t2_2.

      + pose proof tree_gt_recursive d d0 t2_1 Leaf.
        propositional.
        invert H0.
        unfold tree_gt in H4.
        unfold tree_forall in H4. fold tree_forall in H4.
        propositional.

      + propositional.
        unfold tree_lt in H6.
        unfold tree_forall in H6. fold tree_forall in H6.
        unfold tree_gt in H4.
        unfold tree_forall in H4. fold tree_forall in H4.
        propositional.
        apply (lt_trans H8 H4).
    
    * simplify.
      propositional.
      cases t2_2.
      
      + invert H0.
        unfold tree_gt in H4.
        unfold tree_forall in H4. fold tree_forall in H4.
        pose proof (tree_lt_trans t1 d n).
        propositional.
      
      + unfold tree_gt in H4.
        unfold tree_forall in H4. fold tree_forall in H4.
        unfold tree_lt in H6.
        unfold tree_forall in H6. fold tree_forall in H6.
        propositional.
        pose proof (lt_trans H8 H4).
        pose proof (tree_lt_trans t1 d n).
        propositional.

    * unfold tree_lt in H6.
      assumption.
Qed.

Lemma rightmost_trans: forall t1 t2 d t, BST t1 -> BST t2 ->
    tree_lt d t1 -> tree_gt d t2 -> rightmost t1 = Some t -> tree_gt t t2.
Proof.
  intros.
  induct t1.
  simplify.
  equality.

  simplify.  
  cases t1_2.
  * invert H3.
    propositional.
    unfold tree_lt in H1.
    unfold tree_forall in H1. fold tree_forall in H1.
    pose proof (tree_gt_trans t2 t d0).
    propositional.
  * pose proof (IHt1_2 t2 d0 t).
    propositional.
    pose proof (tree_lt_recursive d0 d t1_1 (Node d1 t1_2_1 t1_2_2)).
    propositional.
Qed.

Lemma rightmost_lt: forall t1 t d0, BST t1 -> tree_lt d0 t1 ->
    rightmost t1 = Some t -> lt t d0.
Proof.
  intros.
  induct t1.
  simplify.
  equality.
  
  simplify.
  propositional.
  cases t1_2.
  - invert H1.
    unfold tree_lt in H0.
    unfold tree_forall in H0. fold tree_forall in H0.
    propositional.
  - pose proof (IHt1_2 t d0).
    propositional.
    unfold tree_lt in H0.
    unfold tree_forall in H0. fold tree_forall in H0.
    propositional.
    unfold tree_lt in H6.
    unfold tree_forall in H6. fold tree_forall in H6.
    propositional.
Qed.

Lemma rightmost_gt: forall t1 t d0, BST t1 -> tree_gt d0 t1 ->
    rightmost t1 = Some t -> lt d0 t.
Proof.
  intros.
  induct t1.
  simplify.
  equality.
  
  simplify.
  propositional.
  cases t1_2.
  - invert H1.
    unfold tree_gt in H0.
    unfold tree_forall in H0. fold tree_forall in H0.
    propositional.
  - pose proof (IHt1_2 t d0).
    propositional.
    unfold tree_gt in H0.
    unfold tree_forall in H0. fold tree_forall in H0.
    propositional.
    unfold tree_gt in H6.
    unfold tree_forall in H6. fold tree_forall in H6.
    propositional.
Qed.

Lemma delete_lt: forall t d n, BST t -> tree_lt d t -> tree_lt d (delete n t).
Proof.
  intros.
  induct t.
  unfold tree_lt.
  simplify.
  trivial.
  simplify.
  cases (compare n d).
  - cases (rightmost t1).
    * unfold tree_lt.
      simplify.
      repeat split.
      --
        unfold tree_lt in H.
        unfold tree_forall in H. fold tree_forall in H.
        propositional.
        unfold tree_lt in H0.
        unfold tree_forall in H0. fold tree_forall in H0.
        pose proof (rightmost_lt t1 t d0).
        unfold tree_lt in H3.
        propositional.
      --
        pose proof (delete_rightmost_lt d0 t1).
        unfold tree_lt in H0.
        unfold tree_forall in H0. fold tree_forall in H0.
        unfold tree_lt in H1.
        unfold tree_forall in H1. fold tree_forall in H1.
        propositional.
      --
        unfold tree_lt in H0.
        unfold tree_forall in H0. fold tree_forall in H0.
        propositional.
    * pose proof (tree_lt_recursive d0 d t1 t2).
      propositional.
  - unfold tree_lt.
    unfold tree_forall. fold tree_forall.
    repeat split.
    * unfold tree_lt in H0.
      unfold tree_forall in H0. fold tree_forall in H0.
      propositional.
    * pose proof (IHt1 d0 n).
      pose proof (tree_lt_recursive d0 d t1 t2).
      propositional.
    * pose proof (tree_lt_recursive d0 d t1 t2).
      propositional.
  - unfold tree_lt.
    unfold tree_forall. fold tree_forall.
    repeat split.
    * unfold tree_lt in H0.
      unfold tree_forall in H0. fold tree_forall in H0.
      propositional.
    * pose proof (tree_lt_recursive d0 d t1 t2).
      propositional.
    * pose proof (IHt2 d0 n).
      pose proof (tree_lt_recursive d0 d t1 t2).
      propositional.
Qed.

Lemma delete_gt: forall t d n, BST t -> tree_gt d t -> tree_gt d (delete n t).
Proof.
  intros.
  induct t.
  unfold tree_gt.
  simplify.
  trivial.
  simplify.
  cases (compare n d).
  - cases (rightmost t1).
    * unfold tree_gt.
      simplify.
      repeat split.
      --
        unfold tree_gt in H.
        unfold tree_forall in H. fold tree_forall in H.
        propositional.
        unfold tree_gt in H0.
        unfold tree_forall in H0. fold tree_forall in H0.
        pose proof (rightmost_gt t1 t d0).
        unfold tree_gt in H3.
        propositional.
      --
        pose proof (delete_rightmost_gt d0 t1).
        unfold tree_gt in H0.
        unfold tree_forall in H0. fold tree_forall in H0.
        unfold tree_gt in H1.
        unfold tree_forall in H1. fold tree_forall in H1.
        propositional.
      --
        unfold tree_gt in H0.
        unfold tree_forall in H0. fold tree_forall in H0.
        propositional.
    * pose proof (tree_gt_recursive d0 d t1 t2).
      propositional.
  - unfold tree_gt.
    unfold tree_forall. fold tree_forall.
    repeat split.
    * unfold tree_gt in H0.
      unfold tree_forall in H0. fold tree_forall in H0.
      propositional.
    * pose proof (IHt1 d0 n).
      pose proof (tree_gt_recursive d0 d t1 t2).
      propositional.
    * pose proof (tree_gt_recursive d0 d t1 t2).
      propositional.
  - unfold tree_gt.
    unfold tree_forall. fold tree_forall.
    repeat split.
    * unfold tree_gt in H0.
      unfold tree_forall in H0. fold tree_forall in H0.
      propositional.
    * pose proof (tree_gt_recursive d0 d t1 t2).
      propositional.
    * pose proof (IHt2 d0 n).
      pose proof (tree_gt_recursive d0 d t1 t2).
      propositional.
Qed.

Theorem delete_ok: forall t n, BST t -> BST (delete n t).
Proof.
  intros.
  induct t.
  simplify.
  trivial.
  
  simplify.
  cases (compare n d).
  - cases (rightmost t1).
    + simplify.
      repeat split.
      --
        pose proof (IHt1 n).
        destruct H.
        propositional.
        pose proof (delete_rightmost_ok t1).
        propositional.
      --
        pose proof (rightmost_with_delete t1 t).
        propositional.
      --
        propositional.
      --
        pose proof (rightmost_trans t1 t2 d t).
        propositional.
    + propositional.
  - simplify.
    repeat split; try propositional.
    + pose proof (IHt1 n).
      propositional.
    + pose proof (delete_lt t1 d n).
      propositional.
  - simplify.
    repeat split; try propositional.
    + pose proof (IHt2 n).
      propositional.
    + pose proof (delete_gt t2 d n).
      propositional.
Qed.

(* OPTIONAL PART! *)
(*Theorem delete_member: forall t n, BST t -> member n (delete n t) = false.
Proof.
Admitted.*)
