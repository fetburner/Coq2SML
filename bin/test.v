Require Import List.

Inductive tree (A : Type) : Type :=
  | leaf : A -> tree A
  | node : tree A -> tree A -> tree A.

Fixpoint dfs {A} (t : tree A) :=
  match t with
  | leaf x => x :: nil
  | node l r => dfs l ++ dfs r
  end.

Fixpoint dfs_aux {A} (acc : list A) (t : tree A) :=
  match t with
  | leaf x => x :: acc
  | node l r => dfs_aux (dfs_aux acc r) l
  end.
Definition dfs' {A} : tree A -> list A := dfs_aux nil.

Lemma dfs_aux_fact : forall (A : Type) (l : list A) (t : tree A),
  dfs_aux l t = dfs_aux nil t ++ l.
Proof.
  intros A l t.
  generalize dependent l.
  induction t; intros l.
    reflexivity.

    simpl.
    rewrite -> IHt1.
    rewrite -> IHt2.
    rewrite app_assoc.
    congruence.
Qed.

Theorem dfs'_valid : forall (A : Type) (t : tree A), dfs' t = dfs t.
Proof.
  unfold dfs'.
  intros A t.
  induction t.
    reflexivity.

    simpl.
    rewrite -> dfs_aux_fact.
    congruence.
Qed.

Definition dec l := fold_left (fun a b => 10 * a + b) l 0.

Extraction Language Sml.
Extraction tree.
Extract Inductive list => "list" ["[]" "(::)"].
Extract Constant app => "fn x y => x @ y". 
Extract Inductive nat => int ["0" "(fn n => n + 1)"]
  "(fun fO fS n -> if n = 0 then fO () else fS (n-1))".
Extract Constant fold_left => "List.foldl".
Extract Constant plus => "fn x y => x + y".
Extract Constant mult => "fn x y => x * y".
Extraction dfs.
Extraction dfs_aux.
Extraction dfs'.
Extraction dec.
