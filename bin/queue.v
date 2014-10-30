Require Import List Arith Program.

Module Type QUEUE.
  Parameter queue : Type -> Type.
  Parameter empty : forall A, queue A.
  Parameter isEmpty : forall A, queue A -> bool.
  Parameter enqueue : forall A, A -> queue A -> queue A.
  Parameter dequeue : forall A, queue A -> option (queue A * A).
End QUEUE.

Module Queue <: QUEUE.
  Definition queue (A : Type) := (list A * list A)%type.

  Definition empty (A : Type) : queue A := ([], []).
  Definition isEmpty A (q : queue A) :=
    match q with
    | ([], []) => true
    | _ => false
    end.
  Definition enqueue A (a : A) (q : queue A) :=
    let (old, new) := q in
    (old, a :: new).
  Definition dequeue A (q : queue A) : option (queue A * A).
    destruct q as [old new].
    destruct old.
      remember new.
      case_eq new.
        intros H0.
        exact None.

        intros a new' H0.
        case_eq (rev new).
          intros Hcontra.
          exfalso.
          rewrite H0 in Hcontra.
          simpl in Hcontra.
          symmetry in Hcontra.
          apply (app_cons_not_nil _ _ _ Hcontra).

          intros a0 old H1.
          exact (Some ((old, []), a)).
      exact (Some ((old, new), a)).
  Defined.
End Queue.

Extraction Language Sml.
Extraction "queue.sml" Queue.

