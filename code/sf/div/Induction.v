Module Induction.
Require Import Bool.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b.
destruct b as [ | ].
destruct c as [ | ].
simpl.
reflexivity.
discriminate.
discriminate.
Qed.


Theorem plus_0_r : forall n , 
   n + 0 = n.
Proof.
intros n.
induction n as [ | n'].
simpl.
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem minus_diag : forall n,
   minus n n = 0.
Proof.
intros n.
induction n as [ | n'].
simpl.
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
   n * 0 = 0.
Proof.
induction n as [ | n'].
simpl.
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
   S (n + m) = n + (S m).
 
Proof.
intros n m.
induction n as [ | n'].
destruct m as [ | m'].
simpl.
reflexivity.
simpl.
reflexivity.
destruct m as [ | m'].
simpl.
rewrite -> IHn'. 
reflexivity.
simpl.
rewrite -> IHn'.
reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
   n + m = m + n. 
Proof.
intros n m.
induction n as [ | n'].
simpl.
rewrite -> plus_0_r.
reflexivity.
simpl.
rewrite -> IHn'.
apply plus_n_Sm.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + ( m + p ) = ( n + m ) + p.
Proof.
intros n m p.
induction n as [ | n'].  
simpl.
reflexivity.
simpl.
apply eq_S.
apply IHn'.
Qed.



Fixpoint double ( n : nat ) := 
  match n with
  |  O => O
  |  S n' => S ( S (double n'))
  end.


Lemma double_plus : forall n,  double n = n + n.
Proof.
intros n.
induction n as [ | n'].
simpl.
reflexivity.
simpl.
apply eq_S.
rewrite <-  plus_n_Sm.
apply eq_S.
apply IHn'.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + ( m + p ) = m + ( n + p).
Proof.
intros n m p.
rewrite -> plus_comm.
rewrite -> plus_assoc.
assert (  p + n = n + p ).
apply plus_comm.
rewrite  <-  plus_assoc.
rewrite -> H.
rewrite -> plus_assoc.
reflexivity.
Qed.


Theorem multi_0_r : forall m : nat , m * 0 = 0.
Proof.
intros m.
induction m as [ | m'].
simpl.
reflexivity.
simpl.
rewrite -> IHm'.
reflexivity.
Qed.

Theorem mult_comm : forall m n : nat , m * n = n * m.
Proof.
intros m n.
induction m as [ | m'].
simpl.
rewrite -> multi_0_r.
reflexivity.
simpl.
rewrite <- mult_n_Sm.
rewrite -> IHm'.
rewrite -> plus_comm.
reflexivity.
Qed.

End Induction.
