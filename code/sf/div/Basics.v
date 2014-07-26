Module Basic.

Inductive num : Type :=
    | Zero : num
    | Succ : num -> num . 
   
Inductive bool : Type := 
    | True : bool
    | False : bool .

Definition pred ( n : num ) : num := 
    match n with
      | Zero => Zero
      | Succ n' => n
    end.

Eval compute in (pred Zero).
Eval compute in (pred (Succ Zero)).

Definition iszero (n : num ) : bool := 
     match n with
      | Zero => True
      | Succ _ => False
     end.

Eval compute in (iszero Zero).
Eval compute in (iszero (Succ Zero)).

Fixpoint sum ( n : num ) ( m : num ) : num := 
     match m with
       | Zero => n
       | Succ n' => Succ (sum n n')
     end.

Eval compute in (sum Zero (Succ Zero)).
Eval compute in (sum (Succ Zero) (Succ Zero)).

Fixpoint product ( n : num ) ( m : num ) : num := 
      match m with 
       | Zero => Zero
       | Succ n' => sum n (product n n')
      end.

Eval compute in (product (Succ (Succ Zero)) (Succ (Succ Zero))).

Fixpoint less ( n : num ) ( m : num ) : bool := 
      match n, m with
        | Zero, Zero => False
        | Zero, Succ n' => True
        | Succ n', Zero => False
        | Succ n', Succ m' => less n' m'
      end.

Eval compute in (less Zero (Succ Zero)).

Eval compute in (less (Succ Zero) Zero).


Fixpoint eq ( n : num ) ( m : num ) : bool := 
      match n, m with
        | Zero, Zero => True
        | Zero, Succ m' => False
        | Succ n', Zero => False
        | Succ n', Succ m' => eq n' m'
      end.

Eval compute in (eq Zero Zero).

Definition or ( a : bool ) ( b : bool ) : bool := 
       match a with
         | True => True
         | False => b
       end.

Eval compute in (or False True).
Eval compute in (or True False).

Definition and ( a : bool ) (b : bool) : bool := 
       match a with
         | True => b
         | False => False
       end.

Eval compute in (and False False).
Eval compute in (and True True).

Definition lesseq ( n : num ) ( m : num ) : bool := 
      or (less n m) (eq n m) .    

Eval compute in (lesseq Zero Zero).

Definition not ( a : bool ) : bool := 
      match a with 
        | True => False
        | False => True
      end.

Definition greater ( n : num ) ( m : num ) : bool := 
     not (lesseq n m).

Definition greatereq (n : num)  (m : num) : bool := 
     not (less n m).


Fixpoint subtract (n : num) (m : num) : num := 
     match n, m with
       | Zero, _ => Zero
       |  _ , Zero => n
       | Succ n' , Succ m' => subtract n' m'
     end.

Fixpoint factorial (n : num) := 
      match n with 
       | Zero => Succ Zero
       | Succ n' => product n (factorial n')
      end.

Eval compute in (factorial (Succ (Succ (Succ Zero)))).



Theorem add_commutative : forall a b : nat , a + b = b + a.
Proof. admit. Qed.

Theorem multi_commutative : forall a b : nat, a * b = b * a.
Proof. admit. Qed.

Theorem add_identity : forall a : num, sum a Zero = a.
Proof. intros. reflexivity. Qed.

Theorem multi_identity : forall a : num, product a (Succ Zero) = a.
Proof. intros. reflexivity. Qed.

Example factorial_example : factorial (Succ Zero) = Succ Zero.
Proof. reflexivity. Qed.

Theorem theorem1 : forall a b c : nat, a = b -> b = c -> a + b = b +c .
Proof.  intros.  rewrite -> H. rewrite -> H0. reflexivity. Qed.

Theorem theorem2 : forall a b : nat, a = b + 1 -> a * ( b + 1 ) = a * a.
Proof. intros. rewrite <- H. reflexivity. Qed.

Theorem theorem3 : forall a b : nat, a = b + 1 -> a * ( 1 + b ) = a * a.
Proof. intros. rewrite -> H. rewrite add_commutative. reflexivity. Qed.

End Basic.
