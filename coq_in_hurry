Check True.
Check False.
Check 3.
Check 3*3.
Check 3 > 4.
Check (3+4).
Check (3=5).
Check (3,4).
Check (3, True).
Check ((3=5)/\True).
Check nat -> Prop.
Check (3 <= 6).
Check (3,3=5):nat*Prop.
Check (fun x:nat => x = 3).
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
Check (let f := fun x => (x * 3,x) in f 3).
Locate "_ <= _".
Locate "*".

Check and.
Check (and True False).

Locate "/\".

(* currying *)
Check and True. 


Compute let f := fun x => (x * 3, x) in f 3.

Check let f := fun x1 x2 x3 x4 x5 => x1 + x2 + x3 + x4 + x5 in f 1 2 3 4 5.
Compute let f := fun x1 x2 x3 x4 x5 => x1 + x2 + x3 + x4 + x5 in f 1 2 3 4 5.

Definition example1 := fun x : nat => x*x+2*x+1.

Check example1.

Compute example1 1.


Print example1.

Require Import Bool.

Compute if true then 3 else 5.
Check if true then 3 else 5.

SearchPattern bool.

Search bool.


Require Import Arith.


Definition is_zero (n:nat) :=
  match n with
    0 => true
  | S p => false
end.

Print pred.

Fixpoint sum_n n :=
  match n with
    0 => 0
  | S p => p + sum_n p
end.

Compute sum_n 6.



Fixpoint sum_n2 n s :=
  match n with
    0 => s
  | S p => sum_n2 p (p + s)
end.

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
end.

Compute evenb 9.

Require Import List.

Check 1::2::3::nil.


Compute map (fun x => x + 3) (1::3::2::nil).

Compute map S (1::22::3::nil).


Compute let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.

SearchPattern (nat -> nat -> bool).

Search Nat.eqb.


Check forall x : nat, (x =? x) = true.

Check 3 =? 3.

Compute 3 =? 3.


Locate "_ =? _".

(* exercise 2.5 *)
Fixpoint list_zero_to_nminus1 n := 
  match n with
    0     => nil
  | 1     => 0 :: nil
  | (S p) =>   p :: list_zero_to_nminus1 p
 
end.

Check list_zero_to_nminus1.

Compute list_zero_to_nminus1 4.

Definition head_evb l :=
  match l with 
    nil => false 
  | a::tl => evenb a end.

Check head_evb.

Compute head_evb (2::3::5::nil).


Fixpoint sum_list l :=
  match l with 
    nil => 0 
  | n::tl => n + sum_list tl 
end.

Check sum_list.

Compute sum_list (1::2::3::4::5::nil).


Fixpoint insert n l :=
  match l with
    nil => n::nil
  | a::tl => if n <=? a then n::l else a::insert n tl
end.

Check insert.

Compute insert 7 (1::4::9::nil).

Fixpoint sort l :=
  match l with
    nil => nil
  | a::tl => insert a (sort tl)
end.

Check sort.

Compute sort (1::4::3::22::5::16::7::nil).


Definition checkList l :=
  match l with
    nil       => true
  | a::nil    => true
  | a::b::tl => a <=? b 
end.

Check checkList.
Compute checkList (1::2::4::nil).
Check true && true.

Fixpoint isSorted l :=
  match l with
   nil       => true
 | a::nil    => true
 | a::b::tdl => checkList l &&  
     match tdl with
        nil     => true
      | c::nil  => (b <=? c)
      | c::tdm  => checkList tdl && (b <=? c) && (isSorted tdm)
end
end. 


Check isSorted.
Compute isSorted (1::2::3::4::69::123::23::nil).

Fixpoint countList n l :=
  match l with
   nil     => 0
 | a::tdl  => (if (Nat.eqb a n) then 1 else 0) + countList n tdl
end. 

Check countList.

Compute countList 4 (4::2::4::4::4::nil).



Search True.


Search (_ <= _) (_ + _).

Compute 4 - 3.


SearchPattern (_ + _ <= _ + _).


SearchRewrite (_ + (_ - _)).





















































