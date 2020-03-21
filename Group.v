Require Import Frap Datatypes ZArith.

Set Printing Projections.

Class Group A : Type := {
  f : A -> A -> A;
  id : A;
  assoc : forall a b c, f a (f b c) = f (f a b) c;
  id_l : forall a, f id a = a;
  id_r : forall a, f a id = a;
  inverses : forall a, exists b, f a b = id
}.

(* an example! *)

Theorem Z_inverses : forall (a : Z.t), exists (b : Z.t), Z.add a b = Z.zero.
Proof.
  simplify. exists (Z.opp a). unfold Z.zero. unfold Z.add.
  cases a; simplify; trivial; apply Z.pos_sub_diag.
Qed.

Instance GroupInt : Group Z.t := {
  f := Z.add;
  id := 0;
  assoc := Z.add_assoc;
  id_l := Z.add_0_l;
  id_r := Z.add_0_r;
  inverses := Z_inverses
}.

Definition is_id {A} (G : Group A) (e : A) : Prop := 
  forall (a : A), f a e = a /\ f e a = a.

Theorem id_unique : forall A G e, is_id G e -> e = id (A := A).
Proof.
  simplify. destruct G as [f id assoc id_l id_r inverses]. unfold is_id in H. simplify.
  assert (f id e = e) by (apply id_l).
  assert (f id e = id) by (specialize (H id); intuition).
  rewrite H0 in H1. trivial.
Qed.

Definition is_inverse {A} (G : Group A) (a a' : A) : Prop := f a a' = id /\ f a' a = id.

Theorem inverse_unique : forall A G a a' a'',
  is_inverse G a a' (A := A) -> is_inverse G a a'' -> a' = a''.
Proof.
  simplify. destruct G as [f id assoc id_l id_r inverses]. unfold is_inverse in *.
  simplify. intuition. assert (f a'' (f a a') = a'').
  { rewrite H1. rewrite id_r. trivial. }
  rewrite assoc in H0. rewrite H3 in H0. rewrite id_l in H0. trivial.
Qed.

Theorem inverse_inverse : forall A G a a',
  is_inverse G a a' (A := A) -> is_inverse G a' a.
Proof.
  simplify. unfold is_inverse in *. intuition.
Qed.

Theorem inverse_product : forall A G a a' b b',
  is_inverse G a a' (A := A) -> is_inverse G b b' -> is_inverse G (f a b) (f b' a').
Proof.
  simplify. destruct G as [f id assoc id_l id_r inverses]. unfold is_inverse in *.
  simplify. intuition.
  - rewrite <- assoc. replace (f b (f b' a')) with a'; trivial.
    rewrite assoc. rewrite H. rewrite id_l. trivial.
  - rewrite <- assoc. replace (f a' (f a b)) with b; trivial.
    rewrite assoc. rewrite H2. rewrite id_l. trivial.
Qed.

Definition injective {A B} (map : A -> B) : Prop :=
  forall a1 a2, a1 <> a2 -> map a1 <> map a2.

Definition surjective {A B} (map : A -> B) : Prop :=
  forall b, exists a, map a = b.

Definition bijective {A B} (map : A -> B) : Prop :=
  injective map /\ surjective map.

(* Why can't I apply this thing? *)
Theorem left_inv_right_inv : forall A (G : Group A) a a',
  f a a' = id <-> f a' a = id (A := A).
Proof.
  simplify. destruct G as [f id assoc id_l id_r inverses]. simplify. intuition.
  - specialize (inverses a') as Ha'. inversion Ha'.
    assert (f (f a a') x = f id x) by (rewrite H; trivial). rewrite <- assoc in H1.
    rewrite H0 in H1. rewrite id_l in H1. rewrite id_r in H1. rewrite H1. trivial.
  - specialize (inverses a) as Ha. inversion Ha.
    assert (f (f a' a) x = f id x) by (rewrite H; trivial). rewrite <- assoc in H1.
    rewrite H0 in H1. rewrite id_l in H1. rewrite id_r in H1. rewrite H1. trivial.
Qed.

Theorem left_mul_bijective : forall A (G : Group A) g,
  bijective (fun a => f g a).
Proof.
  simplify. destruct G as [f id assoc id_l id_r inverses]. unfold bijective.
  simplify. intuition.
  - unfold injective. simplify. intuition. apply H.
    specialize (inverses g) as Hg. inversion Hg. assert (f x g = id).
    { specialize (inverses x) as Hx. inversion Hx.
      assert (f g (f x x0) = g) by (rewrite H2; apply id_r).
      rewrite assoc in H3. rewrite H1 in H3. rewrite id_l in H3.
      rewrite <- H3. trivial. }
    assert (f (f x g) a1 = f (f x g) a2).
    { do 2 (rewrite <- assoc). rewrite H0. trivial. }
    rewrite H2 in H3. do 2 (rewrite id_l in H3). trivial.
  - unfold surjective. simplify.
    specialize (inverses g) as Hg. inversion Hg.
    exists (f x b). rewrite assoc. rewrite H. apply id_l.
Qed.




