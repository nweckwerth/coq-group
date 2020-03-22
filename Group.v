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

Definition isomorphism {A B} (G : Group A) (H : Group B) (map : A -> B) : Prop :=
  bijective map /\ forall a1 a2, map (f a1 a2) = f (map a1) (map a2).

(* Z has two self isomorphisms. *)
Lemma Z_self_isomorphism_1 : isomorphism GroupInt GroupInt (fun a => a).
Proof.
  unfold isomorphism. unfold bijective. intuition.
  - unfold injective. simplify. trivial.
  - unfold surjective. simplify. exists b. trivial.
Qed.

Lemma Z_self_isomorphism_2 : isomorphism GroupInt GroupInt (fun a => Z.opp a).
Proof.
  unfold isomorphism. unfold bijective. intuition.
  - unfold injective. simplify. intuition.
  - unfold surjective. simplify. exists (Z.opp b).
    do 2 (unfold Z.opp). cases b; trivial.
  - simplify. rewrite Z.opp_add_distr. trivial.
Qed.

Definition isomorphic {A B} (G : Group A) (H : Group B) : Prop :=
  exists map, isomorphism G H map.

Theorem self_isomorphic : forall A (G : Group A), isomorphic G G.
Proof.
  simplify. unfold isomorphic. exists (fun a => a). unfold isomorphism.
  unfold bijective. intuition.
  - unfold injective. simplify. trivial.
  - unfold surjective. simplify. exists b. trivial.
Qed.

Print Z.add.

Definition product_op {A B} (fa : A -> A -> A) (fb : B -> B -> B) :
                              (A * B -> A * B -> A * B) :=
  fun x y => (fa (fst x) (fst y), fb (snd x) (snd y)).

Check Build_Group.

(* This is harder than it first seems... *)
(*
Definition product_group {A B} (G : Group A) (H : Group B) : Group (A * B) :=
  Build_Group (A * B)
    (product_op G.(@f A) H.(@f B))
    (G.(@id A), H.(@id B)).
*)

Print Z.add.

Theorem mod_existence : forall (x y : nat),
  x > 0 -> exists a b, y = x * a + b /\ 0 <= b < x.
Proof.
  simplify. exists (y / x), (y mod x). intuition.
  - unfold Nat.div. unfold Nat.modulo. cases x; simplify; try linear_arithmetic.
    admit.
  - apply Nat.mod_upper_bound. intuition.
Admitted.

Fixpoint pow_helper {A} (G : Group A) (g acc : A) (n : nat) : A :=
  match n with
  | 0 => acc
  | S m => pow_helper G g (f acc g) m
  end.

Definition pow {A} (G : Group A) (g : A) (n : nat) : A := pow_helper G g id n.

Definition ord_elt {A} (G : Group A) (g : A) (n : nat) : Prop :=
  n > 0 /\ pow G g n = id /\ forall i, 0 < i < n -> pow G g i <> id.

Theorem pow_acc : forall A (G : Group A) g n acc,
  pow_helper G g acc n = f acc (pow G g n).
Proof.
  intros A G g n. induct n; simplify.
  { unfold pow. simplify. destruct G as [f id assoc id_l id_r inverses]. simplify.
    rewrite id_r. trivial. }
  unfold pow. unfold pow_helper. rewrite IHn. rewrite IHn.
  destruct G as [f id assoc id_l id_r inverses] eqn:HG. simplify. clear IHn.
  rewrite <- HG. rewrite (@id_l g). rewrite (@assoc acc g (pow G g n)). trivial.
Qed.

Theorem pow_sum : forall A (G : Group A) g m n,
  pow G g (m + n) = f (pow G g m) (pow G g n).
Proof.
  simplify.
  destruct G as [f id assoc id_l id_r inverses] eqn:HG. simplify. rewrite <- HG.
  induct n; simplify; try equality.
  { replace (m + 0) with m by linear_arithmetic. assert (pow G g 0 = id0).
    { unfold pow. simplify. admit. (* ? *) }
    rewrite H. rewrite (@id_r0 (pow G g m)). trivial. }
  specialize (IHn f0 id0 assoc0 id_l0 id_r0 inverses0). apply IHn in HG as IH.
  clear IHn.
  replace (m + S n) with (S (m + n)) by linear_arithmetic.
  unfold pow in *. unfold pow_helper in *. rewrite pow_acc. rewrite pow_acc.
  admit.
Admitted.

Theorem pow_prod : forall A (G : Group A) g m n,
  pow G g (m * n) = pow G (pow G g m) n.
Proof.
  simplify. induct n; simplify.
  { replace (m * 0) with 0 by linear_arithmetic. unfold pow. simplify. trivial. }
  admit.
Admitted.

Theorem pow_helper_id : forall A (G : Group A) (n : nat), True.
Proof.
Admitted.

Theorem pow_id : forall A (G : Group A) n,
  pow G id n = id.
Proof.
  simplify. induct n; simplify.
  { unfold pow. simplify. trivial. }
  unfold pow. simplify. rewrite pow_acc. rewrite IHn.
  destruct G. simplify. clear IHn. rewrite id_l0. rewrite id_l0. trivial.
Qed.

Theorem ord_div : forall A (G : Group A) g n n',
  ord_elt G g n -> pow G g n' = id -> n' mod n = 0.
Proof.
  simplify. unfold ord_elt in H. intuition. pose proof (mod_existence n n').
  apply H2 in H1 as H4. invert H4. invert H5. intuition. rewrite H5.
  assert (x0 = 0).
  2: { rewrite H2. replace (n * x + 0) with (x * n) by linear_arithmetic.
  rewrite Nat.mod_mul; linear_arithmetic. }
  rewrite H5 in H0. rewrite pow_sum in H0. rewrite pow_prod in H0.
  rewrite H in H0. rewrite pow_id in H0.
  assert (pow G g x0 = G.(@id A)).
  { assert (G.(@f A) G.(@id A) (pow G g x0) = pow G g x0).
    { destruct G as [f id assoc id_l id_r inverses]. simplify. apply id_l. }
    rewrite <- H0. rewrite H2. trivial. }
  specialize (H3 x0). assert (x0 = 0 \/ x0 > 0) by linear_arithmetic.
  destruct H8; trivial. assert (0 < x0 < n) by linear_arithmetic.
  apply H3 in H9; trivial; equality.
Qed.








