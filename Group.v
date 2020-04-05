(* Group definition with some theorems *)

Require Import Frap Datatypes ZArith.

Set Printing Projections.

(* Let's specify the defining characteristics of a group.
   We define groups with left id and left inverse, and derive
   the right id and right inverse rules from these. *)
Definition assoc_group {A} (f : A -> A -> A) : Prop :=
  forall a b c, f a (f b c) = f (f a b) c.

Definition id_l_group {A} (f : A -> A -> A) (id : A) : Prop :=
  forall a, f id a = a.

Definition inv_l_group {A} (f : A -> A -> A) (id : A) : Prop :=
  forall a, exists b, f b a = id.

(* With these definitions, we can define a group. *)
Class Group A : Type := {
  f : A -> A -> A;
  id : A;
  assoc : assoc_group f;
  id_l : id_l_group f id;
  inv_l : inv_l_group f id
}.

(* an example group *)
Theorem Z_inv_l : forall (a : Z.t), exists (b : Z.t), Z.add b a = Z.zero.
Proof.
  simplify. exists (Z.opp a). unfold Z.zero. unfold Z.add.
  cases a; simplify; trivial; apply Z.pos_sub_diag.
Qed.

Instance GroupInt : Group Z.t := {
  f := Z.add;
  id := 0;
  assoc := Z.add_assoc;
  id_l := Z.add_0_l;
  inv_l := Z_inv_l
}.

(* First, we derive the right inverse and right id rules. *)
Definition left_inv {A} (f : A -> A -> A) (id a a' : A) : Prop :=
  f a' a = id.

Definition right_inv {A} (f : A -> A -> A) (id a a' : A) : Prop :=
  f a a' = id.

Theorem left_inv_right_inv : forall A (G : Group A) a a',
  left_inv f id a a' -> right_inv f id a a'.
Proof.
  simplify. destruct G as [f id assoc id_l inv_l]; simplify.
  unfold left_inv, right_inv in *.
  assert (f (f a' a) a' = f id a') by (f_equal; trivial).
  rewrite <- assoc in H0. rewrite id_l in H0. specialize (inv_l a').
  inversion inv_l.
  assert (f x (f a' (f a a')) = f x a') by (f_equal; trivial).
  rewrite assoc in H2. rewrite H1 in H2. rewrite id_l in H2. trivial.
Qed.

Theorem inverses : forall A (G : Group A),
  forall a, exists b, f b a = id /\ f a b = id.
Proof.
  simplify. destruct G as [f id assoc id_l inv_l]; simplify.
  specialize (inv_l a) as inv_l_a. inversion inv_l_a.
  exists x. intuition.
  pose proof (left_inv_right_inv A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              a x); simplify; intuition.
Qed.

Theorem left_id_right_id : forall A (G : Group A),
  forall a, f a id = a.
Proof.
  simplify. destruct G as [f id assoc id_l inv_l]; simplify.
  specialize (inv_l a) as inv_l_a. inversion inv_l_a.
  assert (f x (f (f a x) a) = id).
  { rewrite assoc. rewrite assoc. rewrite H.
    rewrite <- assoc. rewrite H. apply id_l. }
  assert (f x (f (f x a) a) = id)
    by (rewrite H; rewrite id_l; trivial).
  assert (f (f a x) a = f (f x a) a).
  { rewrite <- H1 in H0.
    specialize (inv_l x) as inv_l_x. inversion inv_l_x.
    assert (f x0 (f x (f (f a x) a)) = f x0 (f x (f (f x a) a)))
      by (f_equal; trivial).
    do 2 (rewrite assoc in H3; rewrite H2 in H3; rewrite id_l in H3).
    trivial. }
  rewrite H in H2. rewrite id_l in H2.
  rewrite <- assoc in H2. rewrite H in H2. trivial.
Qed.

Ltac unfold_group A G :=
  pose proof (@left_id_right_id A G) as id_r;
  pose proof (@inverses A G) as inverses;
  destruct G as [f id assoc id_l inv_l]; simplify;
    unfold assoc_group in *;
    unfold id_l_group in *;
    unfold left_inv in *.

(* Let's start with some basic theorems. *)
Theorem id_unique : forall A (G : Group A) e,
  id_l_group f e -> e = id.
Proof.
  simplify. unfold_group A G.
  assert (f e id = id) by (apply H).
  assert (f e id = e) by (apply id_r).
  rewrite H1 in H0. trivial.
Qed.

(* Now we can show that we can cancel, on either side. *)
Theorem left_cancel : forall A (G : Group A) a b c,
  f c a = f c b -> a = b.
Proof.
  simplify. unfold_group A G.
  specialize (inverses c) as Hc. inversion Hc. intuition.
  assert (f x (f c a) = f x (f c b)) by (f_equal; trivial).
  do 2 (rewrite assoc in H0). rewrite H1 in H0.
  do 2 (rewrite id_l in H0). trivial.
Qed.

Theorem right_cancel : forall A (G : Group A) a b c,
  f a c = f b c -> a = b.
Proof.
  simplify. unfold_group A G.
  specialize (inverses c) as Hc. inversion Hc. intuition.
  assert (f (f a c) x = f (f b c) x) by (f_equal; trivial).
  do 2 (rewrite <- assoc in H0). rewrite H2 in H0.
  do 2 (rewrite id_r in H0). trivial.
Qed.

(* With cancellation, we can show that an inverse is unique. *)
Theorem inverse_unique : forall A (G : Group A) a a' a'',
  left_inv f id a a' -> left_inv f id a a'' -> a' = a''.
Proof.
  simplify. rewrite <- H0 in H. apply right_cancel in H. trivial.
Qed.

(* Formula for the inverse of a product. *)
Theorem inverse_product : forall A (G : Group A) a a' b b',
  left_inv f id a a' (A := A) -> left_inv f id b b' ->
    left_inv f id (f a b) (f b' a').
Proof.
  simplify. unfold_group A G.
  rewrite <- assoc. replace (f a' (f a b)) with b; trivial.
  rewrite assoc. rewrite H. rewrite id_l. trivial.
Qed.

(* A helper lemma about modulo; this probably already exists somewhere. *)
Lemma mod_existence : forall (x y : nat),
  x > 0 -> exists a b, y = x * a + b /\ 0 <= b < x.
Proof.
  simplify. exists (y / x), (y mod x). intuition.
  - unfold Nat.div. unfold Nat.modulo. cases x; simplify; try linear_arithmetic.
    admit.
  - apply Nat.mod_upper_bound. intuition.
Admitted.

(* We define the power function recursively with an accumulator.
   Perhaps this should be moved up somewhere earlier? *)
Fixpoint pow {A} (f : A -> A -> A) (acc g : A) (n : nat) : A :=
  match n with
  | 0 => acc
  | S m => pow f (f acc g) g m
  end.

(* We can get a lot of results about pow. *)

(* g^0 = 1 *)
Theorem pow_0 : forall A (G : Group A) acc g,
  pow f acc g 0 = acc.
Proof. simplify. trivial. Qed.

(* g^1 = g *)
Theorem pow_1 : forall A (G : Group A) acc g,
  pow f acc g 1 = f acc g.
Proof. simplify. trivial. Qed.

(* 1^n = 1. *)
Theorem pow_id : forall A (G : Group A) n,
  pow f id id n = id.
Proof.
  simplify; unfold_group A G. induct n; simplify; intuition.
  rewrite id_l; trivial.
Qed.

(* Our first such result of some weight: pulling out the accumulator. *)
(* This may not seem to represent anything interesting mathematically,
   but it's very useful for us in further proofs. *)
Theorem pow_acc : forall A (G : Group A) g n acc,
  pow f acc g n = f acc (pow f id g n).
Proof.
  simplify; unfold_group A G. induct n; simplify.
  { rewrite id_r. trivial. }
  rewrite id_l. rewrite IHn; trivial.
  replace (pow f g g n) with (f g (pow f id g n)) by (rewrite <- IHn; trivial).
  rewrite (@assoc acc g (pow f id g n)). trivial.
Qed.

(* Powers commute with the base, or g * g^n = g^n * g. *)
Theorem pow_base_commute : forall A (G : Group A) g n,
  f g (pow f id g n) = f (pow f id g n) g.
Proof.
  simplify; unfold_group A G. induct n; simplify; rewrite id_l.
  { rewrite id_r; trivial. }
  pose proof (pow_acc A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g n g); simplify; rewrite H.
  replace (f g (f g (pow f id g n))) with (f g (f (pow f id g n) g)).
  2: { f_equal. rewrite IHn; trivial. }
  rewrite assoc. trivial.
Qed.

(* More interesting: g^(m+n) = g^m * g^n. *)
Theorem pow_sum : forall A (G : Group A) g m n,
  pow f id g (m + n) = f (pow f id g m) (pow f id g n).
Proof.
  (* We could move the pose proofs here and look slick,
     but I want to make sure I remember the formatting. Plus, it looks fine. *)
  simplify; unfold_group A G. induct n; simplify.
  { replace (m + 0) with m by linear_arithmetic. rewrite id_r. trivial. }
  replace (m + S n) with (S (m + n)) by linear_arithmetic. rewrite id_l.
  pose proof (pow_acc A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g n g); simplify; rewrite id_l; rewrite H; clear H.
  pose proof (pow_acc A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g (m + n) g); simplify; rewrite H; clear H.
  rewrite IHn; trivial. rewrite assoc.
  pose proof (pow_base_commute A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g m); simplify; rewrite H; clear H.
  rewrite assoc. trivial.
Qed.

(* Also interesting: g^(m*n) = (g^m)^n. *)
Theorem pow_prod : forall A (G : Group A) g m n,
  pow f id g (m * n) = pow f id (pow f id g m) n.
Proof.
  simplify; unfold_group A G. induct n; simplify.
  { replace (m * 0) with 0 by linear_arithmetic. unfold pow. trivial. }
  rewrite id_l. replace (m * S n) with (m * n + m) by linear_arithmetic.
  pose proof (pow_sum A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g (m * n) m); simplify; rewrite H; clear H.
  rewrite IHn; trivial.
  pose proof (pow_acc A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              (pow f id g m) n (pow f id g m)); simplify; rewrite H; clear H.
  pose proof (pow_base_commute A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              (pow f id g m) n); simplify; rewrite H; clear H.
  trivial.
Qed.

(* Using pow, we can define cyclic groups. *)
Definition cyclic_group {A} (f : A -> A -> A) (id : A) : Prop :=
  exists g, forall a, exists n, pow f id g n = a.

(* While we're defining things about groups... *)
Definition abelian_group {A} (f : A -> A -> A) : Prop :=
  forall a b, f a b = f b a.

(* We can also define the order of an element in the group. *)
Definition ord_elt {A} (f : A -> A -> A) (id g : A) (n : nat) : Prop :=
  n > 0 /\ pow f id g n = id /\ forall i, 0 < i < n -> pow f id g i <> id.

(* A big one: if g^n = 1, then ord(g) | n. *)
Theorem ord_div : forall A (G : Group A) g n n',
  ord_elt f id g n -> pow f id g n' = id -> n' mod n = 0.
Proof.
  simplify; unfold_group A G.
  unfold ord_elt in H. intuition. pose proof (mod_existence n n').
  apply H2 in H1 as H4; clear H2. invert H4. invert H2. intuition. rewrite H2.
  assert (x0 = 0).
  2: { rewrite H5. replace (n * x + 0) with (x * n) by linear_arithmetic.
       rewrite Nat.mod_mul; linear_arithmetic. }
  rewrite H2 in H0; clear H2.
  pose proof (pow_sum A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g (n * x) x0); simplify; rewrite H2 in H0; clear H2.
  pose proof (pow_prod A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              g n x); simplify; rewrite H2 in H0; clear H2.
  rewrite H in H0.
  pose proof (pow_id A
                {| f := f; id := id; assoc := assoc;
                   id_l := id_l; inv_l := inv_l |}
              x); simplify; rewrite H2 in H0; clear H2.
  rewrite id_l in H0. specialize (H3 x0).
  assert (x0 = 0 \/ x0 > 0) by linear_arithmetic.
  destruct H2; trivial. assert (0 < x0 < n) by linear_arithmetic.
  apply H3 in H5; equality.
Qed.






(* Some stuff about maps; let's move this to later maybe. *)
Definition injective {A B} (map : A -> B) : Prop :=
  forall a1 a2, a1 <> a2 -> map a1 <> map a2.

Definition surjective {A B} (map : A -> B) : Prop :=
  forall b, exists a, map a = b.

Definition bijective {A B} (map : A -> B) : Prop :=
  injective map /\ surjective map.

Theorem left_mul_bijective : forall A (G : Group A) g,
  bijective (fun a => f g a).
Proof.
  simplify; unfold_group A G. unfold bijective. intuition.
  - unfold injective. simplify. intuition. apply H.
    specialize (inverses g) as Hg. inversion Hg. intuition.
    assert (f (f x g) a1 = f (f x g) a2).
    { do 2 (rewrite <- assoc). rewrite H0. trivial. }
    rewrite H2 in H1. do 2 (rewrite id_l in H1). trivial.
  - unfold surjective. simplify.
    specialize (inverses g) as Hg. inversion Hg. intuition.
    exists (f x b). rewrite assoc. rewrite H1. apply id_l.
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


