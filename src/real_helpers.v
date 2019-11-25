Require Import Reals Psatz Lra.
From Coquelicot Require Import Continuity 
  Derive Hierarchy AutoDerive Rbar Complex .
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope program_scope.
Open Scope general_if_scope.

Create HintDb derive_compute.

Require Import ext_rewrite.

Open Scope R.

Lemma sqrt_lt_left : forall x y, 0 <= x -> 0 <= y -> sqrt x < y <-> x < y^2.
Proof.
  move => x y xge yge; split; move => H.
  - apply sqrt_lt_0_alt.
    rewrite /pow. 
    rewrite Rmult_1_r.
    rewrite sqrt_square; auto.
  - pose z := y * y.
    rewrite -(sqrt_lem_1 z y) /z.
    2-4: nra.
    apply sqrt_lt_1_alt; split; nra.
Qed.

Lemma sqrt_le_left : forall x y, 0 <= x -> 0 <= y -> sqrt x <= y <-> x <= y^2.
Proof.
  move => x y xge yge; split; move => H.
  - apply sqrt_le_0.
    1,2: nra.
    rewrite /pow. 
    rewrite Rmult_1_r.
    rewrite sqrt_square; auto.
  - pose z := y * y.
    rewrite -(sqrt_lem_1 z y) /z.
    2-4: nra.
    apply sqrt_le_1; nra.
Qed.


Lemma rabs_rewrite : forall x y, Rabs x < y <-> (x < y /\ -y < x).
Proof.
  move => x y; split => H.
  -  apply Rabs_def2. auto.
  - apply Rabs_def1; tauto.
Qed.

Lemma le_square : forall x y, 0 <= x -> 0 <= y ->  x < y <-> (x * x < y * y).
Proof.
  move => *; split => H; nra.
Qed.

Lemma abs_sqr: forall x, Rabs x * Rabs x = x * x.
Proof.
  move => x. rewrite -[_ * _]/(Rsqr _). rewrite -Rsqr_abs; auto.
Qed.

Lemma square_in_circle: forall x1 x2 y1 y2 e,
  0 < e -> 
  abs (y1 - x1) < e ->
  abs (y2 - x2) < e ->
  sqrt((y1 - x1)^2 + (y2 - x2)^2) < 2*e.
Proof.
  move => x1 x2 y1 y2 e epos U V.
  apply sqrt_lt_left.
  2: lra.
  { apply Rplus_le_le_0_compat; apply pow2_ge_0. }
  move: U V.
  rewrite le_square //=. 
  3: nra.
  2: apply abs_ge_0.
  move => H1.
  rewrite le_square //=. 
  3: nra.
  2: apply abs_ge_0.
  move: H1.
  rewrite /abs //= abs_sqr abs_sqr.
  nra.
Qed.
Lemma diff_sqr : forall x y, 0 <= x^2 - 2 * x * y + y ^2.
Proof.
  move => x y.
  have <-: (x-y)^2 = x ^ 2 - 2*x*y + y^2.
  - nra.
  - rewrite -Rsqr_pow2; apply Rle_0_sqr.
Qed.

Ltac auto_derive_all_aux := 
  first [progress eauto with derive_compute | auto_derive]; 
  lra.

(** Gets a diff into a is_derive form, then tries a computation. Or it fails.*)
Ltac auto_derive_all :=
  match goal with 
  | |- is_derive _ _ _ => auto_derive_all_aux
  | |- filterdiff id _ ?y => by auto
  | |- filterdiff _ (locally _) _ =>
      (progress rewrite -/(is_derive _ _ _)); auto_derive_all_aux
  | |- filterdiff _ ?F _ => 
       progress rewrite [F]/(within _ (locally _));
       eapply (filterdiff_locally _ _);
       first apply filter_le_within;
       auto_derive_all_aux
    
  | |- ex_derive _ _ => auto_derive_all_aux
  | |- ex_filterdiff id _ => by auto
  | |- ex_filterdiff _ (locally _) =>
      (progress rewrite -/(ex_derive _ _)); auto_derive_all_aux
  | |- ex_filterdiff _ ?F => 
       progress rewrite [F]/(within _ (locally _));
       eapply (ex_filterdiff_locally _);
       first apply filter_le_within;
       apply ex_derive_filterdiff;
       auto_derive_all_aux
    
  end.


Hint Immediate filterdiff_id.
Hint Immediate ex_filterdiff_id.

Lemma is_derive_pair {K : AbsRing} {M : NormedModule K} :
  forall (f g f' g': K -> M) (x: K), 
  is_derive f x (f' x) ->
  is_derive g x (g' x) ->
  is_derive (fun q => (f q, g q)) x (f' x, g' x).
Proof.
  pose h (p q:M) := (p,q).
  move => *.
  apply: (filterdiff_comp_2 _ _ h).
  - auto_derive_all. 
  - auto_derive_all. 
  - under (ext_filterdiff_d) => x.
      have e: ((x.1, x.2)=x); first by case: x. 
      rewrite e.
    over.
    rewrite /h //=.
    under ext_filterdiff_loc.
      { apply global_local; 
        instantiate (1:= id); 
        auto.
      }
      move => x _. 
      have ->: ((x.1, x.2)=x); first by case: x.
    over.
    auto_derive_all.
Qed.

Ltac proj_proof eps := 
   apply (filter_imp (fun _ => True)); 
   [
   move => z _;
   rewrite {2}/minus;
   rewrite minus_eq_zero;
   rewrite norm_zero;
   apply Rmult_le_pos;
     [ pose proof cond_pos eps; nra
     | apply norm_ge_0 ]
   |by apply filter_true]
  .
Lemma filterdiff_fst: forall 
  {K: AbsRing}
  {V1 V2: NormedModule K} 
  (F: (V1*V2 -> Prop) -> Prop)
  {FF : Filter F},
  filterdiff (K:=K) fst F fst.
Proof.
  move => *. 
  apply filterdiff_linear.
  apply is_linear_fst.
Qed.
Lemma filterdiff_snd: forall 
  {K: AbsRing}
  {V1 V2: NormedModule K} 
  (F: (V1*V2 -> Prop) -> Prop)
  {FF : Filter F},
  filterdiff (K:=K) snd F snd.
Proof.
  move => *. 
  apply filterdiff_linear.
  apply is_linear_snd.
Qed.

Hint Resolve is_derive_pair : derive_compute.
Hint Resolve derive_ex_derive : derive_compute.
Hint Resolve filterdiff_ex_filterdiff : derive_compute.
Hint Resolve ex_derive_filterdiff : derive_compute.
Hint Immediate filterdiff_fst : derive_compute.
Hint Immediate filterdiff_snd : derive_compute.

Lemma continous_pair {T U1 U2: UniformSpace}:
  forall (f: T -> U1) (g: T -> U2) t, 
  continuous f t ->
  continuous g t ->
  continuous (fun q => (f q, g q)) t.
Proof.
  move => f g t ctsf ctsg.
  rewrite /continuous.
  eapply filterlim_filter_le_2 .
  2: eapply filterlim_pair.
  2: apply ctsf.
  2: apply ctsg.
  rewrite /filter_le => P.
  case => eps //=.
  rewrite /ball //= /prod_ball //=.
  move => H.
  eapply Filter_prod.
  - eapply locally_ball .
  - eapply locally_ball.
  - move => a b bf bg. 
    apply H.
    eauto.
Qed.