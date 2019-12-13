Require Import Reals Psatz Lra Bool RelationClasses.
From Coquelicot Require Import Continuity 
  Derive Hierarchy AutoDerive Rbar Complex RInt RInt_analysis
  Rcomplements.
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


Instance cls_rle_refl: Reflexive Rle := Rle_refl. 
Instance cls_rle_trans: Transitive Rle := Rle_trans. 
Instance cls_rlt_trans: Transitive Rlt := Rlt_trans. 

Lemma eqn_notation {A}: forall x y (R: A -> A -> Prop) P, 
  (R x y) ->
  (R x y -> P) -> P.
Proof. tauto. Qed.

Tactic Notation 
  "`Begin" uconstr(R) constr(x):=
  refine (eqn_notation (x:=x) (R:=R) _ _).

Tactic Notation
  "|" "{" uconstr(x) "}" tactic(t) :=
   refine (transitivity (y:= x) _ _);
   first (t;
   try now reflexivity
   ).


Tactic Notation
  "`Done" :=
   (auto using reflexivity).


Lemma Cmod_prod_norm: forall x1 x2,
  Cmod (x1,x2) = prod_norm (K:= R_AbsRing) (x1,x2).
Proof.
  move => x y.
  rewrite /Cmod //= /prod_norm //= /norm //= /abs //=.
  f_equal.
  field_simplify.
  rewrite ? pow2_abs.
  auto.
Qed.
Ltac unfold_alg := do ! rewrite 
  /norm //= -?Cmod_prod_norm //= 
  /minus //= /plus //= /opp //= /scal //=
  /mult //= /abs //= /prod_ball /AbsRing_ball //= /ball //= 
  /prod_plus //= /prod_opp //=
.
Lemma R_opp_1: forall x, (-(1) * x) = -x.
Proof. move => x. field_simplify_eq. auto. Qed.

Ltac simplify_R p := 
  let H := fresh in 
  (have H: (p=p) by auto);
  rewrite {1}/p in H;
  field_simplify in H;
  rewrite -{}H {p}
.
Ltac split_as_R2 e p := 
  let H := fresh in 
  let H' := fresh in 
  case e: p;
  rewrite /p /Cmult /Copp /Cplus //= in e;
  case: e => H H';
  rewrite -{}H -{}H' {p}
.
Ltac simplify_as_R2 e p := 
  let H := fresh in 
  let H' := fresh in 
  case e: p;
  rewrite /p /Cmult /Copp /Cplus //= in e;
  case: e => H H';
  field_simplify in H;
  field_simplify in H';
  rewrite -{}H -{}H' {p}
.
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


Ltac elim_norms := do !
  match goal with 
  | |- context[Cmod] => rewrite !/Cmod
  | |- sqrt _ = sqrt _ => f_equal
  | |- (?x * _ = ?x * _)%R => f_equal
  | |- (?x + _ = ?x + _)%R => f_equal
  | |- (?x * _ = ?x * _)%C => f_equal
  | |- (?x + _ = ?x + _)%C => f_equal
  | |- sqrt _ = _ => apply sqrt_lem_1
  | |- sqrt _ < sqrt _ => apply sqrt_lt_1
  | |- Rabs _ <= Rabs _ => apply Rsqr_eq_abs_0
  | |- 0 <= Rabs _ => by apply Rabs_pos
  | |- 0 <= ?x^2 - 2 * ?x * ?y + ?y ^2 => apply diff_sqr
  | _ => rewrite ? (sqrt_le_left, abs_sqr, sqrt_Rsqr, sqrt_square, sqrt_pow2, Rsqr_abs);
         (simpl; field_simplify)
end.
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


Lemma is_derive_pair_iff {K : AbsRing} {M : NormedModule K} :
  forall (f g : K -> M) f' g' (x: K), 
  (is_derive f x (f') /\
  is_derive g x (g')) <->
  is_derive (fun q => (f q, g q)) x (f', g').
Proof.
  move => f g f' g' x. 
  split;
  first by move => [ ? ?]; apply: is_derive_pair; auto.
  move => H; split.
  - eapply (is_derive_ext (fun t => fst (f t, g t) )); first by auto.
    replace (f') with (fst (f', g')); last by auto.
    apply (filterdiff_comp _ fst _ fst H). 
    apply filterdiff_fst.
  - eapply (is_derive_ext (fun t => snd (f t, g t) )); first by auto.
    replace (g') with (snd (f', g')); last by auto.
    apply (filterdiff_comp _ snd _ snd H). 
    apply filterdiff_snd.
Qed.
Hint Resolve is_derive_pair : derive_compute.
Hint Resolve derive_ex_derive : derive_compute.
Hint Resolve filterdiff_ex_filterdiff : derive_compute.
Hint Resolve ex_derive_filterdiff : derive_compute.
Hint Immediate filterdiff_fst : derive_compute.
Hint Immediate filterdiff_snd : derive_compute.

Lemma continuous_pair {T U1 U2: UniformSpace}:
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

Ltac auto_continuous_aux :=
  first 
  [ apply: continuous_id
  | apply: continuous_const
  | apply: continuous_pair
  | apply: continuous_scal
  | apply: continuous_minus
  | apply: continuous_plus
  | apply: continuous_fst
  | apply: continuous_snd
  | apply: continuous_opp].
Ltac auto_continuous x z := 
  have: continuous x z;
  rewrite /x;
  repeat auto_continuous_aux.

Ltac destruct_match := 
  match goal with 
  | |- context[match ?x with _ => _ end]  => 
    let p := fresh in
    let l := fresh in
    set p := x;
    case l: p
  end.
    
Lemma RleP : forall x y,
  reflect (x <= y) (Rle_dec x y).
Proof.
  move => x y.
  apply/iff_reflect.
  case(Rle_dec x y) => H; split => H'; auto.
  discriminate.
Qed.


Lemma Rabs_lt_between_min_max: 
   forall x y z : R, Rmin x y < z < Rmax x y -> Rabs (z - y) < Rabs (x - y).
Proof.
  move => x y z.
  rewrite /Rmin /Rmax.
  set p := (Rle_dec _ _).
  case: p.
  - move => _ ord.
    rewrite ?Rabs_left; lra.
  - move => _ ord.
    rewrite ?Rabs_right; lra.
Qed.
Lemma Rabs_le_between_min_max_2: 
   forall x y z : R, Rmin x y <= z <= Rmax x y -> Rabs (z - x) <= Rabs (y - x).
Proof.
  move => x y z.
  rewrite Rmin_comm Rmax_comm => *.
  apply (Rabs_le_between_min_max y x z).
  auto.
Qed.

Ltac combine_local := 
match goal with 
| H1: @locally ?T _ _, H2: @locally ?T _ _  |- _ => 
  have:= filter_and _ _ H1 H2;
  try move /(_ ltac:(apply locally_filter)) {H1 H2}

end.