Require Import Reals Psatz Lra Bool RelationClasses.
From Coquelicot Require Import Continuity 
  Derive Hierarchy AutoDerive Rbar Complex RInt RInt_analysis
  Rcomplements Derive_2d.
From Coq Require Import ssreflect ssrfun ssrbool ssrmatching.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope program_scope.
Open Scope general_if_scope.

(* rewriting some of the extentionality lemmas from 
coquelicot to be usable with the new under tactic.
*)

Tactic Notation "simplify_term" ssrpatternarg(pat) := 
  let p := fresh in 
  let eq_p := fresh in
  ssrpattern pat;
  intro p;
  pose proof (refl_equal p) as eq_p;
  unfold p at 1 in eq_p;
  field_simplify in eq_p;
  rewrite -{}eq_p; 
  clear p.

Tactic Notation "simplify_as_R2" ssrpatternarg(pat) := 
  let p := fresh in 
  let p1 := fresh in 
  let p2 := fresh in 
  let eq_p := fresh in
  let eq_p1 := fresh in
  let eq_p2 := fresh in
  ssrpattern pat;
  intro p;
  pose proof (refl_equal p) as eq_p;
  unfold p at 1 in eq_p;
  rewrite /Cdiv /Cinv /Cmult /Cminus /Copp /Cplus /= in eq_p;
  destruct p as (p1,p2);
  apply pair_equal_spec in eq_p;
  destruct eq_p as [eq_p1 eq_p2];
  field_simplify in eq_p1;
  field_simplify in eq_p2;
  rewrite -{}eq_p1 -{}eq_p2 {p1 p2}.

Section Extentionality.

Lemma global_local {A: UniformSpace} (P: A -> Prop):
  (forall x, P x) -> (forall x, locally x P).
Proof.
rewrite /locally.
move => glob x.
exists pos_half.
move => y _  //=.
Qed.

Lemma filterdiff_ex_filterdiff: forall {K:AbsRing} {U V:NormedModule K} f F g,
   filterdiff f F g -> ex_filterdiff (K:=K) (V:=V) (U:=U) f F.
Proof.
move => K V f F g d.
eexists.
eauto.
Qed.

Lemma derive_ex_derive: forall {K:AbsRing} {V:NormedModule K} f x g,
   is_derive f x g -> ex_derive (K:=K) (V:=V) f x.
Proof.
move => K V f F g d.
eexists.
eauto.
Qed.

Lemma ext_filter: 
  forall {T} (F: (T-> Prop) -> Prop) {FF: Filter F} P Q,
    (forall x, P x <-> Q x) -> F P <-> F Q.
Proof.
  move=> ? F ? P Q ext.
  split; apply filter_imp; apply ext.
Qed.

Lemma flip_filter_eq {T V}:
  forall  (F: (T-> Prop) -> Prop) {FF: Filter F} (f g: T -> V),
    F (fun x => f x = g x) <-> F (fun x => g x = f x). 
Proof.
  move=> F FF f g ; split; move => fl.
  eapply (filter_imp (fun x => f x = g x)); first by congruence.
  auto.
  eapply (filter_imp (fun x => g x = f x)); first by congruence.
  congruence.
Qed.

Lemma ext_filterdiff_d {K : AbsRing} {U : NormedModule K} {V : NormedModule K}:
   forall l1 l2: U -> V, 
   (forall (x: U), l1 x = l2 x) ->   
   forall f F {FF: Filter F}, 
   filterdiff f F l1 <-> filterdiff f F l2.
Proof.
  move=> l1 l2 *.
  split; move => ?.
  - apply (filterdiff_ext_lin _ l1); auto.
  - apply (filterdiff_ext_lin _ l2); auto.
Qed.


Lemma ext_filterlim_loc:
  forall {T U F G} {FF : Filter F} (f g : T -> U),
  F (fun x => f x = g x) ->
  filterlim f F G <-> filterlim g F G.
Proof.
  move => ? ? F G ? f g ext; split;
  apply filterlim_ext_loc; auto.
  apply flip_filter_eq; auto.
Qed.

Lemma ext_filterdiff_loc {K : AbsRing} {U : NormedModule K} {V : NormedModule K}:
   forall {F} {FF: Filter F} (f1 f2 l: U -> V),
   (F (fun q => f1 q = f2 q)) ->   
   (forall x, is_filter_lim F x -> f1 x = f2 x) ->
   filterdiff f1 F l <-> filterdiff f2 F l.
Proof.
  move => F FF f1 f2 l ext.
  split; move => ?.
  - eapply (filterdiff_ext_loc _ f2); auto. 
    auto.
  - eapply (filterdiff_ext_loc f2 _); auto.
    apply flip_filter_eq; auto.
    symmetry.
    auto.
Qed.

Lemma ext_filterdiff_glo {K : AbsRing} {U : NormedModule K} {V : NormedModule K}:
   forall {F} {FF: Filter F} (f1 f2 l: U -> V),
   (forall x, f1 x = f2 x) ->
   filterdiff f1 F l <-> filterdiff f2 F l.
Proof.
  move => F FF f1 f2 l ext.
  apply ext_filterdiff_loc; last by auto.
  under ext_filter => x do by rewrite ext over.
  apply flip_filter_eq; auto.
  apply filter_forall; auto.
Qed.

Lemma ext_is_derive_loc {K : AbsRing} {V : NormedModule K}:
   forall (f1 f2: K -> V) x l,
   (locally x (fun y => f1 y = f2 y)) ->
   is_derive f1 x l <-> is_derive f2 x l.
Proof.
  move => f1 f2 x l ext; split; move => drv //=; simpl in *.
  - apply (is_derive_ext_loc f1 _); auto.
  - apply (is_derive_ext_loc f2 ); auto.
    apply (filter_imp (fun y => f1 y = f2 y)); congruence.
Qed.

Lemma ext_is_derive_glo {K : AbsRing} {V : NormedModule K}:
   forall (f1 f2: K -> V) x l,
   (forall y,  f1 y = f2 y) ->
   is_derive f1 x l <-> is_derive f2 x l.
Proof.
  move => f1 f2 x l ext. 
  apply ext_is_derive_loc.
  apply global_local; auto.
Qed.

End Extentionality. 

(** A notation for forward reasoning, like 
    a chain of equalities*)
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

(** Lots of unfolding of definitions like ball or norm*)

Section CArith.
  
Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.

Lemma Rlt_0_neq_0: forall a,
  0 < a -> a <> 0.
Proof.
  move => *; lra.
Qed.

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

Lemma scal_one_r {K:Ring}: forall z: K ,
  scal z one = z.
Proof.
rewrite /scal //=.
apply mult_one_r.
Qed.
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
  1: apply Rplus_le_le_0_compat; apply pow2_ge_0.
  1: lra.
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

Lemma Cmod_Rabs_imaginary: forall (x y:R), 
  Rabs y <= Cmod (x,y).
Proof.
  move => x y.
  apply: Rle_trans; last by apply Rmax_Cmod.
  simpl.
  apply Rmax_r.
Qed.
Lemma Cmod_Rabs_real: forall (x y:R), 
  Rabs x <= Cmod (x,y).
Proof.
  move => x y.
  apply: Rle_trans; last by apply Rmax_Cmod.
  simpl.
  apply Rmax_l.
Qed.


Lemma Cmod_Rabs_plus: forall (x y:R), 
  Cmod (x,y) <= Rabs x + Rabs y.
Proof.
  move => x y.
  rewrite /Cmod /=.
  rewrite ? (sqrt_le_left) /=; field_simplify.
  - rewrite 2!pow2_abs. 
    apply Rplus_le_compat_r.
    rewrite -[x in x <= _]Rplus_0_r.
    apply Rplus_le_compat_l.
    apply Rmult_le_pos; last apply Rabs_pos.
    apply Rmult_le_pos; last apply Rabs_pos.
    lra.
  - nra.
  - apply Rplus_le_le_0_compat; apply Rabs_pos.
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
End CArith.

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

Ltac unfold_ball := rewrite 
  /ball /= /prod_ball /= /fct_ball /=
  /AbsRing_ball /=.
Ltac unfold_alg := rewrite 
  /norm /= /scal/= /mult /= /abs /= /minus /= /plus 
  /= /prod_plus /prod_opp /opp /= -/(Cminus _ _) -?/(Rminus _ _).

Lemma is_filter_lim_locally: forall {T:UniformSpace} (z:T),
  is_filter_lim (locally z) z.
Proof.
  move => T z. rewrite //=.
Qed.


(** There are several ways to view the standard topology on C. 
    They are all equivalent.*)
Section CTopologies.

Definition ball_sqr := @ball (C_UniformSpace).
Definition locally_sqr := @locally C_UniformSpace.

Definition ball_circ := @ball (AbsRing_UniformSpace C_AbsRing).
Definition locally_circ := @locally (AbsRing_UniformSpace C_AbsRing).

Lemma ex_RInt_prod: forall f a b,
  @ex_RInt C_R_CompleteNormedModule f a b <->
  @ex_RInt (prod_NormedModule R_AbsRing R_NormedModule R_NormedModule) f a b.
Proof.
  move => f a b; split; move=> [l ?]; exists l; apply: filterlim_filter_le_2. 
  1,3:(by (instantiate (1:= @locally _ l) => P)).
  all: auto.
Qed.

Lemma cts_topology_2 {U: UniformSpace}: forall (f: U -> C) u, 
  @continuous U (C_UniformSpace) f u <-> 
  @continuous U (AbsRing_UniformSpace C_AbsRing) f u.
Proof.
  move => f u; split => H;
  (apply: filterlim_filter_le_2;
  [ move => P; apply locally_C
  | auto
  ]).
Qed.

Lemma cts_topology_1 {U: UniformSpace}: forall (f: C -> U) u, 
  @continuous (C_UniformSpace) U f u <-> 
  @continuous (AbsRing_UniformSpace C_AbsRing) U f u.
Proof.
  move => f u; split => H;
  (apply: filterlim_filter_le_2;
  [ auto
  | move => P H'; apply/locally_C
  ]); eauto.
Qed.

Lemma diff_topology_change: forall f f' z, 
 
 @is_derive C_AbsRing (C_NormedModule) f z f' <-> 
 @is_derive C_AbsRing (AbsRing_NormedModule C_AbsRing) f z f'.
Proof.
  move => f f' z.
  rewrite /is_derive /filterdiff.
  split;
  move => [_ Hf]; (split; first by apply is_linear_scal_l);
  move => + /is_filter_lim_locally_unique <- eps => _;
  move: Hf => /(_ z);
  [ move => /(_ (@is_filter_lim_locally (AbsRing_UniformSpace C_AbsRing) z ))
  | move => /(_ (@is_filter_lim_locally (AbsRing_UniformSpace C_AbsRing) z ))
  ];
  move => /(_ eps); auto.
Qed.


End CTopologies.

Ltac replace_Derive :=
  let df' := fresh in 
  let df := fresh in 
  evar (df' : R);
  set df := Derive _ _;
  have {df df'}->: (df = ?df') by
    rewrite /df;
    apply: is_derive_unique;
    auto_derive; auto.

Create HintDb teardown_leaf.
Tactic Notation "teardown" 
  tactic(topology_shift) 
  tactic(t_plus) 
  tactic(t_scal) 
  tactic(t_mult) 
  tactic(t_minus) 
  tactic(t_opp) 
  tactic(t_div) 
  tactic(t_pair) :=
  try auto with auto_continuous;
  match goal with 
  
  | |- context[fun _ => (_ , _)] => first [t_pair | topology_shift; t_pair]
  
  | |- context[fun _ => plus _ _] => t_plus
  | |- context[fun _ => Rplus _ _] => t_plus
  | |- context[fun _ => Cplus _ _] => t_plus
  | |- context[plus _] => t_plus
  | |- context[Rplus _] => t_plus
  | |- context[Cplus _] => t_plus
  
  | |- context[fun _ => Cmult _ _] => first [t_mult | topology_shift; t_mult]
  
  | |- context[fun _ => scal _ _] => t_scal
  | |- context[fun _ => mult _ _] => t_mult
  | |- context[fun _ => Rmult _ _] => t_mult
  | |- context[fun _ => Cmult _ _] => t_mult
  | |- context[scal _] => t_scal
  | |- context[mult _] => t_mult
  | |- context[Rmult _] => t_mult
  | |- context[Cmult _] => t_mult
   
  | |- context[fun _ => minus _ _] => t_minus
  | |- context[fun _ => Rminus _ _] => t_minus
  | |- context[fun _ => Cminus _ _] => t_minus
  | |- context[minus _] => t_minus
  | |- context[Rminus _] => t_minus
  | |- context[Cminus _] => t_minus

  | |- context[fun _ => opp _] => t_opp
  | |- context[fun _ => Ropp _] => t_opp
  | |- context[fun _ => Copp _] => t_opp
  | |- context[opp _] => t_opp
  | |- context[Ropp _] => t_opp
  | |- context[Copp _] => t_opp

  | |- context[fun _ => Rinv _] => t_div
  | |- context[fun _ => Cinv _] => t_div
end.

Section AutoDiff.

Lemma is_derive_continuous: forall 
  {K: AbsRing} {V : NormedModule K} f f' x,
  is_derive (K:=K) (V:=V) f x f' -> continuous f x.
Proof.
 move => *.
 apply ex_derive_continuous; eexists;  eauto.
Qed.

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

Lemma is_derive_pair_aux {K : AbsRing} {M : NormedModule K} :
  forall (f g: K -> M) f' g' (x: K), 
  is_derive f x f' ->
  is_derive g x g' ->
  is_derive (fun q => (f q, g q)) x (f', g').
Proof.
  pose h (p q:M) := (p,q).
  move => *.
  apply: (filterdiff_comp_2 _ _ h).
  - simpl. auto.
  - simpl. auto.
  - under (ext_filterdiff_d) => x do rewrite -surjective_pairing.
    under ext_filterdiff_glo => x do rewrite /h -surjective_pairing.
    apply filterdiff_id.
Qed.

Lemma is_derive_pair {K : AbsRing} {M : NormedModule K} :
  forall (f g : K -> M) f' g' (x: K), 
  (is_derive f x (f') /\
  is_derive g x (g')) <->
  is_derive (fun q => (f q, g q)) x (f', g').
Proof.
  move => f g f' g' x. 
  split;
  first by move => [ ? ?]; apply: is_derive_pair_aux; auto.
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

End AutoDiff.

Ltac auto_derive_teardown :=
  rewrite /Rdiv /Cdiv;
  repeat (teardown 
          (apply/diff_topology_change) 
          (apply: ex_derive_plus) 
          (apply: ex_derive_scal) 
          (apply: ex_derive_mult)
          (apply: ex_derive_minus)
          (apply: ex_derive_opp)
          (apply: ex_derive_inv)
          (apply: derive_ex_derive; apply/is_derive_pair));
  auto with teardown_leaf.

Hint Extern 4 (ex_derive id _) => (by apply: ex_derive_id) : teardown_leaf.
Hint Extern 4 (ex_derive (fun => _) _) => (by apply: ex_derive_const) : teardown_leaf.



Section AutoContinuous.
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

Lemma continuous_Rinv: forall x, 
  x <> 0 -> continuous Rinv x.
Proof.
  move => x neq.
  apply: ex_derive_continuous.
  auto_derive.
  auto.
Qed.
End AutoContinuous. 


Ltac auto_cts := 
  rewrite /Rdiv /Cdiv; 
  repeat (teardown
          (apply/cts_topology_2) 
          (apply: continuous_plus) 
          (apply: continuous_scal) 
          (apply: continuous_mult)
          (apply: continuous_minus)
          (apply: continuous_opp)
          (apply: continuous_comp)
          (apply: continuous_pair));
 auto with teardown_leaf.
Open Scope C.

Hint Extern 5 (continuous _ _ ) => 
  (apply: ex_derive_continuous; eexists; eauto) : teardown_leaf.

Hint Extern 1 (continuous fst _) => (apply: continuous_fst) : teardown_leaf.
Hint Extern 1 (continuous snd _) => (apply: continuous_snd) : teardown_leaf.
Hint Extern 1 (continuous id _) => (apply: continuous_id) : teardown_leaf.
Hint Extern 1 (continuous (fun =>_) _) => (apply: continuous_const) : teardown_leaf.

Hint Extern 5 (continuous _ _) => (apply/cts_topology_2) : teardown_leaf. 
Hint Extern 5 (continuous _ _) => (apply/cts_topology_1) : teardown_leaf. 


Lemma RleP : forall x y,
  reflect (x <= y) (Rle_dec x y).
Proof.
  move => x y.
  apply/iff_reflect.
  case(Rle_dec x y) => H; split => H'; auto.
  discriminate.
Qed.

Ltac destruct_match := 
  match goal with 
  | |- context[match ?x with _ => _ end]  => 
    let p := fresh in
    let l := fresh in
    set p := x;
    destruct p 
  end.

Ltac copy := 
  let h := fresh in 
  let j := fresh in
   move => h; pose proof h as j; move: h j.


(** a bunch of facts I need about 2d differentiation that are missing from
coquelicot*)
Section Diff_2d.
Open Scope R.

(** A stupid issue with the existing proof in Coquelicot.
they prove Derives = _, but that's not strong enough.
So I copy pasted the entire proof, minus one rewrite at the beginning*)
Lemma differentiable_pt_lim_is_derive (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> is_derive (fun x => f x y) x lx /\ is_derive (fun y => f x y) y ly.
Proof.
  move => Df ; split ; apply is_derive_Reals => e He ;
  case: (Df (pos_div_2 (mkposreal e He))) => {Df} delta /= Df ;
  exists delta => h Hh0 Hh.


  replace ((f (x + h) y - f x y) / h - lx)
    with ((f (x+h) y - f x y - (lx * ((x+h) - x) + ly * (y - y))) / h)
    by (by field).
  rewrite Rabs_div.
  apply Rlt_div_l.
  by apply Rabs_pos_lt.
  apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x + h - x)) (Rabs (y - y))).
  apply (Df (x+h) y).
  by (ring_simplify (x + h - x)).
  rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
  ring_simplify (x + h - x).
  rewrite Rmax_left.
  apply Rmult_lt_compat_r.
  by apply Rabs_pos_lt.
  lra.
  rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
  by [].

  replace ((f x (y + h) - f x y) / h - ly)
    with ((f x (y + h) - f x y - (lx * (x - x) + ly * ((y + h) - y))) / h)
    by (by field).
  rewrite Rabs_div.
  apply Rlt_div_l.
  by apply Rabs_pos_lt.
  apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x - x)) (Rabs (y + h - y))).
  apply (Df x (y + h)).
  rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
  by (ring_simplify (y + h - y)).
  ring_simplify (y + h - y).
  rewrite Rmax_right.
  apply Rmult_lt_compat_r.
  by apply Rabs_pos_lt.
  lra.
  rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
  by [].
Qed.

Lemma differentiable_pt_lim_left (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> ex_derive (fun x => f x y) x.
Proof.
  move => df.
  have [??] := (differentiable_pt_lim_is_derive df).
  exists lx; auto.
Qed.

Lemma differentiable_pt_lim_right (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> ex_derive (fun y => f x y) y.
Proof.
  move => df.
  have [??] := (differentiable_pt_lim_is_derive df).
  exists ly; auto.
Qed.

Lemma differentiable_pt_unique (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  differentiable_pt_lim f x y  
    (Derive (fun x => f x y) x) 
    (Derive (fun y => f x y) y).
Proof. 
  move => [l1 [l2]].
  copy.
  by move => /differentiable_pt_lim_unique [-> ->].
Qed.

Lemma differentiable_pt_ex_derive (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  ex_derive [eta f x] y /\
  ex_derive (f ^~ y) x. 
Proof. 
  move => [l1 [l2]] /differentiable_pt_lim_is_derive [H1 H2].
  split; [exists l2 | exists l1]; auto.
Qed.
Lemma differentiable_pt_ex_left (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  ex_derive (f ^~ y) x. 
Proof. apply differentiable_pt_ex_derive. Qed.

Lemma differentiable_pt_ex_right (f : R -> R -> R) (x y : R) :
  differentiable_pt f x y -> 
  ex_derive [eta f x] y.
Proof. apply differentiable_pt_ex_derive. Qed.

Lemma continuity_2d_pt_comp: 
  forall f g h x y,
  continuity_2d_pt f (g x y) (h x y) -> 
  continuity_2d_pt g x y -> 
  continuity_2d_pt h x y -> 
  continuity_2d_pt (fun x' y' => f (g x' y') (h x' y')) x y.
Proof.
  move => f g h x y 
    /continuity_2d_pt_filterlim Cf
    /continuity_2d_pt_filterlim Cg 
    /continuity_2d_pt_filterlim Ch. 
  apply/ continuity_2d_pt_filterlim. 
  apply: filterlim_comp_2; eauto.
  apply: filterlim_filter_le_1 Cf.
  move => P [del +].
  rewrite /ball //= /prod_ball //= => H.
  eapply Filter_prod. 
  - exists del => x0; instantiate(1 := ball (g x y) del); auto. 
  - exists del => y0; instantiate(1 := ball (h x y) del); auto.
  - move => x0 y0 b1 b2. apply H; simpl; tauto.
Qed.

Lemma continuity_2d_pt_continuous: 
  forall f x y,
  continuity_2d_pt f x y <-> 
  continuous (fun z => f z.1 z.2) (x,y).
Proof.
  move => f x y.
  rewrite continuity_2d_pt_filterlim /continuous //=.
Qed.

Lemma continuity_2d_pt_continuous_right: 
  forall f x y,
  continuity_2d_pt f x y -> 
  continuous (fun z => f x z) y.
Proof.
  move => f x y.
  rewrite continuity_2d_pt_continuous //=. 
  move => /(continuous_comp (fun z => (x, z.2))).
  move => /(_ ltac:(auto_cts)) //= => + P lP.
  move => /(_ P lP) [eps H].
  exists eps => y' xball. 
  apply: (H (x,y')).
  split; auto. 
  apply ball_center.
Qed.

Section DifferentiablePtComp.
  Variables (f g h : R -> R -> R).
  Variables (x y : R).
  Hypothesis (df: differentiable_pt f (g x y) (h x y)).
  Hypothesis (dg: differentiable_pt g x y ).
  Hypothesis (dh: differentiable_pt h x y ).
  Lemma differentiable_pt_comp   :
    differentiable_pt (fun x' y'  => f (g x' y') (h x' y')) x y .
  Proof.
    move: df dg dh=> [? [? ?]] [? [? ?]] [? [? ?]]. 
    eexists; eexists.
    apply differentiable_pt_lim_comp; eauto.
  Qed.
  
  Lemma differentiable_pt_comp_ex_derive  :
    ex_derive (fun x' => f (g x' y) (h x' y)) x /\
    ex_derive (fun y' => f (g x y') (h x y')) y 
  .
  Proof.
    have := differentiable_pt_comp.
    move => /differentiable_pt_ex_derive; tauto.
  Qed.
  
  Lemma differentiable_pt_comp_ex_derive_right:
    ex_derive (fun y' => f (g x y') (h x y')) y .
  Proof. apply differentiable_pt_comp_ex_derive. Qed.
  Lemma differentiable_pt_comp_ex_derive_left:
    ex_derive (fun x' => f (g x' y) (h x' y)) x.
  Proof.
    apply differentiable_pt_comp_ex_derive.
  Qed.

  Lemma Derive_comp_2_left: 
    Derive (fun z => f (g z y) (h z y)) x = 
    Derive (f ^~ (h x y)) (g x y) * Derive (g ^~ y) x + 
    Derive [eta (f (g x y))] (h x y) * Derive (h ^~ y) x.
  Proof.
    move: df => /differentiable_pt_unique => Df.
    move: dg => /differentiable_pt_unique => Dg.
    move: dh => /differentiable_pt_unique => Dh.
    have := (differentiable_pt_lim_comp f g h x y _ _ _ _ _ _ Df Dg Dh). 
    move=>  /differentiable_pt_lim_unique; tauto.
  Qed.
  Lemma Derive_comp_2_right: 
    Derive (fun z => f (g x z) (h x z)) y = 
    Derive (f ^~ (h x y)) (g x y) * Derive (g x) y + 
    Derive [eta (f (g x y))] (h x y) * Derive (h x) y.
  Proof.
    move: df => /differentiable_pt_unique => Df.
    move: dg => /differentiable_pt_unique => Dg.
    move: dh => /differentiable_pt_unique => Dh.
    have := (differentiable_pt_lim_comp f g h x y _ _ _ _ _ _ Df Dg Dh). 
    move=>  /differentiable_pt_lim_unique; tauto.
  Qed.

End DifferentiablePtComp.

Lemma differentiable_pt_scal: forall f x y,
  ex_derive f y -> 
  differentiable_pt (fun p q => p * f q) x y.
Proof.
  move => f x y Ex.
  eexists; eexists.
  apply/filterdiff_differentiable_pt_lim. 
  apply: (@is_derive_filterdiff (fun p q => p * f q)). 
  - apply global_local => x'; auto_derive; eauto; field_simplify;
      instantiate (1:= fun _ q => f q); auto.
  - auto_derive; auto. 
  - auto_cts. 
    apply: continuous_comp.
    simpl.
    1: auto with teardown_leaf.
    apply: ex_derive_continuous.
    auto.
Qed.

Lemma differentiable_pt_proj2: forall f x y,
  ex_derive f y -> 
  differentiable_pt (fun p q => f q) x y.
Proof.
  move => f x y Ex.
  eexists; eexists.
  apply/filterdiff_differentiable_pt_lim. 
  apply: (@is_derive_filterdiff (fun p q =>  f q)). 
  - apply global_local => x'; auto_derive; eauto.
      instantiate (1:= fun _ _ => 0); auto.
  - auto_derive; auto. 
  - apply continuous_const. 
Qed.
Lemma differentiable_pt_proj1: forall f x y,
  ex_derive f x -> 
  differentiable_pt (fun p q => f p) x y.
Proof.
  move => f x y [??].
  eexists; eexists.
  apply: differentiable_pt_lim_proj1_0 .
  apply/ is_derive_Reals.
  eauto.
Qed.

Lemma differentiable_pt_ext: forall f g x y,
  (forall p q, f p q = g p q) -> 
  differentiable_pt f x y <-> differentiable_pt g x y.
Proof.
  split; move => [? [? G]]; eexists; eexists; 
  eapply differentiable_pt_lim_ext.
  - exists pos_half => *. apply H.
  - eauto.
  - exists pos_half => *. symmetry. apply H.
  - eauto.
Qed.

Lemma differentiable_pt_ext_loc: forall f g x y,
  locally_2d (fun p q => f p q = g p q) x y -> 
  differentiable_pt f x y <-> differentiable_pt g x y.
Proof.
  move => f g x y /locally_2d_locally loc_eq.
  split; move => [? [? /filterdiff_differentiable_pt_lim G]]; eexists; eexists;
  apply/ filterdiff_differentiable_pt_lim;
  [ |
  have {}loc_eq: locally (x,y) (fun z => g z.1 z.2 = f z.1 z.2) by
      apply: filter_imp loc_eq;
      move => *; congruence
  ];
  apply: (filterdiff_ext_loc _ _ _ loc_eq).
  - apply locally_filter.
  - move => p /is_filter_lim_locally_unique <- //=.
    move: loc_eq => /locally_singleton //=.
  - eauto.
  - apply locally_filter.
  - move => p /is_filter_lim_locally_unique <- //=.
    move: loc_eq => /locally_singleton //=.
  - eauto.
Qed.

Lemma differentiable_pt_mult: forall x y,
  differentiable_pt Rmult x y .
Proof.
  move => x y.
  exists y; exists x.
  apply/ filterdiff_differentiable_pt_lim.
  apply: filterdiff_ext_lin.
  2: move => z; rewrite [x in _ + x]Rmult_comm; reflexivity.
  apply: filterdiff_mult_fct.
  1: unfold_alg; move => *; field_simplify; auto.
  1: split; first by apply is_linear_fst.
  2: split; first by apply is_linear_snd.

  all: move => p /is_filter_lim_locally_unique <- //= eps;
       exists pos_half => *;
       rewrite /minus plus_opp_r  norm_zero /zero /=;
       apply Rmult_le_pos; first (by left; apply cond_pos);
       apply norm_ge_0.
Qed.

Lemma differentiable_pt_minus: forall x y,
  differentiable_pt Rminus x y .
Proof.
  move => x y.
  exists 1; exists (-1).
  apply/ filterdiff_differentiable_pt_lim.
  apply: (@filterdiff_ext_lin _ _ _ _ _ _ ( fun z => z.1 - z.2)).
  2: move => *; field_simplify; auto.
  apply: filterdiff_minus.
Qed.
  
Lemma differentiable_pt_rplus : forall x y, differentiable_pt Rplus x y .
Proof.
  move => x y.
  exists 1; exists 1.
  apply/ filterdiff_differentiable_pt_lim.
  apply: filterdiff_ext_lin.
  2: move => z; rewrite ?Rmult_1_r; reflexivity.
  apply: filterdiff_plus.
Qed.
End Diff_2d.

Ltac auto_differentiable_pt := 
  rewrite /Rdiv; 
  repeat (teardown
          (fail "no topology changes here") 
          (apply: differentiable_pt_comp; 
             first (by apply: differentiable_pt_rplus)) 

          (unfold_alg; apply: differentiable_pt_comp; 
             first (by apply: differentiable_pt_mult)) 

          (apply: differentiable_pt_comp; 
             first (by apply: differentiable_pt_mult)) 

          (apply: differentiable_pt_comp; 
             first (by apply: differentiable_pt_minus)) 
          (fail "not sure about 1d composition")
          (fail "not sure about 1d composition")
          (fail "doesn't make sense for differentiable_pt"));
  try apply: differentiable_pt_proj2;
  try apply: differentiable_pt_proj1;
  auto with teardown_leaf.

