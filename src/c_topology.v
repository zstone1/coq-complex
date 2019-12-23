Require Import Reals Psatz Lra RelationClasses List.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex
  RInt RInt_analysis Derive_2d Compactness.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import domains ext_rewrite real_helpers.
Require Import domains cauchy_riemann path_independence cauchy_integral .

Lemma Cminus_eq_0: forall z, z - z = 0.
Proof. move => *. field_simplify_eq; auto. Qed.



Section UniformOn.

Context {U V:UniformSpace}.

Definition uniformly_on (E: U -> Prop) f (P: (U -> V) -> Prop) := 
  exists (del: posreal), forall g, 
    (forall x, E x -> (ball (f x) del (g x))) -> 
    P g.
Lemma uniformly_on_self: forall E f P, 
  uniformly_on E f P -> P f.
Proof.
  move => E f P [del H].
  apply H.
  move =>*. 
  apply: ball_center.
Qed.


Global Instance uniformly_on_filter: forall E f,
  ProperFilter (uniformly_on E f).
Proof.
  move => D f .
  constructor;[| constructor].
  - move => *.
    exists f.
    apply: uniformly_on_self.
    eauto.
  - move => *.
    exists pos_half.
    auto.
  - move => P Q [del1 H1] [del2 H2].
    exists (mkposreal _ (Rmin_stable_in_posreal del1 del2 )).
    move => g gbd.
    split.
    + apply: H1 => x Dx.
      apply: ball_le; last apply gbd; simpl; auto.
      apply: Rmin_l.
    + apply: H2 => x Dx.
      apply: ball_le; last apply gbd; simpl; auto.
      apply: Rmin_r.
  - move => P Q impl [del H].
    exists del => g gbd.
    apply: impl.
    apply H.
    auto.
Qed.

Lemma uniformly_on_subset : forall (E1 E2: U -> Prop) f ,
  (forall z, E1 z -> E2 z) ->
  filter_le (uniformly_on E2 f) (uniformly_on E1 f).
Proof.
  move => E1 E2 f sub P [del H].
  exists del => g gbd.
  apply: H.
  move => x E1x.
  apply gbd.
  apply sub.
  auto.
Qed.

Lemma uniformly_on_union : forall (E1 E2: U -> Prop) f P Q,
  uniformly_on E1 f P -> 
  uniformly_on E2 f Q -> 
  uniformly_on (fun q => E1 q \/ E2 q) f (fun g => P g /\ Q g).
Proof.
  move => E1 E2 f P Q [del1 UE1] [del2 UE2].

  exists (mkposreal _ (Rmin_stable_in_posreal del1 del2 )).
  move => g gbd.
  split.
  + apply UE1 => *.
    apply: ball_le; last apply gbd; simpl; auto.
    apply: Rmin_l.
  + apply UE2 => *.
    apply: ball_le; last apply gbd; simpl; auto.
    apply: Rmin_r.
Qed.

Definition uniformly_on_family 
  (Fam: ((U -> Prop) -> Prop)) f (P:(U -> V) -> Prop): Prop :=
  exists (l: list ({ (E, P):(_ * _) | 
            Fam E /\ (uniformly_on E f P) } )),
    forall g,
      List.Forall (fun z => (snd (proj1_sig z)) g ) l -> P g.

Instance uniformly_on_family_filter: forall (Fam: (U -> Prop) -> Prop) f,
  (exists E, Fam E) ->
  ProperFilter (uniformly_on_family Fam f).
Proof.
  move => Fam f [E0 FamE0].
  constructor;[|constructor].
  - move => P //= [l H] .
    exists f.
    apply H.
    apply/ Forall_forall.
    case => [[??][??]] *.
    apply: uniformly_on_self.
    eauto.
  - have H: Fam E0 /\ (uniformly_on E0 f (fun => True)) by
      split; [apply FamE0| apply filter_true ].
    exists [exist _ (E0,(fun => True)) H] .
    auto.
  - move => P Q [lP Hp] [lQ Hq].
    exists (lP ++ lQ).
    move => g /Forall_forall Hg.
    split.
    + apply Hp.
      apply/Forall_forall => x xIn.
      apply Hg.
      apply in_or_app.
      auto.
    + apply Hq.
      apply/Forall_forall => x xIn.
      apply Hg.
      apply in_or_app.
      auto.
  - move => P Q impl [l H].
    exists l.
    move => *.
    apply impl.
    auto.
Qed.


Lemma filterlim_on_family {T: UniformSpace}: 
  forall (Fam: (U -> Prop) -> Prop) (f_: T -> U -> V) flim F {FF: Filter F},
  (forall (E: U -> Prop), Fam E -> filterlim (f_) F (uniformly_on E flim)) -> 
  filterlim (f_) F (uniformly_on_family Fam flim) .  
Proof.
  move => Fam f_ flim F FF all.
  move => P [l+]. 
  move: l P.
  elim.
  - move => ? H. 
    apply: filter_imp; last by apply filter_true.
    move => *.
    apply H.
    apply Forall_nil.
  - move => a l IH P H.
    have {}H: forall g : U -> V,
          ((`a).2 g) /\ (List.Forall (fun z => (` z).2 g) l) ->
          P g by
       move => *; apply H; apply Forall_cons; tauto.
    apply (filter_imp _ P H).
    apply filter_and.
    + clear H. move: a => [[??][??]].
      apply: all; eauto.
    + apply IH; auto.
Qed.

Definition inner_ball (D: U -> Prop) x := exists y (del: posreal), 
  (forall z, ball y del z -> D z) /\ ball y (pos_div_2 del) x.

(** Technically this is only "compactly" when D is bounded. 
    But that's ok because I will assume that in practice*)
Definition compactly D (f: U -> V) := uniform_over_all (inner_ball D) D f.

Global Instance compactly_filter: forall D f,
  ProperFilter (compactly D f).
Proof.
  move => D f.
  apply: uniform_over_all_filter.
  - move => E1 E2 [??].
    SearchAbout (closed).
    apply: closed_or.
    
  move => D f.


      
    



    apply H.
    elim: cpt.
    + move => ? [eps [x [del [Dx +]]]].
      apply.
      move => *.
      apply: ball_center.
    + move => P0 Q R pand _ ? _ ?.
      apply pand; tauto.
  - constructor. 
    exists pos_half.
    exists z0.
    exists pos_half.
    split; first by auto.
    move => * //=.
  - move => P Q lP lQ.
    apply: Intersect. 
    + move => z. apply.
    + auto.
    + auto.

  - move => P + + H. 
    case: H.
    + move => [eps [u [del[Du H]]]] Q Qimpl. 
      constructor.
      exists eps, u, del. 
      split; first by auto.
      move => y yball.
      apply Qimpl.
      apply H.
      auto.
    + move => Q1 Q2 impl lQ1 lQ2 Q Qimpl.
      apply: Intersect.
      3: apply lQ2.
      2: apply lQ1.
      firstorder.
Qed.

Definition contour_inside (g:Contour) D:= 
  forall t, l_end g <= t <= r_end g -> D (gamma g t).
  
Definition OnPaths (D: C -> Prop) f (P: (C -> C) -> Prop) : Prop := 
  forall (gam:Contour), 
    contour_inside gam D ->
  (exists (del:posreal), forall g,
     (forall t, l_end gam <= t <= r_end gam -> 
     Cmod (g (gamma gam t) - f (gamma gam t)) < del) -> 
   P g
  ).

Lemma locally_uniform_le_uniform: forall D f,
  (exists z0, D z0) ->
  filter_le (locally f) (locally_uniform D f).
Proof.
  move => D f [z0 Dz0] ?. 
  elim. 
  + move => P [eps[x[del [Dx H']]]].
    exists eps => g gball.
    apply H'.
    move => z _.
    apply gball.
  + move => P Q1 Q2 impl unifQ1 lQ1 unifQ2 lQ2.
    have:=  @filter_and _ _ _ _ _ lQ1 lQ2.
    move => /(_ ltac:(apply locally_filter)) H.
    apply: filter_imp H; auto.
Qed.

End LocallyUniform.