Require Import Reals Psatz Lra RelationClasses.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex 
  RInt RInt_analysis Derive_2d.
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Require Import domains cauchy_riemann path_independence.

Open Scope program_scope.
Open Scope general_if_scope.
Require Import domains ext_rewrite real_helpers.

Section CauchyIntegral.
Open Scope C.
Definition c_circle (r: R) (t:R):C := r * (cos t, sin t).
Definition c_circle' (r: R) (t:R):C := r * (-sin t, cos t)%R.

Lemma c_circle_deriv: forall r x, is_derive (c_circle r) x ((c_circle' r) x).
Proof.
  rewrite /c_circle /c_circle'.
  move => r x.
  under ext_is_derive_glo => y.
    set p := _ * _.
    simplify_as_R2 e p.
  over.
  set p := _ * _.
  simplify_as_R2  e p.
  apply (is_derive_pair 
    (f := fun q => r * cos q) 
    (g := fun q => r * sin q)
    (f' := fun q => -r * sin q)
    (g' := fun q => r * cos q)
  )%R; auto_derive_all. 
Qed.

Open Scope R.
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
  - apply continuous_comp; simpl; try auto_continuous_aux.
    apply: ex_derive_continuous.
    auto_derive; auto.
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
    


Lemma smooth_circ: forall r t, 
  SmoothPath (fun r t => r * cos t)%R ( fun r t => r * sin t)%R r t.
Proof.

  Ltac rerwite_under f := 
    let l := fresh in 
    under differentiable_pt_ext => p q do (
      set l := Derive _ _;
      replace l with f
    )
    ;
    rewrite /l; symmetry;
    apply: is_derive_unique;
    auto_derive; auto; field_simplify; auto;
    apply: differentiable_pt_scal;
    auto_derive; auto.
  Ltac replace_Derive := 
    eapply continuity_2d_pt_ext;[ move => x y;
      eapply Derive_ext => z;
        symmetry;
        apply is_derive_unique;
        auto_derive; auto;
        field_simplify; auto | ];
    eapply continuity_2d_pt_ext;[ move => x y;
        symmetry;
        apply is_derive_unique;
        auto_derive; auto;
        field_simplify; auto | ].
  move => r t; repeat split; [exists pos_half | exists pos_half | .. ]; repeat split.
  7-10: 
    replace_Derive;
    auto;
    apply: differentiable_continuity_pt;
    apply differentiable_pt_proj2; auto_derive; auto.
  - apply differentiable_pt_scal; auto_derive; auto.
  - apply (@differentiable_pt_ext _ (fun p q => (p * (- sin q))));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_scal; auto_derive; auto
    ].
  - apply (@differentiable_pt_ext _ (fun p q => cos q));
    [ move => *; apply: is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_proj2; auto_derive; auto
    ].
    
  - apply differentiable_pt_scal; auto_derive; auto.
  - apply (@differentiable_pt_ext _ (fun p q => (p * (cos q))));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_scal; auto_derive; auto
    ].
  - apply (@differentiable_pt_ext _ (fun p q => sin q));
    [ move => *; apply:is_derive_unique; auto_derive; auto; field_simplify; auto
    | apply: differentiable_pt_proj2; auto_derive; auto
    ].
Qed.

Open Scope C.
Definition CHolo f f' z := 
  Holo f f' z /\ continuous f' z.
Lemma circ_independence : forall (f: C -> C) f' z (r r' r'': posreal),
  (forall z', ball z r z' -> CHolo f f' z') -> 
  r' < r ->
  r'' < r ->
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f (c_circle r' t0) * c_circle' r' t0) 0 (2 * PI) =
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t0 => f(c_circle r'' t0) * c_circle' r'' t0) 0 (2 * PI).
Proof.
  move => f f' z r r' r'' holo H1 H2.
  apply path_independence_part_4.

  


  
Record Contour := mkContour {
  gamma: R -> C; 
  l: R;
  r: R;
  l_to_r: l < r;
  diff: forall t, l < t < r -> ex_derive gamma t;
}.
Open Scope C. 
Definition CInt {g: Contour } f := 
  RInt (V:=C_R_CompleteNormedModule) 
    (fun t => f (gamma g t) * (gamma' g t)) (l g) (r g) .
Definition is_CInt (g: Contour) (f: C -> C) (z:C) :=
  is_RInt (fun t => f (gamma g t) * (gamma' g t)) (l g) (r g) z.

    eexists; eexists.
    apply/filterdiff_differentiable_pt_lim. 
    apply: (@is_derive_filterdiff 
      (fun p q => Derive (fun t0 => p * cos t0) q)).
    + apply global_local => x'.
      
    
    


Lemma rmult_scal : forall (r:R) (z:C),
  (RtoC r) * z = scal r z.
Proof.
  move => r [z1 z2]. unfold_alg; rewrite /prod_scal /Cmult.
  simpl.
  set p := LHS.
  simplify_as_R2 e p.
  set p := RHS.
  simplify_as_R2 e p.
Qed.
