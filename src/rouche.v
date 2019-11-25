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

Require Import domains.

Open Scope program_scope.
Open Scope general_if_scope.
Require Import domains ext_rewrite real_helpers.

Definition c_circle (t:R):C := (cos t, sin t).
Definition c_circle' (t:R):C := (-sin t, cos t).

Lemma c_circle_deriv: forall x, is_derive c_circle x (c_circle' x).
Proof.
  rewrite /c_circle /c_circle'.
  move => x.
  apply (is_derive_pair (f' := fun q => -_ _)); auto_derive_all. 
Qed.
Hint Resolve c_circle_deriv : derive_compute.

Lemma scal_one_r {K:Ring}: forall z: K ,
  scal z one = z.
Proof.
rewrite /scal //=.
apply mult_one_r.
Qed.
SearchAbout (0 <= Rabs _).
Ltac nrapp := 
  match goal with 
  | |- context [Rabs ?y] => pose proof (Rabs_pos y)
  end.
Open Scope C.

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
  ? /norm //= -?Cmod_prod_norm //= 
  ? /minus //= ? /plus //= ? /opp //= ? /scal //=
  ? /mult //= ? /abs //= ?/prod_ball //= ? /ball //= 
.

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

Section Holo.
  Definition CR_eqs (u v udx udy vdx vdy: C -> R)  z := 
      is_derive (fun t => u (t,z.2)) z.1 (udx z) /\
      is_derive (fun t => u (z.1,t)) z.2 (udy z) /\
      is_derive (fun t => v (t,z.2)) z.1 (vdx z) /\
      is_derive (fun t => v (z.1,t)) z.2 (vdy z)
      .

  Definition CauchyRieman (u v udx udy vdx vdy: C -> R) z:=
    udx z = vdy z /\ 
    udy z = (- vdx z)%R
    .
  
  Definition Holo (f g: C -> C) z := 
    is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z (g z).

  Ltac auto_continuous_aux :=
    try apply continuous_id;
    try apply continuous_const;
    try eapply continous_pair; 
    try apply continuous_fst; 
    try apply continuous_snd.
  Ltac auto_continuous x z := 
    have: continuous x z;
    rewrite /x;
    repeat auto_continuous_aux.

  Lemma local_c_reals:
    forall (z:C) P,
      (within (fun q => q.2 = z.2) (locally (T:=C_UniformSpace) z)) P ->
      (locally (T:= R_UniformSpace) z.1 (fun q => (P (q,z.2)))).
  Proof.
    move => z P lz //=.
    case lz => eps clim.
    exists eps => y byz.
    apply clim; last by simpl; auto.
    unfold_alg.
    auto using AbsRing_ball_center.
  Qed.

  Lemma local_c_imags:
    forall (z:C) P,
        (within (fun q => q.1 = z.1) (locally (T:=C_UniformSpace) z)) P ->
        (locally (T:= R_UniformSpace) z.2 (fun q => (P (z.1,q)))).
  Proof.
    move => z P.
    pose h (z:C) := (z.2,z.1) .
    auto_continuous h (z.2, z.1) => H {} /H ?.
    apply (local_c_reals (z:=(z.2, _)) (P:= fun q => _ (q.2, q.1))).
    auto.
  Qed.

  Hint View for move /is_filter_lim_locally_unique.

  Ltac prove_within_C_axis cn rn h z := 
    let H := fresh  in
    let H' := fresh  in
    rewrite /within; 
    apply: (filter_imp (fun q => cn (h q)));
    [ case => q1 q2; simpl => + H;
      rewrite {}H /cn /rn /h //=;
      case eq: z;
      (have H : 
        (forall a b c d, a = b -> c = d -> a <= c -> b <= d) 
        by congruence);
      apply H;
      (unfold_alg;
      by elim_norms)
    | auto_continuous h z => H';
      apply: H'; 
      rewrite -surjective_pairing prod_c_topolog_eq
    ].
  Tactic Notation "rewrite" "->" := let h := fresh in move => h; rewrite {}h.
  Tactic Notation "rewrite" "<-" := let h := fresh in move => h; rewrite -{}h.
  Hint Rewrite prod_c_topolog_eq.
  Lemma c_diff_imaginary_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (z.1, q)) z.2 ((-v.2,v.1)%R).
  Proof.
    rewrite /is_derive /filterdiff => f z v.
    case => _ //=; split;
    first by apply (is_linear_scal_l (K:=R_AbsRing) ((-v.2,v.1)%R)).
    move => o /is_filter_lim_locally_unique.
    rewrite <-.
    rewrite /Equiv.is_domin //=  in b * => eps.
    pose r_normeq := 
      fun z' => norm (K:=R_AbsRing)
          (minus (minus (f (z'.1, z'.2)) (f (z.1, z.2))) 
                 (scal (minus z'.2 z.2) ((-v.2,v.1)%R))) <=
        eps * norm (minus z'.2 z.2) .
    under ext_filter => p do rewrite -/(r_normeq (z.1, p)).
    apply local_c_imags.
    set c_normeq := fun x: C =>
      norm  (minus (minus (f x) (f z)) (scal (minus x z) v)) <=
       eps * norm (minus x z) in b.

    pose h := fun q:C => (z.1,q.2).
    auto_continuous h z => hcts.
    prove_within_C_axis c_normeq r_normeq h z.
    apply (b z).
    rewrite //=.
  Qed.
  (** copy paste horror show!, but it's fine for now*)
  Lemma c_diff_real_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (q,z.2)) z.1 (v.1,v.2).
  Proof.
    rewrite /filterdiff => f z v.
    case => _ //=; split;
    first by apply (is_linear_scal_l (K:=R_AbsRing) (v.1,v.2)).
    move => o xlim .
    have eqn: (z.1 = o) by apply is_filter_lim_locally_unique; auto.
    subst.
    rewrite /Equiv.is_domin //= in b *.
    move => eps.
    pose r_normeq := 
      fun z' => norm (K:=R_AbsRing)
          (minus (minus (f (z'.1, z'.2)) (f (z.1, z.2))) 
                 (scal (minus z'.1 z.1) (v.1,v.2))) <=
        eps * norm (minus z'.1 z.1) .
    under ext_filter => p.
       rewrite -/(r_normeq (p, z.2)).
    over.
    apply local_c_reals.
    set c_normeq := fun x: C =>
      norm  (minus (minus (f x) (f z)) (scal (minus x z) v)) <=
       eps * norm (minus x z).

    pose h := fun q:C => (q.1,z.2).
    auto_continuous h z => hcts.
    prove_within_C_axis c_normeq r_normeq h z.
    apply (b z).
    rewrite //=.
  Qed.



  Lemma diff_split_coords: forall 
    {K: AbsRing}
    {V1 V2: NormedModule K} 
    (u: K -> V1)
    (v: K -> V2) x u' v', 
    is_derive (K:= K) (fun t => (u t, v t)) x (u', v') -> 
    is_derive (K:= K) u x u' /\
    is_derive (K:= K) v x v'
    .
  Proof.
    move => K V1 V2 u v x u' v' diff; split;
    [ apply (filterdiff_comp _ fst _ fst) in diff; simpl in *
    | apply (filterdiff_comp _ snd _ snd) in diff; simpl in *
    ];
    [auto | apply filterdiff_fst | auto | apply filterdiff_snd].
  Qed.

  Ltac copy := 
    let h := fresh in 
    let j := fresh in
     move => h; pose proof h as j; move: h j.
  Theorem CauchyRieman_Easy: forall u v udx udy vdx vdy g z,
    CR_eqs u v udx udy vdx vdy z -> 
    Holo (fun p => (u p, v p)) g z ->
    (CauchyRieman u v udx udy vdx vdy z /\ (g z).1 = (vdy z) /\ (g z).2 = vdx z)
    .
  Proof.
    move => u v udx udy vdx vdy g z .
    rewrite /Holo /CauchyRieman => cr_eqs .
    copy.
    case /c_diff_imaginary_axis /diff_split_coords .
    move /is_derive_unique => + /is_derive_unique => h1 h2.
    
    case /c_diff_real_axis /diff_split_coords .
    move /is_derive_unique => + /is_derive_unique => h3 h4.
    move: h1 h2 h3 h4.
    
    move: cr_eqs; rewrite /CR_eqs.
    do 3 (case; move /is_derive_unique; rewrite ->) .
    move /is_derive_unique; rewrite ->.
    move => *.
    repeat split; congruence.
  Qed.
End Holo.

