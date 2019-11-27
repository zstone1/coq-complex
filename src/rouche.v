Require Import Reals Psatz Lra RelationClasses.
From Coquelicot Require Import Continuity 
  Rcomplements Derive Hierarchy AutoDerive Rbar Complex .
From Coq Require Import ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Require Import Program.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

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

Lemma is_filter_lim_locally: forall {T:UniformSpace} (z:T),
  is_filter_lim (locally z) z.
Proof.
  move => T z. rewrite //=.
Qed.
  

Section Holo.
  Definition CR_eqs (u v udx udy vdx vdy: C -> R)  z := 
    locally z ( fun q =>
      is_derive (fun t => u (t,q.2)) q.1 (udx q)) /\
    locally z ( fun q =>
      is_derive (fun t => u (q.1,t)) q.2 (udy q)) /\
    locally z ( fun q =>
      is_derive (fun t => v (t,q.2)) q.1 (vdx q)) /\
    locally z ( fun q =>
      is_derive (fun t => v (q.1,t)) q.2 (vdy q))
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

  Hint Rewrite prod_c_topology_eq.
  Lemma c_diff_imaginary_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (z.1, q)) z.2 ((-v.2,v.1)%R).
  Proof.
    rewrite /is_derive /filterdiff => f z v.
    case => _ //= /(_ z) b. split;
    first by apply (is_linear_scal_l (K:=R_AbsRing) ((-v.2,v.1)%R)).
    move => o /is_filter_lim_locally_unique <-.
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
    rewrite /within; 
    apply: (filter_imp (fun q => c_normeq (h q))).
    - case => q1 q2; simpl => + ->.
      rewrite /c_normeq /r_normeq /h //=.
      case eq: z.
      (have H : 
        (forall a b c d, a = b -> c = d -> a <= c -> b <= d) 
        by congruence).
      apply H;
      (unfold_alg;
      by elim_norms).
    - auto_continuous h z.
      apply. 
      rewrite -surjective_pairing prod_c_topology_eq.
      apply b.
      rewrite //=.
  Qed.

  Lemma diff_topology_equiv: forall f z v,
    is_derive (K:=C_AbsRing) (V:= AbsRing_NormedModule C_AbsRing) f z v <->
    is_derive (K:=C_AbsRing) (V:= C_NormedModule) f z v.
  Proof.
    move => f z v.
    rewrite /is_derive /filterdiff //= /Equiv.is_domin.
    do 2 split.
    1,3: apply is_linear_scal_l.
    all: destruct H; auto.
  Qed.

  Lemma Ci_sqr : Ci * Ci = -1.
  Proof.
    rewrite /Ci /Cmult //= /RtoC. f_equal; field_simplify; auto.
  Qed.

  Lemma is_derive_scal_C: forall z k,
    is_derive (K:=C_AbsRing) (fun q => scal k q) z k.
  Proof.
    move => z k. 
    rewrite /is_derive.
    under ext_filterdiff_glo => x.
      rewrite /scal //= /mult //= Cmult_comm.
    over.
    apply filterdiff_linear . 
    apply is_linear_scal_l.
  Qed.

  Lemma R_opp_1: forall x, (-(1) * x) = -x.
  Proof. move => x. field_simplify_eq. auto. Qed.

  Ltac simplify_R e p := 
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

  (** copy paste horror show!, but it's fine for now*)
  Lemma c_diff_real_axis: forall 
    (f: C -> C) (z:C) (v:C) ,
    is_derive (K:=C_AbsRing) f z v ->
    is_derive (fun q => f (q,z.2)) z.1 (v.1,v.2).
  Proof.
    move => f z v.
    pose h := fun z => scal Ci z.
    have {1}->: (z = -Ci * (Ci * z) ) by
      set p := (X in _ = X);
      simplify_as_R2 e p;
      rewrite -surjective_pairing.
    move /(is_derive_comp _ _) 
         /(_ (is_derive_scal_C _ _))
         /c_diff_imaginary_axis.
    rewrite //=. 
    under ext_is_derive_glo => x.
      set p := (X in f X).
      simplify_as_R2 e p.
    over.
    set p := (X in is_derive _ _ X).
    simplify_as_R2 e p.
    set p := (X in is_derive _ X).
    simplify_R e p.
    auto.
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
    do 3 (case; move /locally_singleton/is_derive_unique ->) .
    move /locally_singleton /is_derive_unique ->.
    move => *.
    repeat split; congruence.
  Qed.
  Notation "|| x ||" := (norm x) (at level 100).
  Infix "[+]" := plus (at level 199).
  Infix "[-]" := minus (at level 199).
  Infix "[.]" := scal (at level 100).

  SearchAbout ( sumbool (Rle _ _ ) _).
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

  Ltac combine_local H := 
  match goal with 
  | J: locally _ _ |- _ => pose proof (filter_and _ _ J H) as H
  end.
  Ltac ssrautoprop := try tauto; trivial.
  Theorem CauchyRieman_Hard: forall u v udx udy vdx vdy z,
    CR_eqs u v udx udy vdx vdy z -> 
    (CauchyRieman u v udx udy vdx vdy z) -> 
    locally z (continuous udx) ->  
    locally z (continuous udy) ->  
    locally z (continuous vdx) ->  
    locally z (continuous vdy) ->  
    Holo (fun p => (u p, v p)) (fun q => (vdy q, vdx q)) z 
  .
  Proof.
    move => u v udx udy vdx vdy z.
    case => loc.
    case => {loc} /(filter_and _ _ loc) => loc.
    case => {loc} /(filter_and _ _ loc) => loc.
    move => {loc} /(filter_and _ _ loc) => loc.
    move => CR.
    do 4 move => {loc} /(filter_and _ _ loc) => loc.
    rewrite ?and_assoc.
     
    rewrite /Holo /is_derive/ filterdiff.
    split; first by apply: is_linear_scal_l.
    
    rewrite /Equiv.is_domin => a.
    move => /is_filter_lim_locally_unique <- {a} eps.
    rewrite -prod_c_topology_eq.

    eexists ?[del] => a.
    rewrite /ball //= /prod_ball.
    rewrite /ball //= /AbsRing_ball. 
    unfold_alg => aballz.
    case: loc. 
    do 2 (rewrite /ball //= /AbsRing_ball; unfold_alg).
    move => eps_safe safe.

    have H: (?del <= eps_safe) by shelve.
    have {}: (ball z eps_safe a) by 
      do 2 (rewrite /ball //= /AbsRing_ball; unfold_alg);
      split;
      apply: (Rlt_le_trans _ ?del) ; tauto.
    (do 2 (rewrite /ball //= /AbsRing_ball; unfold_alg)) => {}H.
    have x_axis_mvt: 
      forall (f df :R -> R),
      let l0 := Rmin z.1 a.1 in
      let r0 := Rmax z.1 a.1 in
      (forall x, ball z eps_safe (x,z.2) -> is_derive f x (df x)) ->
      exists c:R, l0 <= c <= r0 /\ f a.1 - f z.1 = df(c)*(a.1-z.1).
    { move {safe} => f df l0 r0 diffin.
      have: (forall x, l0 <= x <= r0 -> is_derive f x (df x)).
      - simpl in *. move => x /Rabs_le_between_min_max bds.
        apply: (diffin x).
        do 2 (rewrite /ball //= /AbsRing_ball; unfold_alg).
        case: H => H1 H2.
        simpl in *; split.
        + rewrite /Rminus in bds. apply: (Rle_lt_trans _ _ _ bds); auto.
        + set p := (x in Rabs x). simplify_R e p.
          rewrite Rabs_R0; apply cond_pos.
      - move => diffall.
        rewrite /r0 /l0.
        apply (MVT_gen f a.1 z.1 df).
        have := .

      apply: (MVT_gen f). 
    
    
    have := (MVT_gen (fun q => u(q,z.2)) a.1 z.1 (fun q => udx (q,z.2))).
    - move => x /Rabs_lt_between_min_max bds.
      move: safe => /(_ (x,z.2)).
      case; last by tauto. 
      case: H.
      simpl; split.
      + by apply: (transitivity bds).
      + set p := (x in Rabs x). simplify_R e p.
        rewrite Rabs_R0; apply cond_pos.
    - move => x /Rabs_le_between_min_max bds.
      rewrite continuity_pt_filterlim -/(continuous _ _).
      apply: ex_derive_continuous.
      exists (udx (x,z.2)).
      move: safe => /(_ (x,z.2)).
      case; last by tauto. 
      case: H.
      simpl in *; split.
      + rewrite /Rminus in bds. apply: (Rle_lt_trans _ _ _ bds); auto.
      + set p := (x in Rabs x). simplify_R e p.
        rewrite Rabs_R0; apply cond_pos.

    - move => mvtdx.
      split; 
      SearchAbout (Rmin _ _)%R.
      apply.

      do 2 (rewrite /ball //= /AbsRing_ball; unfold_alg).
      have eps2bd: (Rabs (a.1+ -z.1) < eps2 /\ Rabs(a.2 + - z.2) < eps2)by
        case:aballz; 
        do 2 move => /(Rlt_le_trans) /(_ H) => ?.
      move /(_ eps2bd).
      
      
        SearchAbout (_< _ -> _ <= _ -> _ < _).
        split; transitivity .

      move => /(_ eps).

    pose proof (filter_and _ _ _ d_udx c_udx).

    rewrite /CR_eqs in CR_eqs.
    move: CR_eqs.
    Set Printing Implicit.


    `Begin eq U. { 
       rewrite /U.
      
     | {( (u(b,c) - u(x, c)) + (u(x, c) - u(x,y)) )} 
         field_simplify. 
     | {( udx _ * (b-x)      +  _  )} idtac. 
    all: `Done.
    }
      
    
    over.
End Holo.


