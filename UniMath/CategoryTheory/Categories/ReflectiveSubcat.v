Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.

(*
  if you use the equivalence between homsets property for adjunctions, then you need to have both functors. This can be annoying, because you need to show that taking exponentials is functorial. However, the beset way to get around it is to just use the unit/counit definition in the more commpact way. Specifically, one gves the counit (evaluation) and one shows that a suitable universal mapping property is satisfied.

  for exponentials concretely, the main work lies in giving the precise description of the evaluation and lambda abstraction. This requires one to go through the adjunctions. However, this can lead to complicated descriptions, so there is some calculational work
 *)

Proposition fully_faithful_reflects_monic
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            (HF : fully_faithful F)
            {x y : C₁}
            {f : x --> y}
            (Hf : isMonic (#F f))
  : isMonic f.
Proof.
  intros w g₁ g₂ p.
  use (invmaponpathsweq (weq_from_fully_faithful HF _ _)).
  use (Hf (F w) (#F g₁) (#F g₂)).
  rewrite <- !functor_comp.
  rewrite p.
  apply idpath.
Qed.


Definition reflective_subcat
           (C : category)
  : UU
  := ∑ (C' : category)
       (R : C' ⟶ C),
     fully_faithful R
     ×
     is_right_adjoint R.

Coercion reflective_subcat_to_cat
         {C : category}
         (C' : reflective_subcat C)
  : category
  := pr1 C'.

Coercion reflective_subcat_to_functor
         {C : category}
         (C' : reflective_subcat C)
  : C' ⟶ C
  := pr12 C'.

Definition fully_faithful_reflective
           {C : category}
           (C' : reflective_subcat C)
  : fully_faithful C'
  := pr122 C'.

Definition is_right_adjoint_reflective
           {C : category}
           (C' : reflective_subcat C)
  : is_right_adjoint C'
  := pr222 C'.

Definition reflective_subcat_left_adjoint
           {C : category}
           (C' : reflective_subcat C)
  : C ⟶ C'
  := left_adjoint (is_right_adjoint_reflective C').

Definition reflective_subcat_unit
           {C : category}
           (C' : reflective_subcat C)
  : functor_identity _ ⟹ reflective_subcat_left_adjoint C' ∙ C'
  := unit_from_right_adjoint (is_right_adjoint_reflective C').

Definition reflective_subcat_counit
           {C : category}
           (C' : reflective_subcat C)
  : C' ∙ reflective_subcat_left_adjoint C' ⟹ functor_identity _
  := counit_from_right_adjoint (is_right_adjoint_reflective C').

Proposition reflective_subcat_triangle_1
            {C : category}
            (C' : reflective_subcat C)
            (x : C)
  : #(reflective_subcat_left_adjoint C') (reflective_subcat_unit C' x)
    · reflective_subcat_counit C' _
    =
    identity _.
Proof.
  exact (pr122 (is_right_adjoint_reflective C') x).
Qed.

Proposition reflective_subcat_triangle_2
            {C : category}
            (C' : reflective_subcat C)
            (x : C')
  : reflective_subcat_unit C' _
    · #C' (reflective_subcat_counit C' x)
    =
    identity _.
Proof.
  exact (pr222 (is_right_adjoint_reflective C') x).
Qed.

Definition is_nat_z_iso_reflective_subcat_counit
           {C : category}
           (C' : reflective_subcat C)
           (x : C')
  : is_z_isomorphism (reflective_subcat_counit C' x).
Proof.
  use counit_is_z_iso_if_right_adjoint_is_fully_faithful.
  exact (fully_faithful_reflective C').
Defined.

Definition reflective_subcat_counit_iso
           {C : category}
           (C' : reflective_subcat C)
           (x : C')
  : z_iso (reflective_subcat_left_adjoint C' (C' x)) x
  := _ ,, is_nat_z_iso_reflective_subcat_counit C' x.

Proposition preserves_terminal_reflective
           {C : category}
           (C' : reflective_subcat C)
  : preserves_terminal C'.
Proof.
  exact (right_adjoint_preserves_terminal
           (reflective_subcat_left_adjoint C')
           (is_left_adjoint_left_adjoint _)).
Qed.

Proposition preserves_binproduct_reflective
           {C : category}
           (C' : reflective_subcat C)
  : preserves_binproduct C'.
Proof.
  exact (right_adjoint_preserves_binproduct
           (reflective_subcat_left_adjoint C')
           (is_left_adjoint_left_adjoint _)).
Qed.

Proposition preserves_equalizer_reflective
           {C : category}
           (C' : reflective_subcat C)
  : preserves_equalizer C'.
Proof.
  exact (right_adjoint_preserves_equalizer
           (reflective_subcat_left_adjoint C')
           (is_left_adjoint_left_adjoint _)).
Qed.

Proposition preserves_pullback_reflective
           {C : category}
           (C' : reflective_subcat C)
  : preserves_pullback C'.
Proof.
  exact (right_adjoint_preserves_pullback
           (reflective_subcat_left_adjoint C')
           (is_left_adjoint_left_adjoint _)).
Qed.


Definition exact_reflective_subcat
           (C : category)
  : UU
  := ∑ (C' : reflective_subcat C),
     preserves_terminal (reflective_subcat_left_adjoint C')
     ×
     preserves_pullback (reflective_subcat_left_adjoint C').

Coercion exact_reflective_subcat_to_reflective_subcat
         {C : category}
         (C' : exact_reflective_subcat C)
  : reflective_subcat C
  := pr1 C'.

Definition preserves_terminal_exact_reflective_subcat
           {C : category}
           (C' : exact_reflective_subcat C)
  : preserves_terminal (reflective_subcat_left_adjoint C').
Proof.
  exact (pr12 C').
Defined.

Definition preserves_pullback_exact_reflective_subcat
           {C : category}
           (C' : exact_reflective_subcat C)
  : preserves_pullback (reflective_subcat_left_adjoint C').
Proof.
  exact (pr22 C').
Defined.

Definition preserves_monic_exact_reflective_subcat
           {C : category}
           (C' : exact_reflective_subcat C)
           {x y : C'}
           (f : Monic C' x y)
  : Monic C (C' x) (C' y).
Proof.
  refine (functor_preserves_pb_on_monic _ f).
  exact (right_adjoint_preserves_pullback
           _
           (is_left_adjoint_left_adjoint
              (is_right_adjoint_reflective C'))).
Qed.


Definition exact_reflective_subcat_terminal
           {C : category}
           (C' : exact_reflective_subcat C)
           (T : Terminal C)
  : Terminal C'.
Proof.
  exact (preserves_terminal_to_terminal
           _
           (preserves_terminal_exact_reflective_subcat C')
           T).
Defined.

Definition exact_reflective_subcat_pullbacks
           {C : category}
           (C' : exact_reflective_subcat C)
           (PB : Pullbacks C)
  : Pullbacks C'.
Proof.
  intros x y z f g.
  pose (functor_preserves_pullback_on_pullback
          PB
          (preserves_pullback_exact_reflective_subcat C')
          (#C' f) (#C' g))
    as P.
  use make_Pullback.
  - exact P.
  - exact (PullbackPr1 P · reflective_subcat_counit_iso C' y).
  - exact (PullbackPr2 P · reflective_subcat_counit_iso C' z).
  - abstract
      (cbn ;
       rewrite !assoc' ;
       refine (maponpaths
                 (λ z, _ · z)
                 (!(nat_trans_ax (reflective_subcat_counit C') _ _ f))
               @ _) ;
       refine (_ @ maponpaths
                     (λ z, _ · z)
                     (nat_trans_ax (reflective_subcat_counit C') _ _ g)) ;
       cbn ;
       rewrite !assoc ;
       rewrite <- !functor_comp ;
       rewrite PullbackSqrCommutes ;
       apply idpath).
  - use (Pullback_iso_squares _ (isPullback_Pullback P)).
    + exact (z_iso_inv (reflective_subcat_counit_iso C' y)).
    + exact (z_iso_inv (reflective_subcat_counit_iso C' z)).
    + exact (z_iso_inv (reflective_subcat_counit_iso C' x)).
    + apply identity_z_iso.
    + abstract
        (simpl ;
         use z_iso_inv_on_left ;
         rewrite !assoc' ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         exact (nat_trans_ax (reflective_subcat_counit C') _ _ f)).
    + abstract
        (simpl ;
         use z_iso_inv_on_left ;
         rewrite !assoc' ;
         refine (!_) ;
         use z_iso_inv_on_right ;
         exact (nat_trans_ax (reflective_subcat_counit C') _ _ g)).
    + abstract
        (rewrite id_left ;
         rewrite !assoc' ;
         refine (!(id_right _) @ !_) ;
         apply maponpaths ;
         apply z_iso_inv_after_z_iso).
    + abstract
        (rewrite id_left ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         apply z_iso_inv_after_z_iso).
Defined.

Definition preserves_binproduct_exact_reflective_subcat
           {C : category}
           (C' : exact_reflective_subcat C)
           (T : Terminal C)
           (PB : Pullbacks C)
  : preserves_binproduct (reflective_subcat_left_adjoint C').
Proof.
  use preserves_binproduct_from_pullback_terminal.
  - exact T.
  - exact PB.
  - exact (preserves_pullback_exact_reflective_subcat C').
  - exact (preserves_terminal_exact_reflective_subcat C').
Qed.


Section ExactReflectiveSubCatExponentials.
  Context {C : category}
          (T : Terminal C)
          (PB : Pullbacks C)
          (BP := BinProductsFromPullbacks PB T)
          (E : Exponentials BP)
          (C' : exact_reflective_subcat C)
          (T' := exact_reflective_subcat_terminal C' T)
          (PB' := exact_reflective_subcat_pullbacks C' PB)
          (BP' := BinProductsFromPullbacks PB' T')
          (x y : C').

  Let L : C ⟶ C' := reflective_subcat_left_adjoint C'.
  Let R : C' ⟶ C := C'.

  Let η : functor_identity _ ⟹ L ∙ R
    := reflective_subcat_unit C'.
  Let ε (a : C') : z_iso (L(R a)) a
    := reflective_subcat_counit_iso C' a.

  Definition exact_reflective_subcat_unit_factor
             {z : C}
             (f : z --> exp (E (R x)) (R y))
    : ∃! (h : R(L z) --> exp (E (R x)) (R y)), f = η z · h.
  Proof.
    use iscontraprop1.
    - admit.
    - simple refine (_ ,, _).
      + use exp_lam.
        refine (inv_from_z_iso
                  (preserves_binproduct_to_z_iso
                     _
                     (preserves_binproduct_reflective C')
                     (BP' x (L z))
                     (BP (R x) (R(L z))))
                · _).
        refine (#R(BinProductOfArrows
                     _
                     (BP' (L(R x)) (L z))
                     (BP' x (L z))
                     (inv_from_z_iso (ε x))
                     (identity _))
                · _).
        refine (#R(inv_from_z_iso
                     (preserves_binproduct_to_z_iso
                        L
                        (preserves_binproduct_exact_reflective_subcat C' T PB)
                        (BP (R x) z)
                        (BP' (L(R x)) (L z))))
                · _).
        refine (#R _).
        refine (#L _ · ε _).
        refine (BinProductOfArrows _ (BP _ _) (BP _ _) (identity _) f · _).
        apply exp_eval.
      + simpl.
  Admitted.

  (*
    from uniqueness, you can get that if η f = η g, then f = g
    this allows us to conclude that η is an isomorphism
   *)

  Definition is_z_isomorphism_reflective_subcat_unit_exp
    : is_z_isomorphism (η (exp (E (R x)) (R y))).
  Proof.
    (*
    pose (exact_reflective_subcat_unit_factor (identity _)) as H.
    pose (φ := pr11 H).
    use make_is_z_isomorphism.
    - exact φ.
    - refine (!(pr21 H) ,, _).
      refine (nat_trans_ax η _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (!id_left _ @ _).
        apply maponpaths_2.
        refine (!_).
        refine (_ @ functor_id R _).
        apply maponpaths.
        apply reflective_subcat_triangle_1.
      }
      rewrite !functor_comp.
      cbn.
      rewrite !assoc.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply (functor_comp R).
      }

      simpl.


        use exp_lam.
        refine (η (BP xx (R (L z))) · #R _).
        use (fully_faithful_inv_hom (fully_faithful_reflective C')).
        refine (#R (BinProductOfArrows _ (BP' _ _) _ (ε x) (identity _)) · _).
        simpl.

     *)
  Admitted.


(*
  L : C' --> C
  R : C --> C'

  L ⊣ R

  R is ff
  L preserves finite limits

  x y : C'
  Exponential: R(L x --> L y)

  Evaluation:
        x × R(L x --> L y) --> y


  L(R x) ≅ x
 *)


Proposition isMonic_exact_reflective_subcat_left_adj
            {C : category}
            (C' : exact_reflective_subcat C)
            {x y : C}
            {f : x --> y}
            (Hf : isMonic f)
  : isMonic (#(reflective_subcat_left_adjoint C') f).
Proof.
  exact (is_monic_functor_preserves_pb
           (preserves_pullback_exact_reflective_subcat C')
           f
           Hf).
Qed.

Proposition isMonic_exact_reflective_subcat_inv
            {C : category}
            (C' : exact_reflective_subcat C)
            {x y : C'}
            {f : x --> y}
            (Hf : isMonic (#C' f))
  : isMonic f.
Proof.
  exact (fully_faithful_reflects_monic (fully_faithful_reflective C') Hf).
Qed.

Proposition reflective_subcat_left_adjoint_mor_inv
            {C : category}
            (C' : exact_reflective_subcat C)
            {x y : C'}
            {f : x --> y}
  : #(reflective_subcat_left_adjoint C') (#C' f)
    =
    reflective_subcat_counit_iso C' x
    · f
    · inv_from_z_iso (reflective_subcat_counit_iso C' y).
Proof.
  cbn.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply (nat_trans_ax (reflective_subcat_counit C')).
  }
  cbn.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    apply (z_iso_inv_after_z_iso (reflective_subcat_counit_iso C' y)).
  }
  apply id_right.
Qed.

Proposition isMonic_exact_reflective_subcat
            {C : category}
            (C' : exact_reflective_subcat C)
            {x y : C'}
            {f : x --> y}
            (Hf : isMonic f)
  : isMonic (#C' f).
Proof.
  exact (fully_faithful_reflects_monic (fully_faithful_reflective C') Hf).
Qed.

Definition exact_reflective_subcat_subobject_classifier
           {C : category}
           (T : Terminal C)
           (C' : exact_reflective_subcat C)
           (Ω : subobject_classifier T)
  : subobject_classifier (exact_reflective_subcat_terminal C' T).
Proof.
  use make_subobject_classifier.
  - exact (reflective_subcat_left_adjoint C' Ω).
  - exact (#(reflective_subcat_left_adjoint C') (true Ω)).
  - intros x y m.
    use iscontraprop1.
    + admit.
    + simple refine (_ ,, _ ,, _).
      * Search fully_faithful isMonic.
