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
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Exponentials.

Local Open Scope cat.

Proposition BinProductOfArrows_comp'
            {C : category}
            {a b c d x y : C}
            (P₁ : BinProduct _ c d)
            (P₂ : BinProduct _ x y)
            (P₃ : BinProduct _ a b)
            (f : a --> c)
            (f' : b --> d)
            (g : c --> x)
            (g' : d --> y)
  : BinProductOfArrows C P₁ P₃ f f' · BinProductOfArrows C P₂ _ g g'
    =
    BinProductOfArrows C _ _ (f · g) (f' · g').
Proof.
  use BinProductArrowsEq.
  - rewrite !assoc'.
    rewrite !BinProductOfArrowsPr1.
    rewrite !assoc.
    rewrite BinProductOfArrowsPr1.
    apply idpath.
  - rewrite !assoc'.
    rewrite !BinProductOfArrowsPr2.
    rewrite !assoc.
    rewrite BinProductOfArrowsPr2.
    apply idpath.
Qed.



Definition exp_fun_left
           {C : category}
           {P : BinProducts C}
           (E : Exponentials P)
           {x₁ x₂ : C}
           (f : x₂ --> x₁)
           (y : C)
  : exp (E x₁) y --> exp (E x₂) y.
Proof.
  use exp_lam.
  refine (_ · exp_eval (E x₁) y).
  use BinProductOfArrows.
  - exact f.
  - exact (identity _).
Defined.

Proposition exp_fun_left_id
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            (x : C)
            (y : C)
  : exp_fun_left E (identity x) y = identity _.
Proof.
  unfold exp_fun_left.
  use exp_funext.
  intros a h.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  rewrite BinProductOfArrows_id.
  rewrite id_left.
  apply idpath.
Qed.

Proposition exp_fun_left_comp
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            {x₁ x₂ x₃ : C}
            (f : x₂ --> x₁)
            (g : x₃ --> x₂)
            (y : C)
  : exp_fun_left E (g · f) y = exp_fun_left E f y · exp_fun_left E g y.
Proof.
  unfold exp_fun_left.
  use exp_funext.
  intros a h.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths_2.
    exact (!(id_right h)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  rewrite !assoc.
  rewrite BinProductOfArrows_comp.
  rewrite id_right.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right _)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  rewrite !assoc.
  rewrite !BinProductOfArrows_comp.
  rewrite !id_left.
  rewrite assoc.
  apply idpath.
Qed.

Definition exp_fun_right
           {C : category}
           {P : BinProducts C}
           (E : Exponentials P)
           (x : C)
           {y₁ y₂ : C}
           (f : y₁ --> y₂)
  : exp (E x) y₁ --> exp (E x) y₂.
Proof.
  use exp_lam.
  exact (exp_eval (E x) y₁ · f).
Defined.

Proposition exp_fun_right_id
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            (x : C)
            (y : C)
  : exp_fun_right E x (identity y) = identity _.
Proof.
  unfold exp_fun_right.
  use exp_funext.
  intros a h.
  rewrite id_right.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  apply idpath.
Qed.

Proposition exp_fun_right_comp
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            (x : C)
            {y₁ y₂ y₃ : C}
            (f : y₁ --> y₂)
            (g : y₂ --> y₃)
  : exp_fun_right E x (f · g) = exp_fun_right E x f · exp_fun_right E x g.
Proof.
  unfold exp_fun_right.
  use exp_funext.
  intros a h.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths_2.
    exact (!(id_right h)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  rewrite !assoc.
  apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  apply idpath.
Qed.

Proposition exp_fun_left_right
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            {x₁ x₂ : C}
            (f : x₂ --> x₁)
            {y₁ y₂ : C}
            (g : y₁ --> y₂)
  : exp_fun_left E f y₁ · exp_fun_right E x₂ g
    =
    exp_fun_right E x₁ g · exp_fun_left E f y₂.
Proof.
  use exp_funext.
  intros a h.
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  etrans.
  {
    apply maponpaths.
    do 2 apply maponpaths_2.
    exact (!(id_left _)).
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right h)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  apply maponpaths.
  etrans.
  {
    do 2 apply maponpaths_2.
    exact (!(id_left _)).
  }
  rewrite <- !BinProductOfArrows_comp.
  unfold exp_fun_left, exp_fun_right.
  rewrite !assoc'.
  rewrite !exp_beta.
  rewrite !assoc.
  etrans.
  {
    rewrite BinProductOfArrows_comp.
    rewrite id_left, id_right.
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(id_right _)).
    }
    apply maponpaths.
    exact (!(id_left _)).
  }
  rewrite <- BinProductOfArrows_comp.
  rewrite !assoc'.
  rewrite exp_beta.
  rewrite !assoc.
  rewrite exp_beta.
  apply idpath.
Qed.

Definition exp_functor
           {C : category}
           {P : BinProducts C}
           (E : Exponentials P)
           {x₁ x₂ : C}
           (f : x₂ --> x₁)
           {y₁ y₂ : C}
           (g : y₁ --> y₂)
  : exp (E x₁) y₁ --> exp (E x₂) y₂
  := exp_fun_left E f y₁ · exp_fun_right E x₂ g.

Proposition exp_functor_id
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            (x y : C)
  : exp_functor E (identity x) (identity y) = identity _.
Proof.
  unfold exp_functor.
  rewrite exp_fun_left_id, exp_fun_right_id.
  apply id_left.
Qed.

Proposition exp_functor_comp
            {C : category}
            {P : BinProducts C}
            (E : Exponentials P)
            {x₁ x₂ x₃ : C}
            (f : x₂ --> x₁)
            (f' : x₃ --> x₂)
            {y₁ y₂ y₃ : C}
            (g : y₁ --> y₂)
            (g' : y₂ --> y₃)
  : exp_functor E f g · exp_functor E f' g' = exp_functor E (f' · f) (g · g').
Proof.
  unfold exp_functor.
  rewrite exp_fun_left_comp, exp_fun_right_comp.
  rewrite !assoc'.
  apply maponpaths.
  rewrite !assoc.
  rewrite exp_fun_left_right.
  apply idpath.
Qed.



Proposition characteristic_morphism_eq
            {C : category}
            {T : Terminal C}
            (Ω : subobject_classifier T)
            {x₁ x₂ y : C}
            (m₁ : Monic C x₁ y)
            (m₂ : Monic C x₂ y)
            (f : z_iso x₁ x₂)
            (p : f · m₂ = m₁)
  : characteristic_morphism Ω m₁ = characteristic_morphism Ω m₂.
Proof.
  use (subobject_classifier_map_eq Ω m₁).
  - apply subobject_classifier_square_commutes.
  - abstract
      (rewrite <- p ;
       rewrite !assoc' ;
       rewrite subobject_classifier_square_commutes ;
       unfold const_true ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - exact (isPullback_Pullback (subobject_classifier_pullback Ω m₁)).
  - pose (PB := subobject_classifier_pullback Ω m₁).
    pose (PB' := subobject_classifier_pullback Ω m₂).
    intros w h k q.
    use iscontraprop1.
    + use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use (MorphismsIntoPullbackEqual (isPullback_Pullback PB)).
      * exact (pr12 φ₁ @ !(pr12 φ₂)).
      * apply TerminalArrowEq.
    + simple refine (_ ,, _ ,, _).
      * refine (_ · inv_from_z_iso f).
        use (PullbackArrow PB').
        ** exact h.
        ** exact k.
        ** exact q.
      * rewrite <- p.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite assoc.
          rewrite z_iso_after_z_iso_inv.
          apply id_left.
        }
        apply (PullbackArrow_PullbackPr1 PB').
      * apply TerminalArrowEq.
Qed.

Proposition characteristic_morphism_precomp
            {C : category}
            {T : Terminal C}
            (PB : Pullbacks C)
            (Ω : subobject_classifier T)
            {x y₁ y₂ : C}
            (m : Monic C x y₂)
            (f : y₁ --> y₂)
  : f · characteristic_morphism Ω m
    =
    characteristic_morphism Ω (pullback_pr1_monic m _ (PB _ _ _ f m)).
Proof.
  pose (P := PB y₂ y₁ x f m).
  pose (m' := pullback_pr1_monic m f P).
  pose (P' := subobject_classifier_pullback Ω m').
  pose (P'' := subobject_classifier_pullback Ω m).
  use (subobject_classifier_map_eq Ω m').
  - abstract
      (cbn ;
       rewrite !assoc ;
       rewrite PullbackSqrCommutes ;
       rewrite !assoc' ;
       rewrite subobject_classifier_square_commutes ;
       unfold const_true ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - apply subobject_classifier_square_commutes.
  - intros w h k p.
    use iscontraprop1.
    + use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      use (MorphismsIntoPullbackEqual (isPullback_Pullback P')).
      * exact (pr12 φ₁ @ !(pr12 φ₂)).
      * apply TerminalArrowEq.
    + simple refine (_ ,, _ ,, _).
      * use (PullbackArrow P).
        ** exact h.
        ** use (PullbackArrow P'').
           *** exact (h · f).
           *** exact k.
           *** abstract
               (rewrite assoc' ;
                exact p).
        ** abstract
            (refine (!_) ;
             apply (PullbackArrow_PullbackPr1 P'')).
      * rewrite PullbackArrow_PullbackPr1.
        apply idpath.
      * apply TerminalArrowEq.
  - exact (isPullback_Pullback (subobject_classifier_pullback Ω m')).
Qed.


Definition functor_subobject_classifier_mor_monic
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {T₁ : Terminal C₁}
           (Ω₁ : subobject_classifier T₁)
           {T₂ : Terminal C₂}
           (Ω₂ : subobject_classifier T₂)
           (HF : preserves_terminal F)
  : Monic _ T₂ (F Ω₁).
Proof.
  use make_Monic.
  - exact (inv_from_z_iso (preserves_terminal_to_z_iso F HF T₁ T₂) · #F Ω₁).
  - abstract
      (intros x f g p ;
       apply TerminalArrowEq).
Defined.

Definition functor_subobject_classifier_mor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {T₁ : Terminal C₁}
           (Ω₁ : subobject_classifier T₁)
           {T₂ : Terminal C₂}
           (Ω₂ : subobject_classifier T₂)
           (HF : preserves_terminal F)
  : F Ω₁ --> Ω₂.
Proof.
  use characteristic_morphism.
  - exact T₂.
  - exact (functor_subobject_classifier_mor_monic Ω₁ Ω₂ HF).
Defined.

Proposition functor_subobject_classifier_mor_comm
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {T₁ : Terminal C₁}
            (Ω₁ : subobject_classifier T₁)
            {T₂ : Terminal C₂}
            (Ω₂ : subobject_classifier T₂)
            (HF : preserves_terminal F)
  : functor_subobject_classifier_mor_monic Ω₁ Ω₂ HF
    · functor_subobject_classifier_mor Ω₁ Ω₂ HF
    =
    TerminalArrow T₂ T₂ · Ω₂.
Proof.
  exact (subobject_classifier_square_commutes
           Ω₂
           (functor_subobject_classifier_mor_monic Ω₁ Ω₂ HF)).
Qed.

Proposition functor_subobject_classifier_mor_comm'
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {T₁ : Terminal C₁}
            (Ω₁ : subobject_classifier T₁)
            {T₂ : Terminal C₂}
            (Ω₂ : subobject_classifier T₂)
            (HF : preserves_terminal F)
  : # F (true' Ω₁)
    · functor_subobject_classifier_mor Ω₁ Ω₂ HF
    =
    TerminalArrow _ _ · Ω₂.
Proof.
  use (cancel_z_iso' (z_iso_inv (preserves_terminal_to_z_iso F HF T₁ T₂))).
  cbn.
  rewrite !assoc.
  etrans.
  {
    apply functor_subobject_classifier_mor_comm.
  }
  apply maponpaths_2.
  apply TerminalArrowEq.
Qed.


Definition gluing
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : category
  := comma (functor_identity _) F.

Definition gluing_pr1_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : gluing F ⟶ C₁
  := comma_pr2 _ _.

Definition gluing_pr2_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : gluing F ⟶ C₂
  := comma_pr1 _ _.

Definition make_gluing_ob
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           (x : C₁)
           (y : C₂)
           (f : y --> F x)
  : gluing F
  := (y ,, x) ,, f.

Definition gluing_pr1
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           (x : gluing F)
  : C₁
  := gluing_pr1_functor F x.

Definition gluing_pr2
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           (x : gluing F)
  : C₂
  := gluing_pr2_functor F x.

Definition gluing_mor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           (x : gluing F)
  : gluing_pr2 x --> F(gluing_pr1 x)
  := comma_commute _ _ x.

Definition make_gluing_mor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {x y : gluing F}
           (f : gluing_pr1 x --> gluing_pr1 y)
           (g : gluing_pr2 x --> gluing_pr2 y)
           (p : gluing_mor x · #F f = g · gluing_mor y)
  : x --> y
  := (g ,, f) ,, p.

Definition gluing_mor_pr1
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {x y : gluing F}
           (f : x --> y)
  : gluing_pr1 x --> gluing_pr1 y
  := #(comma_pr2 _ _) f.

Definition gluing_mor_pr2
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {x y : gluing F}
            (f : x --> y)
  : gluing_pr2 x --> gluing_pr2 y
  := #(comma_pr1 _ _) f.

Proposition gluing_mor_eq
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {x y : gluing F}
            (f : x --> y)
  : gluing_mor x · #F (gluing_mor_pr1 f)
    =
    gluing_mor_pr2 f · gluing_mor y.
Proof.
  exact (!(nat_trans_ax (comma_commute _ _) _ _ f)).
Qed.

Proposition eq_gluing_mor
            {C₁ C₂ : category}
            {F : C₁ ⟶ C₂}
            {x y : gluing F}
            {f g : x --> y}
            (p : gluing_mor_pr1 f = gluing_mor_pr1 g)
            (q : gluing_mor_pr2 f = gluing_mor_pr2 g)
  : f = g.
Proof.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  use pathsdirprod.
  - exact q.
  - exact p.
Qed.

Section Gluing.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition gluing_pr1_functor_coreflection_data
             (x : C₁)
    : coreflection_data x (gluing_pr1_functor F).
  Proof.
    use make_coreflection_data.
    - use make_gluing_ob.
      + exact x.
      + exact (F x).
      + exact (identity _).
    - apply identity.
  Defined.

  Definition is_left_adjoint_gluing_pr1_functor
    : is_left_adjoint (gluing_pr1_functor F).
  Proof.
    use coreflections_to_is_left_adjoint.
    intro x.
    use make_coreflection.
    - exact (gluing_pr1_functor_coreflection_data x).
    - intros f.
      induction f as [ y f ].
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros φ₁ φ₂ ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           pose (p := !(pr2 φ₁) @ pr2 φ₂) ;
           cbn in p ;
           rewrite !id_right in p ;
           use eq_gluing_mor ; [ apply p | ];
           refine (!(id_right _) @ _) ;
           refine (!(gluing_mor_eq (pr1 φ₁)) @ _) ;
           refine (_ @ id_right _) ;
           refine (_ @ gluing_mor_eq (pr1 φ₂)) ;
           do 2 apply maponpaths ;
           exact p).
      + simple refine (_ ,, _).
        * use make_gluing_mor.
          ** exact f.
          ** exact (gluing_mor y · #F f).
          ** abstract
              (cbn ;
               rewrite id_right ;
               apply idpath).
        * abstract
            (cbn ;
             exact (!(id_right _))).
  Defined.

  Definition gluing_pr1_functor_right_adj
    : C₁ ⟶ gluing F
    := right_adjoint is_left_adjoint_gluing_pr1_functor.

  Proposition fully_faithful_gluing_pr1_functor_right_adj
    : fully_faithful gluing_pr1_functor_right_adj.
  Proof.
    use full_and_faithful_implies_fully_faithful.
    split.
    - intros x y f.
      use hinhpr.
      simple refine (_ ,, _).
      + exact (gluing_mor_pr1 f).
      + use eq_gluing_mor ; cbn.
        * apply id_left.
        * rewrite !id_left.
          pose (gluing_mor_eq f) as p ; cbn in p.
          rewrite id_left, id_right in p.
          exact p.
    - intros x y f.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      pose (p := maponpaths gluing_mor_pr1 (pr2 φ₁ @ !(pr2 φ₂))).
      cbn in p.
      rewrite !id_left in p.
      exact p.
  Qed.


  Section RightAdj.
    Context (T₁ : Terminal C₁)
            (HF : preserves_terminal F).

    Let T₂ : Terminal C₂
      := preserves_terminal_to_terminal F HF T₁.

    Definition gluing_pr2_functor_coreflection_data
               (x : C₂)
      : coreflection_data x (gluing_pr2_functor F).
    Proof.
      use make_coreflection_data.
      - use make_gluing_ob.
        + exact T₁.
        + exact x.
        + exact (TerminalArrow T₂ x).
      - apply identity.
    Defined.

    Definition is_left_adjoint_gluing_pr2_functor
      : is_left_adjoint (gluing_pr2_functor F).
    Proof.
      use coreflections_to_is_left_adjoint.
      intro x.
      use make_coreflection.
      - exact (gluing_pr2_functor_coreflection_data x).
      - intros f.
        induction f as [ y f ].
        use iscontraprop1.
        + abstract
            (use invproofirrelevance ;
             intros φ₁ φ₂ ;
             use subtypePath ; [ intro ; apply homset_property | ] ;
             pose (p := !(pr2 φ₁) @ pr2 φ₂) ;
             cbn in p ;
             rewrite !id_right in p ;
             use eq_gluing_mor ; [ | apply p ] ;
             apply TerminalArrowEq).
        + simple refine (_ ,, _).
          * use make_gluing_mor.
            ** apply TerminalArrow.
            ** exact f.
            ** abstract
                (apply (TerminalArrowEq (T := T₂))).
          * abstract
              (cbn ;
               exact (!(id_right _))).
    Defined.

    Definition gluing_pr2_functor_right_adj
      : C₂ ⟶ gluing F
      := right_adjoint is_left_adjoint_gluing_pr2_functor.

    Proposition fully_faithful_gluing_pr2_functor_right_adj
      : fully_faithful gluing_pr2_functor_right_adj.
    Proof.
      use full_and_faithful_implies_fully_faithful.
      split.
      - intros x y f.
        use hinhpr.
        simple refine (_ ,, _).
        + exact (gluing_mor_pr2 f).
        + use eq_gluing_mor ; cbn.
          * apply TerminalArrowEq.
          * rewrite id_left.
            apply idpath.
      - intros x y f.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        pose (p := maponpaths gluing_mor_pr2 (pr2 φ₁ @ !(pr2 φ₂))).
        cbn in p.
        rewrite !id_left in p.
        exact p.
    Qed.
  End RightAdj.


  Definition gluing_terminal
             (T₁ : Terminal C₁)
             (T₂ : Terminal C₂)
             (HF : preserves_terminal F)
    : Terminal (gluing F).
  Proof.
    use make_Terminal.
    - use make_gluing_ob.
      + exact T₁.
      + exact T₂.
      + apply (TerminalArrow (preserves_terminal_to_terminal F HF T₁)).
    - intros x.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros f₁ f₂ ;
           use eq_gluing_mor ;
           cbn ;
           apply TerminalArrowEq).
      + use make_gluing_mor ; cbn.
        * apply TerminalArrow.
        * apply TerminalArrow.
        * abstract
            (apply (TerminalArrowEq (T := preserves_terminal_to_terminal F HF T₁))).
  Defined.

  Definition preserves_terminal_gluing_pr1
             (T₁ : Terminal C₁)
             (T₂ : Terminal C₂)
             (HF : preserves_terminal F)
    : preserves_terminal (gluing_pr1_functor F).
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      exact (gluing_terminal T₁ T₂ HF).
    }
    unfold preserves_chosen_terminal ; cbn.
    apply T₁.
  Defined.

  Definition preserves_terminal_gluing_pr2
             (T₁ : Terminal C₁)
             (T₂ : Terminal C₂)
             (HF : preserves_terminal F)
    : preserves_terminal (gluing_pr2_functor F).
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      exact (gluing_terminal T₁ T₂ HF).
    }
    unfold preserves_chosen_terminal ; cbn.
    apply T₂.
  Defined.



  Section GluingBinProduct.
    Context (BP₁ : BinProducts C₁)
            (BP₂ : BinProducts C₂)
            (HF : preserves_binproduct F)
            (x y : gluing F).

    Let P : BinProduct C₂ (F (gluing_pr1 x)) (F (gluing_pr1 y))
      := preserves_binproduct_to_binproduct
           F HF
           (BP₁ (gluing_pr1 x) (gluing_pr1 y)).

    Definition gluing_binproduct_ob
      : gluing F.
    Proof.
      use make_gluing_ob.
      - exact (BP₁ (gluing_pr1 x) (gluing_pr1 y)).
      - exact (BP₂ (gluing_pr2 x) (gluing_pr2 y)).
      - exact (BinProductOfArrows _ P _ (gluing_mor x) (gluing_mor y)).
    Defined.

    Proposition gluing_mor_binproduct_ob
      : gluing_mor gluing_binproduct_ob
        =
        BinProductOfArrows _ P _ (gluing_mor x) (gluing_mor y).
    Proof.
      apply idpath.
    Qed.

    Arguments gluing_binproduct_ob /.

    Definition gluing_binproduct_pr1
      : gluing_binproduct_ob --> x.
    Proof.
      use make_gluing_mor.
      - exact (BinProductPr1 _ _).
      - exact (BinProductPr1 _ _).
      - abstract
          (apply (BinProductPr1Commutes _ _ _ P)).
    Defined.

    Definition gluing_binproduct_pr2
      : gluing_binproduct_ob --> y.
    Proof.
      use make_gluing_mor.
      - exact (BinProductPr2 _ _).
      - exact (BinProductPr2 _ _).
      - abstract
          (apply (BinProductPr2Commutes _ _ _ P)).
    Defined.

    Section UMP.
      Context {w : gluing F}
              (f : w --> x)
              (g : w --> y).

      Definition gluing_binproduct_pair
        : w --> gluing_binproduct_ob.
      Proof.
        use make_gluing_mor.
        - use BinProductArrow.
          + exact (gluing_mor_pr1 f).
          + exact (gluing_mor_pr1 g).
        - use BinProductArrow.
          + exact (gluing_mor_pr2 f).
          + exact (gluing_mor_pr2 g).
        - use (BinProductArrowsEq _ _ _ P).
          + abstract
              (refine (assoc' _ _ _ @ _) ;
               refine (maponpaths (λ z, _ · z) ((!functor_comp _ _ _)) @ _) ;
               refine (maponpaths (λ z, _ · #F z) (BinProductPr1Commutes _ _ _ _ _ _ _) @ _) ;
               refine (gluing_mor_eq f @ _) ;
               refine (!_) ;
               unfold gluing_mor ; simpl ;
               rewrite assoc' ;
               etrans ;
               [ apply maponpaths ;
                 apply (BinProductOfArrowsPr1 _ P (BP₂ _ _))
               | ] ;
               rewrite assoc ;
               rewrite BinProductPr1Commutes ;
               apply idpath).
          + abstract
              (refine (assoc' _ _ _ @ _) ;
               refine (maponpaths (λ z, _ · z) ((!functor_comp _ _ _)) @ _) ;
               refine (maponpaths (λ z, _ · #F z) (BinProductPr2Commutes _ _ _ _ _ _ _) @ _) ;
               refine (gluing_mor_eq g @ _) ;
               refine (!_) ;
               unfold gluing_mor ; simpl ;
               rewrite assoc' ;
               etrans ;
               [ apply maponpaths ;
                 apply (BinProductOfArrowsPr2 _ P (BP₂ _ _))
               | ] ;
               rewrite assoc ;
               rewrite BinProductPr2Commutes ;
               apply idpath).
      Defined.

      Proposition gluing_binproduct_pair_pr1
        : gluing_binproduct_pair · gluing_binproduct_pr1 = f.
      Proof.
        use eq_gluing_mor.
        - apply BinProductPr1Commutes.
        - apply BinProductPr1Commutes.
      Qed.

      Proposition gluing_binproduct_pair_pr2
        : gluing_binproduct_pair · gluing_binproduct_pr2 = g.
      Proof.
        use eq_gluing_mor.
        - apply BinProductPr2Commutes.
        - apply BinProductPr2Commutes.
      Qed.

      Proposition gluing_binproduct_unique
        : isaprop
            (∑ (fg : w --> gluing_binproduct_ob),
             fg · gluing_binproduct_pr1 = f
             ×
             fg · gluing_binproduct_pr2 = g).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use eq_gluing_mor.
        - use BinProductArrowsEq.
          + exact (maponpaths gluing_mor_pr1 (pr12 φ₁ @ !(pr12 φ₂))).
          + exact (maponpaths gluing_mor_pr1 (pr22 φ₁ @ !(pr22 φ₂))).
        - use BinProductArrowsEq.
          + exact (maponpaths gluing_mor_pr2 (pr12 φ₁ @ !(pr12 φ₂))).
          + exact (maponpaths gluing_mor_pr2 (pr22 φ₁ @ !(pr22 φ₂))).
      Qed.
    End UMP.

    Definition gluing_binproduct
      : BinProduct (gluing F) x y.
    Proof.
      use make_BinProduct.
      - exact gluing_binproduct_ob.
      - exact gluing_binproduct_pr1.
      - exact gluing_binproduct_pr2.
      - intros w f g.
        use iscontraprop1.
        + apply gluing_binproduct_unique.
        + simple refine (_ ,, _ ,, _).
          * exact (gluing_binproduct_pair f g).
          * exact (gluing_binproduct_pair_pr1 f g).
          * exact (gluing_binproduct_pair_pr2 f g).
    Defined.
  End GluingBinProduct.

  Definition gluing_binproducts
             (BP₁ : BinProducts C₁)
             (BP₂ : BinProducts C₂)
             (HF : preserves_binproduct F)
    : BinProducts (gluing F)
    := λ x y, gluing_binproduct BP₁ BP₂ HF x y.

  Definition preserves_binproduct_gluing_pr1
             (BP₁ : BinProducts C₁)
             (BP₂ : BinProducts C₂)
             (HF : preserves_binproduct F)
    : preserves_binproduct (gluing_pr1_functor F).
  Proof.
    use preserves_binproduct_if_preserves_chosen.
    {
      exact (gluing_binproducts BP₁ BP₂ HF).
    }
    intros x y.
    apply isBinProduct_BinProduct.
  Defined.

  Definition preserves_binproduct_gluing_pr2
             (BP₁ : BinProducts C₁)
             (BP₂ : BinProducts C₂)
             (HF : preserves_binproduct F)
    : preserves_binproduct (gluing_pr2_functor F).
  Proof.
    use preserves_binproduct_if_preserves_chosen.
    {
      exact (gluing_binproducts BP₁ BP₂ HF).
    }
    intros x y.
    apply BP₂.
  Defined.



  Section GluingEqualizer.
    Context (EQ₁ : Equalizers C₁)
            (EQ₂ : Equalizers C₂)
            (HF : preserves_equalizer F)
            {x y : gluing F}
            (f g : x --> y).

    Let E : Equalizer (#F (gluing_mor_pr1 f)) (#F (gluing_mor_pr1 g))
      := preserves_equalizer_equalizer HF (EQ₁ _ _ (gluing_mor_pr1 f) (gluing_mor_pr1 g)).

    Definition gluing_equalizer_ob
      : gluing F.
    Proof.
      use make_gluing_ob.
      - exact (EQ₁ _ _ (gluing_mor_pr1 f) (gluing_mor_pr1 g)).
      - exact (EQ₂ _ _ (gluing_mor_pr2 f) (gluing_mor_pr2 g)).
      - use (EqualizerIn E).
        + exact (EqualizerArrow _ · gluing_mor x).
        + abstract
            (rewrite !assoc' ;
             rewrite !gluing_mor_eq ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply EqualizerEqAr).
    Defined.

    Definition gluing_equalizer_arrow
      : gluing_equalizer_ob --> x.
    Proof.
      use make_gluing_mor.
      - exact (EqualizerArrow _).
      - exact (EqualizerArrow _).
      - abstract
          (exact (EqualizerCommutes E _ _ _)).
    Defined.

    Proposition gluing_equalizer_arrow_eq
      : gluing_equalizer_arrow · f = gluing_equalizer_arrow · g.
    Proof.
      use eq_gluing_mor ; cbn.
      - apply EqualizerEqAr.
      - apply EqualizerEqAr.
    Qed.

    Section UMP.
      Context {w : gluing F}
              (h : w --> x)
              (p : h · f = h · g).

      Definition gluing_equalizer_in
        : w --> gluing_equalizer_ob.
      Proof.
        use make_gluing_mor.
        - use EqualizerIn.
          + exact (gluing_mor_pr1 h).
          + exact (maponpaths gluing_mor_pr1 p).
        - use EqualizerIn.
          + exact (gluing_mor_pr2 h).
          + exact (maponpaths gluing_mor_pr2 p).
        - abstract
            (use (EqualizerInsEq E) ;
             refine (assoc' _ _ _ @ _) ;
             refine (maponpaths (λ z, _ · z) ((!functor_comp _ _ _)) @ _) ;
             refine (maponpaths (λ z, _ · #F z) (EqualizerCommutes _ _ _ _) @ _) ;
             refine (gluing_mor_eq _ @ _) ;
             refine (!_) ;
             refine (assoc' _ _ _ @ _) ;
             refine (maponpaths (λ z, _ · z) (EqualizerCommutes _ _ _ _) @ _) ;
             refine (assoc _ _ _ @ _) ;
             apply maponpaths_2 ;
             exact (EqualizerCommutes _ _ _ _)).
      Defined.

      Proposition gluing_equalizer_commutes
        : gluing_equalizer_in · gluing_equalizer_arrow = h.
      Proof.
        use eq_gluing_mor.
        - exact (EqualizerCommutes _ _ _ _).
        - exact (EqualizerCommutes _ _ _ _).
      Qed.

      Proposition gluing_equalizer_unique
        : isaprop
            (∑ (φ : w --> gluing_equalizer_ob),
             φ · gluing_equalizer_arrow = h).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use eq_gluing_mor.
        - use EqualizerInsEq.
          exact (maponpaths gluing_mor_pr1 (pr2 φ₁ @ !(pr2 φ₂))).
        - use EqualizerInsEq.
          exact (maponpaths gluing_mor_pr2 (pr2 φ₁ @ !(pr2 φ₂))).
      Qed.
    End UMP.

    Definition gluing_equalizer
      : Equalizer f g.
    Proof.
      use make_Equalizer.
      - exact gluing_equalizer_ob.
      - exact gluing_equalizer_arrow.
      - exact gluing_equalizer_arrow_eq.
      - intros w h p.
        use iscontraprop1.
        + apply gluing_equalizer_unique.
        + simple refine (_ ,, _).
          * exact (gluing_equalizer_in h p).
          * exact (gluing_equalizer_commutes h p).
    Defined.
  End GluingEqualizer.

  Definition gluing_equalizers
             (EQ₁ : Equalizers C₁)
             (EQ₂ : Equalizers C₂)
             (HF : preserves_equalizer F)
    : Equalizers (gluing F)
    := λ x y f g, gluing_equalizer EQ₁ EQ₂ HF f g.

  Definition preserves_equalizer_gluing_pr1
             (EQ₁ : Equalizers C₁)
             (EQ₂ : Equalizers C₂)
             (HF : preserves_equalizer F)
    : preserves_equalizer (gluing_pr1_functor F).
  Proof.
    use preserves_equalizer_if_preserves_chosen.
    {
      exact (gluing_equalizers EQ₁ EQ₂ HF).
    }
    intros x y f g p.
    apply isEqualizer_Equalizer.
  Defined.

  Definition preserves_equalizer_gluing_pr2
             (EQ₁ : Equalizers C₁)
             (EQ₂ : Equalizers C₂)
             (HF : preserves_equalizer F)
    : preserves_equalizer (gluing_pr2_functor F).
  Proof.
    use preserves_equalizer_if_preserves_chosen.
    {
      exact (gluing_equalizers EQ₁ EQ₂ HF).
    }
    intros x y f g p.
    apply EQ₂.
  Defined.




  Section GluingPullback.
    Context (PB₁ : Pullbacks C₁)
            (PB₂ : Pullbacks C₂)
            (HF : preserves_pullback F)
            {x y z : gluing F}
            (f : x --> z)
            (g : y --> z).

    Let P : Pullback (# F (gluing_mor_pr1 f)) (# F (gluing_mor_pr1 g))
      := functor_preserves_pullback_on_pullback PB₁ HF (gluing_mor_pr1 f) (gluing_mor_pr1 g).

    Definition gluing_pullback_ob
      : gluing F.
    Proof.
      use make_gluing_ob.
      - exact (PB₁ _ _ _ (gluing_mor_pr1 f) (gluing_mor_pr1 g)).
      - exact (PB₂ _ _ _ (gluing_mor_pr2 f) (gluing_mor_pr2 g)).
      - use (PullbackArrow P).
        + exact (PullbackPr1 _ · gluing_mor x).
        + exact (PullbackPr2 _ · gluing_mor y).
        + abstract
            (rewrite !assoc' ;
             rewrite !gluing_mor_eq ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply PullbackSqrCommutes).
    Defined.

    Definition gluing_pullback_pr1
      : gluing_pullback_ob --> x.
    Proof.
      use make_gluing_mor.
      - exact (PullbackPr1 _).
      - exact (PullbackPr1 _).
      - exact (PullbackArrow_PullbackPr1 P _ _ _ _).
    Defined.

    Definition gluing_pullback_pr2
      : gluing_pullback_ob --> y.
    Proof.
      use make_gluing_mor.
      - exact (PullbackPr2 _).
      - exact (PullbackPr2 _).
      - exact (PullbackArrow_PullbackPr2 P _ _ _ _).
    Defined.

    Proposition gluing_pullback_sqr
      : gluing_pullback_pr1 · f = gluing_pullback_pr2 · g.
    Proof.
      use eq_gluing_mor.
      - exact (PullbackSqrCommutes _).
      - exact (PullbackSqrCommutes _).
    Qed.

    Section UMP.
      Context {w : gluing F}
              (h : w --> x)
              (k : w --> y)
              (q : h · f = k · g).

      Definition gluing_pullback_mor
        : w --> gluing_pullback_ob.
      Proof.
        use make_gluing_mor.
        - use PullbackArrow.
          + exact (gluing_mor_pr1 h).
          + exact (gluing_mor_pr1 k).
          + abstract
              (exact (maponpaths gluing_mor_pr1 q)).
        - use PullbackArrow.
          + exact (gluing_mor_pr2 h).
          + exact (gluing_mor_pr2 k).
          + abstract
              (exact (maponpaths gluing_mor_pr2 q)).
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
          + abstract
              (refine (assoc' _ _ _ @ _) ;
               refine (maponpaths (λ z, _ · z) (!(functor_comp _ _ _)) @ _) ;
               refine (maponpaths (λ z, _ · #F z) (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _) ;
               refine (gluing_mor_eq _ @ _) ;
               refine (!_) ;
               refine (assoc' _ _ _ @ _) ;
               refine (maponpaths (λ z, _ · z) (PullbackArrow_PullbackPr1 _ _ _ _ _) @ _) ;
               refine (assoc _ _ _ @ _) ;
               apply maponpaths_2 ;
               exact (PullbackArrow_PullbackPr1 _ _ _ _ _)).
          + abstract
              (refine (assoc' _ _ _ @ _) ;
               refine (maponpaths (λ z, _ · z) (!(functor_comp _ _ _)) @ _) ;
               refine (maponpaths (λ z, _ · #F z) (PullbackArrow_PullbackPr2 _ _ _ _ _) @ _) ;
               refine (gluing_mor_eq _ @ _) ;
               refine (!_) ;
               refine (assoc' _ _ _ @ _) ;
               refine (maponpaths (λ z, _ · z) (PullbackArrow_PullbackPr2 _ _ _ _ _) @ _) ;
               refine (assoc _ _ _ @ _) ;
               apply maponpaths_2 ;
               exact (PullbackArrow_PullbackPr2 _ _ _ _ _)).
      Defined.

      Proposition gluing_pullback_mor_pr1
        : gluing_pullback_mor · gluing_pullback_pr1 = h.
      Proof.
        use eq_gluing_mor.
        - apply PullbackArrow_PullbackPr1.
        - apply PullbackArrow_PullbackPr1.
      Qed.

      Proposition gluing_pullback_mor_pr2
        : gluing_pullback_mor · gluing_pullback_pr2 = k.
      Proof.
        use eq_gluing_mor.
        - apply PullbackArrow_PullbackPr2.
        - apply PullbackArrow_PullbackPr2.
      Qed.

      Proposition gluing_pullback_unique
        : isaprop
            (∑ (hk : gluing F ⟦ w, gluing_pullback_ob ⟧),
             hk · gluing_pullback_pr1 = h
             ×
             hk · gluing_pullback_pr2 = k).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply homset_property.
        }
        use eq_gluing_mor.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          + exact (maponpaths gluing_mor_pr1 (pr12 φ₁ @ !(pr12 φ₂))).
          + exact (maponpaths gluing_mor_pr1 (pr22 φ₁ @ !(pr22 φ₂))).
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          + exact (maponpaths gluing_mor_pr2 (pr12 φ₁ @ !(pr12 φ₂))).
          + exact (maponpaths gluing_mor_pr2 (pr22 φ₁ @ !(pr22 φ₂))).
      Qed.
    End UMP.

    Definition gluing_pullback
      : Pullback f g.
    Proof.
      use make_Pullback.
      - exact gluing_pullback_ob.
      - exact gluing_pullback_pr1.
      - exact gluing_pullback_pr2.
      - exact gluing_pullback_sqr.
      - intros w h k q.
        use iscontraprop1.
        + apply gluing_pullback_unique.
        + simple refine (_ ,, _ ,, _).
          * exact (gluing_pullback_mor h k q).
          * exact (gluing_pullback_mor_pr1 h k q).
          * exact (gluing_pullback_mor_pr2 h k q).
    Defined.
  End GluingPullback.

  Definition gluing_pullbacks
             (PB₁ : Pullbacks C₁)
             (PB₂ : Pullbacks C₂)
             (HF : preserves_pullback F)
    : Pullbacks (gluing F)
    := λ x y z f g, gluing_pullback PB₁ PB₂ HF f g.

  Definition preserves_pullback_gluing_pr1
             (PB₁ : Pullbacks C₁)
             (PB₂ : Pullbacks C₂)
             (HF : preserves_pullback F)
    : preserves_pullback (gluing_pr1_functor F).
  Proof.
    use preserves_pullback_if_preserves_chosen.
    {
      exact (gluing_pullbacks PB₁ PB₂ HF).
    }
    intros x y f g p.
    apply isPullback_Pullback.
  Defined.

  Definition preserves_pullback_gluing_pr2
             (PB₁ : Pullbacks C₁)
             (PB₂ : Pullbacks C₂)
             (HF : preserves_pullback F)
    : preserves_pullback (gluing_pr2_functor F).
  Proof.
    use preserves_pullback_if_preserves_chosen.
    {
      exact (gluing_pullbacks PB₁ PB₂ HF).
    }
    intros x y f g p.
    apply PB₂.
  Defined.


  Proposition preserves_monic_gluing_pr1
              (PB₁ : Pullbacks C₁)
              (PB₂ : Pullbacks C₂)
              (HF : preserves_pullback F)
              {x y : gluing F}
              (f : x --> y)
              (Hf : isMonic f)
    : isMonic (gluing_mor_pr1 f).
  Proof.
    exact (is_monic_functor_preserves_pb
             (preserves_pullback_gluing_pr1 PB₁ PB₂ HF)
             f Hf).
  Qed.

  Definition gluing_pr1_monic
             (PB₁ : Pullbacks C₁)
             (PB₂ : Pullbacks C₂)
             (HF : preserves_pullback F)
             {x y : gluing F}
             (f : Monic _ x y)
    : Monic _ (gluing_pr1 x) (gluing_pr1 y)
    := functor_preserves_pb_on_monic (preserves_pullback_gluing_pr1 PB₁ PB₂ HF) f.

  Proposition preserves_monic_gluing_pr2
              (PB₁ : Pullbacks C₁)
              (PB₂ : Pullbacks C₂)
              (HF : preserves_pullback F)
              {x y : gluing F}
              (f : x --> y)
              (Hf : isMonic f)
    : isMonic (gluing_mor_pr2 f).
  Proof.
    exact (is_monic_functor_preserves_pb
             (preserves_pullback_gluing_pr2 PB₁ PB₂ HF)
             f Hf).
  Qed.

  Definition gluing_pr2_monic
             (PB₁ : Pullbacks C₁)
             (PB₂ : Pullbacks C₂)
             (HF : preserves_pullback F)
             {x y : gluing F}
             (f : Monic _ x y)
    : Monic _ (gluing_pr2 x) (gluing_pr2 y)
    := functor_preserves_pb_on_monic (preserves_pullback_gluing_pr2 PB₁ PB₂ HF) f.

  Proposition gluing_mor_monic
              {x y : gluing F}
              (f : x --> y)
              (Hf₁ : isMonic (gluing_mor_pr1 f))
              (Hf₂ : isMonic (gluing_mor_pr2 f))
    : isMonic f.
  Proof.
    intros w g₁ g₂ p.
    use eq_gluing_mor.
    - use Hf₁.
      exact (maponpaths gluing_mor_pr1 p).
    - use Hf₂.
      exact (maponpaths gluing_mor_pr2 p).
  Qed.


  Section Exponentials.
    Context {P₁ : BinProducts C₁}
            {P₂ : BinProducts C₂}
            (E₁ : Exponentials P₁)
            (E₂ : Exponentials P₂)
            (PB₂ : Pullbacks C₂)
            (HF : preserves_binproduct F).

    Section Exp.
      Context (x y : gluing F).

      Let f : exp (E₂ (gluing_pr2 x)) (gluing_pr2 y)
              -->
              exp (E₂ (gluing_pr2 x)) (F (gluing_pr1 y))
        := exp_fun_right E₂ _ (gluing_mor y).

      Let g : F (exp (E₁ (gluing_pr1 x)) (gluing_pr1 y))
              -->
              exp (E₂ (gluing_pr2 x)) (F (gluing_pr1 y))
        := preserves_exponentials_map E₁ E₂ HF (gluing_pr1 x) (gluing_pr1 y)
           · exp_fun_left E₂ (gluing_mor x) _.

      Let P : Pullback f g := PB₂ _ _ _ f g.

      Lemma gluing_pb_sqr_commutes
        : BinProductOfArrows
            C₂ (P₂ _ _) (P₂ _ _)
            (identity _)
            (PullbackPr1 P)
          · exp_eval (E₂ (gluing_pr2 x)) (gluing_pr2 y)
          · gluing_mor y
          =
          BinProductOfArrows
            C₂
            (preserves_binproduct_to_binproduct F HF (P₁ _ _))
            _
            (gluing_mor x)
            (PullbackPr2 P)
          · # F (exp_eval (E₁ (gluing_pr1 x)) (gluing_pr1 y)).
      Proof.
        pose proof (maponpaths
                      (λ z, BinProductOfArrows _ _ (P₂ _ _) (identity _) z · exp_eval _ _)
                      (PullbackSqrCommutes P))
          as p.
        refine (_ @ p @ _) ; clear p.
        - rewrite <- (id_left (identity _)).
          rewrite <- BinProductOfArrows_comp.
          rewrite !assoc'.
          unfold f, exp_fun_right.
          rewrite exp_beta.
          rewrite id_left.
          apply idpath.
        - etrans.
          {
            rewrite <- (id_left (identity _)).
            unfold g.
            rewrite assoc.
            rewrite <- BinProductOfArrows_comp.
            unfold exp_fun_left.
            rewrite !assoc'.
            rewrite exp_beta.
            rewrite !assoc.
            rewrite BinProductOfArrows_comp.
            rewrite id_left, id_right.
            etrans.
            {
              do 2 apply maponpaths_2.
              exact (!(id_right _)).
            }
            rewrite <- BinProductOfArrows_comp.
            rewrite !assoc'.
            unfold preserves_exponentials_map.
            rewrite exp_beta.
            cbn -[gluing_mor].
            unfold BinProductOfArrows.
            rewrite assoc.
            etrans.
            {
              apply maponpaths_2.
              apply (precompWithBinProductArrow _ (preserves_binproduct_to_binproduct F HF _)).
            }
            rewrite BinProductPr1Commutes.
            rewrite BinProductPr2Commutes.
            apply idpath.
          }
          apply idpath.
      Qed.

      Definition gluing_exponential
        : gluing F.
      Proof.
        use make_gluing_ob.
        - exact (exp (E₁ (gluing_pr1 x)) (gluing_pr1 y)).
        - exact P.
        - exact (PullbackPr2 P).
      Defined.

      Proposition gluing_mor_expontial
        : gluing_mor gluing_exponential = PullbackPr2 P.
      Proof.
        apply idpath.
      Qed.

      Definition gluing_eval
        : gluing_binproduct_ob P₁ P₂ HF x gluing_exponential --> y.
      Proof.
        use make_gluing_mor.
        - apply exp_eval.
        - exact (BinProductOfArrows _ (P₂ _ _) _ (identity _) (PullbackPr1 P) · exp_eval _ _).
        - abstract
            (rewrite gluing_mor_binproduct_ob, gluing_mor_expontial ;
             refine (!_) ;
             apply gluing_pb_sqr_commutes).
      Defined.

      Section UMP.
        Context {w : gluing F}
                (φ : gluing_binproduct_ob P₁ P₂ HF x w --> y).

        Lemma gluing_lam_eq
          : exp_lam (E₂ (gluing_pr2 x)) (gluing_mor_pr2 φ) · f
            =
            gluing_mor w · # F (exp_lam (E₁ (gluing_pr1 x)) (gluing_mor_pr1 φ)) · g.
        Proof.
          use exp_funext.
          intros a h.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(id_right _)).
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(id_left _)).
          }
          rewrite <- BinProductOfArrows_comp.
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(id_right _)).
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            exact (!(id_left _)).
          }
          rewrite <- BinProductOfArrows_comp.
          rewrite !assoc'.
          apply maponpaths.
          clear h.
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(id_right _)).
          }
          rewrite <- BinProductOfArrows_comp.
          rewrite !assoc'.
          unfold f, exp_fun_right.
          rewrite exp_beta.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths_2.
              exact (!(id_right _)).
            }
            apply maponpaths.
            exact (!(id_left _)).
          }
          rewrite <- BinProductOfArrows_comp.
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            rewrite assoc.
            rewrite exp_beta.
            exact (!(gluing_mor_eq φ)).
          }
          rewrite gluing_mor_binproduct_ob.
          rewrite !assoc.
          rewrite BinProductOfArrows_id.
          rewrite id_left.
          refine (!_).
          unfold g.
          rewrite !assoc.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(id_right _)).
          }
          rewrite <- BinProductOfArrows_comp.
          rewrite !assoc'.
          unfold exp_fun_left.
          rewrite exp_beta.
          rewrite !assoc.
          rewrite BinProductOfArrows_comp.
          rewrite id_left, id_right.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(id_right _)).
          }
          rewrite <- BinProductOfArrows_comp.
          rewrite !assoc'.
          unfold preserves_exponentials_map.
          rewrite exp_beta.
          cbn -[gluing_mor].
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply (precompWithBinProductArrow _ (preserves_binproduct_to_binproduct F HF _)).
          }
          rewrite BinProductOfArrowsPr1.
          rewrite BinProductOfArrowsPr2.
          etrans.
          {
            do 2 apply maponpaths_2.
            exact (!(id_right _)).
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            exact (BinProductOfArrows_comp'
                     (preserves_binproduct_to_binproduct F HF (P₁ _ _))
                     (preserves_binproduct_to_binproduct F HF _)
                     (P₂ _ _)
                     (gluing_mor x)
                     (gluing_mor w)
                     (identity _)
                     (# F (exp_lam (E₁ _) _))).
          }
          rewrite !assoc'.
          apply maponpaths.
          refine (!_).
          etrans.
          {
            apply maponpaths.
            exact (!(exp_beta (E₁ (gluing_pr1 x)) (gluing_mor_pr1 φ))).
          }
          rewrite functor_comp.
          apply maponpaths_2.
          use (BinProductArrowsEq _ _ _ (preserves_binproduct_to_binproduct F HF _)).
          - refine (_ @ !(BinProductOfArrowsPr1
                            _ _
                            (preserves_binproduct_to_binproduct F HF _)
                            _ _)).
            rewrite id_right.
            cbn.
            rewrite <- functor_comp.
            apply maponpaths.
            refine (BinProductOfArrowsPr1 _ _ (P₁ _ _) _ _ @ _).
            apply id_right.
          - refine (_ @ !(BinProductOfArrowsPr2
                            _ _
                            (preserves_binproduct_to_binproduct F HF _)
                            _ _)).
            cbn.
            rewrite <- !functor_comp.
            apply maponpaths.
            apply BinProductOfArrowsPr2.
        Qed.

        Definition gluing_lam
          : w --> gluing_exponential.
        Proof.
          use make_gluing_mor.
          - exact (exp_lam _ (gluing_mor_pr1 φ)).
          - use PullbackArrow.
            + exact (exp_lam _ (gluing_mor_pr2 φ)).
            + exact (gluing_mor w · #F (exp_lam _ (gluing_mor_pr1 φ))).
            + apply gluing_lam_eq.
          - abstract
              (refine (!_) ;
               apply (PullbackArrow_PullbackPr2 P)).
        Defined.

        Proposition gluing_lam_beta
          : φ
            =
            gluing_binproduct_pair
              P₁ P₂ HF x gluing_exponential
              (gluing_binproduct_pr1 P₁ P₂ HF x _ · identity x)
              (gluing_binproduct_pr2 P₁ P₂ HF x _ · gluing_lam)
            · gluing_eval.
        Proof.
          use eq_gluing_mor.
          - exact (!(exp_beta (E₁ (gluing_pr1 x)) (gluing_mor_pr1 φ))).
          - cbn -[gluing_mor].
            refine (!_).
            rewrite !assoc.
            rewrite postcompWithBinProductArrow.
            rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr1.
            rewrite id_right.
            exact (exp_beta (E₂ (gluing_pr2 x)) (gluing_mor_pr2 φ)).
        Qed.

        Proposition gluing_exp_unique
          : isaprop
              (∑ (g : w --> gluing_exponential),
               φ
               =
               gluing_binproduct_pair P₁ P₂ HF x gluing_exponential
                 (gluing_binproduct_pr1 P₁ P₂ HF x _ · identity x)
                 (gluing_binproduct_pr2 P₁ P₂ HF x _ · g)
               · gluing_eval).
        Proof.
          use invproofirrelevance.
          intros ψ₁ ψ₂.
          use subtypePath.
          {
            intro.
            apply homset_property.
          }
          assert (gluing_mor_pr1 (pr1 ψ₁) = gluing_mor_pr1 (pr1 ψ₂)) as H.
          {
            use exp_funext.
            intros a h.
            rewrite <- (id_right h).
            rewrite <- (id_left (gluing_mor_pr1 (pr1 ψ₁))).
            rewrite <- (id_left (gluing_mor_pr1 (pr1 ψ₂))).
            rewrite <- !BinProductOfArrows_comp.
            rewrite !assoc'.
            apply maponpaths.
            exact (maponpaths gluing_mor_pr1 (!(pr2 ψ₁) @ pr2 ψ₂)).
          }
          use eq_gluing_mor.
          - exact H.
          - use (MorphismsIntoPullbackEqual (isPullback_Pullback P)).
            + use exp_funext.
              intros a h.
              rewrite <- (id_right h).
              rewrite <- (id_left (gluing_mor_pr2 (pr1 ψ₁) · _)).
              rewrite <- (id_left (gluing_mor_pr2 (pr1 ψ₂) · _)).
              rewrite <- !BinProductOfArrows_comp.
              rewrite !assoc'.
              apply maponpaths.
              refine (_ @ maponpaths gluing_mor_pr2 (!(pr2 ψ₁) @ pr2 ψ₂) @ _).
              * cbn.
                rewrite !assoc.
                rewrite postcompWithBinProductArrow.
                rewrite id_right.
                rewrite !assoc'.
                apply idpath.
              * cbn.
                rewrite !assoc.
                rewrite postcompWithBinProductArrow.
                rewrite id_right.
                rewrite !assoc'.
                apply idpath.
            + refine (!(gluing_mor_eq (pr1 ψ₁)) @ _ @ gluing_mor_eq (pr1 ψ₂)).
              do 2 apply maponpaths.
              exact H.
        Qed.
      End UMP.
    End Exp.

    Definition gluing_exponentials
      : Exponentials (gluing_binproducts P₁ P₂ HF).
    Proof.
      intro x.
      use coreflections_to_is_left_adjoint.
      intro y.
      use make_coreflection'.
      - exact (gluing_exponential x y).
      - exact (gluing_eval x y).
      - intros k.
        use iscontraprop1.
        + apply gluing_exp_unique.
        + simple refine (_ ,, _).
          * exact (gluing_lam x y (pr2 k)).
          * apply gluing_lam_beta.
    Defined.

    Proposition preserves_exponentials_gluing_pr1_functor_eq
                (x y : gluing F)
      : identity _
        =
        preserves_exponentials_map
          gluing_exponentials
          E₁
          (preserves_binproduct_gluing_pr1 P₁ P₂ HF)
          x y.
    Proof.
      use exp_funext.
      intros a h.
      rewrite <- (id_right h).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!(id_left _)).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!(id_left _)).
      }
      rewrite <- !BinProductOfArrows_comp.
      rewrite !assoc'.
      apply maponpaths.
      unfold preserves_exponentials_map.
      rewrite exp_beta.
      apply maponpaths_2.
      cbn.
      unfold precomp_with.
      rewrite id_right.
      use BinProductArrowsEq.
      - rewrite !assoc'.
        rewrite !BinProductPr1Commutes.
        rewrite BinProductOfArrowsPr1.
        rewrite id_right.
        apply idpath.
      - rewrite !assoc'.
        rewrite !BinProductPr2Commutes.
        rewrite BinProductOfArrowsPr2.
        rewrite id_right.
        apply idpath.
    Qed.

    Definition preserves_exponentials_gluing_pr1_functor
      : preserves_exponentials
          gluing_exponentials
          E₁
          (preserves_binproduct_gluing_pr1 P₁ P₂ HF).
    Proof.
      intros x y.
      use is_z_isomorphism_path.
      - apply identity.
      - apply preserves_exponentials_gluing_pr1_functor_eq.
      - apply is_z_isomorphism_identity.
    Defined.
  End Exponentials.



  Section SubobjectClassifier.
    Context {T₁ : Terminal C₁}
            (Ω₁ : subobject_classifier T₁)
            {T₂ : Terminal C₂}
            (Ω₂ : subobject_classifier T₂)
            {P₁ : BinProducts C₁}
            {P₂ : BinProducts C₂}
            (PB₁ : Pullbacks C₁)
            (PB₂ : Pullbacks C₂)
            (HF₁ : preserves_terminal F)
            (HF₂ : preserves_pullback F).

    Let f : Monic _ Ω₂ (P₂ Ω₂ Ω₂) := diagonalMap _ _.
    Let g : P₂ Ω₂ (F Ω₁) --> P₂ Ω₂ Ω₂
      := BinProductOfArrows
           _ _ _
           (identity _)
           (functor_subobject_classifier_mor Ω₁ Ω₂ HF₁).
    Let P : Pullback f g := PB₂ _ _ _ f g.

    Definition gluing_subobject_classifier_ob
      : gluing F.
    Proof.
      use make_gluing_ob.
      - exact Ω₁.
      - exact P.
      - exact (PullbackPr2 _ · BinProductPr2 _ _).
    Defined.

    Lemma gluing_subobject_classifier_truth_eq
      : true Ω₂ · f
        =
        BinProductArrow
          _ _
          (true Ω₂)
          (inv_from_z_iso (preserves_terminal_to_z_iso F HF₁ T₁ T₂) · # F Ω₁)
        · g.
    Proof.
      use BinProductArrowsEq.
      - cbn.
        rewrite !assoc'.
        unfold diagonalMap', g.
        rewrite BinProductOfArrowsPr1.
        rewrite id_right.
        rewrite !BinProductPr1Commutes.
        rewrite id_right.
        apply idpath.
      - cbn.
        rewrite !assoc'.
        unfold diagonalMap', g.
        rewrite BinProductOfArrowsPr2.
        rewrite BinProductPr2Commutes.
        rewrite assoc.
        rewrite BinProductPr2Commutes.
        rewrite id_right.
        unfold functor_subobject_classifier_mor.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply functor_subobject_classifier_mor_comm'.
        }
        refine (_ @ id_left _).
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
    Qed.

    Definition gluing_subobject_classifier_truth
      : gluing_terminal T₁ T₂ HF₁ --> gluing_subobject_classifier_ob.
    Proof.
      use make_gluing_mor.
      - exact (true' Ω₁).
      - use PullbackArrow.
        + exact (true Ω₂).
        + use BinProductArrow.
          * exact (true Ω₂).
          * exact (inv_from_z_iso (preserves_terminal_to_z_iso F HF₁ T₁ T₂) · #F Ω₁).
        + apply gluing_subobject_classifier_truth_eq.
      - abstract
          (cbn ;
           rewrite !assoc ;
           rewrite PullbackArrow_PullbackPr2 ;
           rewrite BinProductPr2Commutes ;
           apply idpath).
    Defined.

    Section UMP.
      Context {x y : gluing F}
              (m : Monic (gluing F) x y).

      Let χ₁ : gluing_pr1 y --> gluing_pr1 gluing_subobject_classifier_ob
        := characteristic_morphism _ (gluing_pr1_monic PB₁ PB₂ HF₂ m).
      Let χ₂ : gluing_pr2 y --> Ω₂
        := characteristic_morphism _ (gluing_pr2_monic PB₁ PB₂ HF₂ m).

      Lemma gluing_subobject_classifier_characteristic_eq
        : χ₂ · f = BinProductArrow C₂ (P₂ Ω₂ (F Ω₁)) χ₂ (gluing_mor y · # F χ₁) · g.
      Proof.
        cbn -[gluing_mor] ; unfold g, diagonalMap'.
        use BinProductArrowsEq.
        - rewrite !assoc'.
          rewrite BinProductPr1Commutes.
          rewrite BinProductOfArrowsPr1.
          rewrite !id_right.
          rewrite BinProductPr1Commutes.
          apply idpath.
        - rewrite !assoc'.
          rewrite BinProductPr2Commutes.
          rewrite BinProductOfArrowsPr2.
          rewrite !assoc.
          rewrite id_right.
          rewrite BinProductPr2Commutes.
          unfold functor_subobject_classifier_mor.
          simple refine (_ @ !(characteristic_morphism_precomp PB₂ _ _ _)).
          (*
          Check gluing_mor y.
          pose (# F χ₁).
          cbn in p.
          pose (subobject_classifier_pullback
                    Ω₂
                    (gluing_pr2_monic PB₁ PB₂ HF₂ m))
            as P'.
          pose (PullbackObject P').
          Check gluing_mor_eq m.
           *)
          use characteristic_morphism_eq ; clear χ₂.
          + pose (subobject_classifier_pullback
                    Ω₂
                    (gluing_pr2_monic PB₁ PB₂ HF₂ m))
              as P'.
            use make_z_iso.
            * use PullbackArrow.
              ** exact (gluing_mor_pr2 m).
              ** apply TerminalArrow.
              ** abstract
                  (rewrite !assoc ;
                   refine (maponpaths (λ z, z · _) (!(gluing_mor_eq m)) @ _) ;
                   rewrite !assoc' ;
                   rewrite <- functor_comp ;
                   refine (maponpaths
                             (λ z, _ · #F z)
                             (subobject_classifier_square_commutes
                                Ω₁
                                (gluing_pr1_monic PB₁ PB₂ HF₂ m))
                           @ _) ;
                   rewrite functor_comp ;
                   cbn ;
                   rewrite !assoc ;
                   apply maponpaths_2 ;
                   apply (TerminalArrowEq (T := preserves_terminal_to_terminal F HF₁ T₁))).
            * use (PullbackArrow P').
              ** exact (PullbackPr1 _).
              ** apply TerminalArrow.
              ** Check (MonicisMonic _ m _).
                 pose (subobject_classifier_square_commutes
                         Ω₁
                         (gluing_pr1_monic PB₁ PB₂ HF₂ m))
                   as p.
                 pose (PullbackSqrCommutes
                         ((PB₂ (F Ω₁) (pr11 y) T₂ (gluing_mor y · # F χ₁)
                             (functor_subobject_classifier_mor_monic Ω₁ Ω₂ HF₁))))
                   as q.
                 pose (gluing_mor_eq m) as r.
                 simpl in p, q, r.
                 admit.
            * split.
              ** use (MorphismsIntoPullbackEqual (isPullback_Pullback P')).
                 *** rewrite !assoc'.
                     rewrite (PullbackArrow_PullbackPr1 P').
                     rewrite PullbackArrow_PullbackPr1.
                     rewrite id_left.
                     apply idpath.
                 *** apply TerminalArrowEq.
              ** use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
                 *** rewrite !assoc'.
                     rewrite PullbackArrow_PullbackPr1.
                     rewrite (PullbackArrow_PullbackPr1 P').
                     rewrite id_left.
                     apply idpath.
                 *** apply TerminalArrowEq.
          + cbn.
            rewrite PullbackArrow_PullbackPr1.
            apply idpath.
      Admitted.
       *)

      Definition gluing_subobject_classifier_characteristic
        : y --> gluing_subobject_classifier_ob.
      Proof.
        use make_gluing_mor.
        - exact χ₁.
        - use PullbackArrow.
          + exact χ₂.
          + exact (BinProductArrow _ _ χ₂ (gluing_mor y · #F χ₁)).
          + exact gluing_subobject_classifier_characteristic_eq.
        - abstract
            (cbn ;
             rewrite !assoc ;
             rewrite PullbackArrow_PullbackPr2 ;
             rewrite BinProductPr2Commutes ;
             apply idpath).
      Defined.

      Proposition gluing_subobject_classifier_characteristic_comm
        : m · gluing_subobject_classifier_characteristic
          =
          TerminalArrow (gluing_terminal T₁ T₂ HF₁) x
          · gluing_subobject_classifier_truth.
      Proof.
        use eq_gluing_mor.
        - exact (subobject_classifier_square_commutes
                   Ω₁
                   (gluing_pr1_monic PB₁ PB₂ HF₂ m)).
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)) ; cbn -[gluing_mor].
          + rewrite !assoc'.
            rewrite !PullbackArrow_PullbackPr1.
            exact (subobject_classifier_square_commutes
                     Ω₂
                     (gluing_pr2_monic PB₁ PB₂ HF₂ m)).
          + rewrite !assoc'.
            rewrite !PullbackArrow_PullbackPr2.
            use BinProductArrowsEq.
            * rewrite !assoc'.
              rewrite !BinProductPr1Commutes.
              exact (subobject_classifier_square_commutes
                       Ω₂
                       (gluing_pr2_monic PB₁ PB₂ HF₂ m)).
            * rewrite !assoc'.
              rewrite !BinProductPr2Commutes.
              rewrite !assoc.
              etrans.
              {
                apply maponpaths_2.
                exact (!(gluing_mor_eq m)).
              }
              rewrite !assoc'.
              rewrite <- functor_comp.
              etrans.
              {
                do 2 apply maponpaths.
                exact (subobject_classifier_square_commutes
                         Ω₁
                         (gluing_pr1_monic PB₁ PB₂ HF₂ m)).
              }
              rewrite functor_comp.
              rewrite !assoc.
              apply maponpaths_2.
              apply (TerminalArrowEq
                       (T := preserves_terminal_to_terminal F HF₁ T₁)).
      Qed.

      Proposition gluing_subobject_classifier_unique
        : isaprop
            (∑ (chi : y --> gluing_subobject_classifier_ob)
               (H : m · chi
                    =
                    TerminalArrow (gluing_terminal T₁ T₂ HF₁) x
                    · gluing_subobject_classifier_truth),
             isPullback H).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          use isaproptotal2.
          {
            intro.
            apply isaprop_isPullback.
          }
          intros.
          apply homset_property.
        }
        assert (H₁ : gluing_mor_pr1 (pr1 φ₁) = gluing_mor_pr1 (pr1 φ₂)).
        {
          use (subobject_classifier_map_eq Ω₁ (gluing_pr1_monic PB₁ PB₂ HF₂ m)).
          - exact (maponpaths gluing_mor_pr1 (pr12 φ₁)).
          - exact (maponpaths gluing_mor_pr1 (pr12 φ₂)).
          - exact (preserves_pullback_gluing_pr1 PB₁ PB₂ HF₂ _ _ _ _ _ _ _ _ _ _(pr22 φ₁)).
          - exact (preserves_pullback_gluing_pr1 PB₁ PB₂ HF₂ _ _ _ _ _ _ _ _ _ _(pr22 φ₂)).
        }
        assert (PullbackPr2 P · BinProductPr1 C₂ (P₂ Ω₂ (F Ω₁)) = PullbackPr1 P)
          as H₂.
        {
          refine (!_).
          refine (_ @ maponpaths (λ z, z · BinProductPr1 _ _) (PullbackSqrCommutes P) @ _).
          - cbn.
            unfold diagonalMap'.
            rewrite !assoc'.
            rewrite BinProductPr1Commutes.
            rewrite id_right.
            apply idpath.
          - unfold g.
            rewrite !assoc'.
            rewrite BinProductOfArrowsPr1.
            rewrite id_right.
            apply idpath.
        }
        assert (gluing_mor_pr2 (pr1 φ₁) · PullbackPr1 P
                =
                gluing_mor_pr2 (pr1 φ₂) · PullbackPr1 P)
          as H₃.
        {
          use (subobject_classifier_map_eq Ω₂ (gluing_pr2_monic PB₁ PB₂ HF₂ m)).
          - cbn.
            rewrite !assoc.
            refine (maponpaths (λ z, z · _) (maponpaths gluing_mor_pr2 (pr12 φ₁)) @ _).
            cbn.
            rewrite !assoc'.
            rewrite PullbackArrow_PullbackPr1.
            apply idpath.
          - admit.
          - admit.
          - admit.
        }
        use eq_gluing_mor.
        - exact H₁.
        - use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          + exact H₃.
          + use BinProductArrowsEq.
            * rewrite !assoc'.
              rewrite !H₂.
              exact H₃.
            * rewrite !assoc'.
              refine (!(gluing_mor_eq (pr1 φ₁)) @ _ @ gluing_mor_eq (pr1 φ₂)).
              do 2 apply maponpaths.
              exact H₁.
      Admitted.
    End UMP.

    Definition gluing_subobject_classifier
      : subobject_classifier (gluing_terminal T₁ T₂ HF₁).
    Proof.
      use make_subobject_classifier.
      - exact gluing_subobject_classifier_ob.
      - exact gluing_subobject_classifier_truth.
      - intros x y m.
        use iscontraprop1.
        + apply gluing_subobject_classifier_unique.
        + simple refine (_ ,, _ ,, _).
          * exact (gluing_subobject_classifier_characteristic m).
          * exact (gluing_subobject_classifier_characteristic_comm m).
          * admit.
    Admitted.






    asdfadfadfadfasdfadf


    (*(HF₃ : preserves_pullback F).*)

    Let i : z_iso (F Ω₁) Ω₂ := preserves_subobject_classifier_z_iso HF₂ Ω₁ Ω₂.
    Let FT : Terminal C₂
      := preserves_terminal_to_terminal F HF₁ T₁.
    Let FΩ : subobject_classifier T₂
      := preserves_subobject_classifier_on_ob HF₂ Ω₁.

    Definition gluing_subobject_classifier_ob
      : gluing F.
    Proof.
      use make_gluing_ob.
      - exact Ω₁.
      - exact Ω₂.
      - exact (inv_from_z_iso i).
    Defined.

    Definition gluing_subobject_classifier_truth
      : gluing_terminal T₁ T₂ HF₁ --> gluing_subobject_classifier_ob.
    Proof.
      use make_gluing_mor.
      - exact (true' Ω₁).
      - exact (true' Ω₂).
      - abstract
          (cbn ;
           unfold mor_subobject_classifier ;
           refine (!_) ;
           refine (subobject_classifier_square_commutes FΩ Ω₂ @ _) ;
           cbn ;
           rewrite assoc ;
           apply maponpaths_2 ;
           apply (TerminalArrowEq (T := FT))).
    Defined.

    Section UMP.
      Context {x y : gluing F}
              (m : Monic (gluing F) x y).

      Lemma gluing_subobject_classifier_characteristic_help_eq
        : gluing_mor y
          · #F (characteristic_morphism Ω₁ (gluing_pr1_monic PB₁ PB₂ HF₃ m))
          =
          characteristic_morphism Ω₂ (gluing_pr2_monic PB₁ PB₂ HF₃ m)
          · gluing_mor gluing_subobject_classifier_ob.
      Proof.
        pose (PB := subobject_classifier_pullback Ω₂ (gluing_pr2_monic PB₁ PB₂ HF₃ m)).
        use (subobject_classifier_map_eq FΩ).
        - exact (gluing_pr2 x).
        - exact (gluing_pr2_monic PB₁ PB₂ HF₃ m).
        - abstract
            (simpl ;
             rewrite !assoc ;
             refine (maponpaths (λ z, z · _) (!(gluing_mor_eq m)) @ _) ;
             rewrite !assoc' ;
             rewrite <- functor_comp ;
             rewrite (subobject_classifier_square_commutes
                        _
                        (gluing_pr1_monic PB₁ PB₂ HF₃ m)) ;
             rewrite functor_comp ;
             unfold const_true, FΩ ; simpl ;
             unfold true' ; simpl ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply (TerminalArrowEq (T := FT))).
        - abstract
            (rewrite !assoc ;
             rewrite subobject_classifier_square_commutes ;
             unfold const_true ; cbn ;
             rewrite assoc' ;
             apply maponpaths ;
             unfold mor_subobject_classifier ;
             refine (subobject_classifier_square_commutes FΩ Ω₂ @ _) ;
             unfold const_true, FΩ ; simpl ;
             unfold true' ; simpl ;
             rewrite !assoc ;
             apply maponpaths_2 ;
             apply (TerminalArrowEq (T := FT))).
        - intros w h k p.
          use iscontraprop1.
          + use invproofirrelevance.
            intros φ₁ φ₂.
            use subtypePath.
            {
              intro.
              apply isapropdirprod ; apply homset_property.
            }
            use (MorphismsIntoPullbackEqual (isPullback_Pullback PB)).
            * exact (pr12 φ₁ @ !(pr12 φ₂)).
            * exact (pr22 φ₁ @ !(pr22 φ₂)).
          + simple refine (_ ,, _ ,, _) ; [ | | apply TerminalArrowEq ].
            * use (PullbackArrow PB _ h k).
              cbn -[gluing_mor] in p.
              refine (_ @ maponpaths (λ z, z · i) p @ _).
              ** rewrite assoc'.
                 cbn -[gluing_mor].
                 unfold mor_subobject_classifier.
                 admit.
              ** cbn.
                 unfold mor_subobject_classifier.
                 rewrite !assoc'.
                 apply maponpaths.
                 rewrite assoc.
                 etrans.
                 {
                   exact (subobject_classifier_square_commutes
                            Ω₂
                            (preserves_subobject_classifier_on_ob HF₂ Ω₁)).
                 }
                 refine (_ @ id_left _).
                 apply maponpaths_2.
                 apply TerminalArrowEq.
            * apply (PullbackArrow_PullbackPr1 PB).
        - intros w h k p.
          use iscontraprop1.
          + use invproofirrelevance.
            intros φ₁ φ₂.
            use subtypePath.
            {
              intro.
              apply isapropdirprod ; apply homset_property.
            }
            use (MorphismsIntoPullbackEqual (isPullback_Pullback PB)).
            * exact (pr12 φ₁ @ !(pr12 φ₂)).
            * exact (pr22 φ₁ @ !(pr22 φ₂)).
          + simple refine (_ ,, _ ,, _) ; [ | | apply TerminalArrowEq ].
            * use (PullbackArrow PB _ h k).
              cbn in p.
              cbn -[gluing_mor] in p.
              cbn in p.
              admit.
            * apply (PullbackArrow_PullbackPr1 PB).
      Admitted.

      Definition gluing_subobject_classifier_characteristic
        : y --> gluing_subobject_classifier_ob.
      Proof.
        use make_gluing_mor.
        - use characteristic_morphism.
          + exact (gluing_pr1 x).
          + exact (gluing_pr1_monic PB₁ PB₂ HF₃ m).
        - use characteristic_morphism.
          + exact (gluing_pr2 x).
          + exact (gluing_pr2_monic PB₁ PB₂ HF₃ m).
        - exact gluing_subobject_classifier_characteristic_help_eq.
      Defined.

      Proposition gluing_subobject_classifier_characteristic_comm
        : m · gluing_subobject_classifier_characteristic
          =
          TerminalArrow (gluing_terminal T₁ T₂ HF₁) x
          · gluing_subobject_classifier_truth.
      Proof.
        use eq_gluing_mor.
        - exact (subobject_classifier_square_commutes
                   Ω₁
                   (gluing_pr1_monic PB₁ PB₂ HF₃ m)).
        - exact (subobject_classifier_square_commutes
                   Ω₂
                   (gluing_pr2_monic PB₁ PB₂ HF₃ m)).
      Qed.

      Proposition gluing_subobject_classifier_unique
        : isaprop
            (∑ (chi : y --> gluing_subobject_classifier_ob)
               (H : m · chi
                    =
                    TerminalArrow _ x · gluing_subobject_classifier_truth),
             isPullback H).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
      Admitted.
    End UMP.

    Definition gluing_subobject_classifier
      : subobject_classifier (gluing_terminal T₁ T₂ HF₁).
    Proof.
      use make_subobject_classifier.
      - exact gluing_subobject_classifier_ob.
      - exact gluing_subobject_classifier_truth.
      - intros x y m.
        use iscontraprop1.
        + exact (gluing_subobject_classifier_unique m).
        + simple refine (_ ,, _ ,, _).
          * exact (gluing_subobject_classifier_characteristic m).
          * exact (gluing_subobject_classifier_characteristic_comm m).
          *
