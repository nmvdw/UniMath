(**********************************************************************************

 Double functors between double categories of structured cospans

 Suppose that we have the following square of functors:

          L₁
       A₁ ⟶ X₁
    FA |      | FX
       V      V
       A₂ ⟶ X₂
          L₂

 and suppose that we have a natural isomorphism from `FA ∙ L₂` to `L₁ ∙ FX`. Then
 we have a double functor from the double category of `L₁`-structured cospans to
 the double category of `L₂`-structured cospans. The description on this double
 functor on the vertical categories is given by `FA`. A structured cospan
 `L₁ a <-- x --> L₁ b` is sent to `L₂ (FA a) <-- FX x --> L₂ (FA b)`.

 A part of this construction is already given in the file `StructuredCospans.v`.
 In that file the action of this double functor on objects, horizontal morphisms,
 and on squares is defined. In this file, we show that this gives rise to a double
 functor.

 A reference for this construction is Theorem 4.2 in "Structured Cospans" by Baez,
 and Courser.
    https://arxiv.org/pdf/1911.04630.pdf
 Note that in their version of the theorem, one of the functors is required to
 preserve pushouts. However, our construction does not need this assumption.

 Contents
 1. Preservation of horizontal identities
 2. Preservation of horizontal composition
 3. The coherences
 4. The double functors between the double categories of structured cospans

 **********************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.StructuredCospans.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleFunctor.Basics.
Require Import UniMath.Bicategories.DoubleCategories.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Examples.StructuredCospansDoubleCat.

Local Open Scope cat.

Section StructuredCospansDoubleFunctor.
  Context {A₁ A₂ X₁ X₂ : univalent_category}
          (PX₁ : Pushouts X₁)
          (PX₂ : Pushouts X₂)
          {L₁ : A₁ ⟶ X₁}
          {L₂ : A₂ ⟶ X₂}
          {FA : A₁ ⟶ A₂}
          {FX : X₁ ⟶ X₂}
          (α : nat_z_iso (FA ∙ L₂) (L₁ ∙ FX)).

  (**
   1. Preservation of horizontal identities
   *)
  Definition structured_cospans_double_cat_functor_id_data
    : double_functor_hor_id_data
        (twosided_disp_cat_of_struct_cospans_functor α)
        (structured_cospans_double_cat_hor_id L₁)
        (structured_cospans_double_cat_hor_id L₂).
  Proof.
    intro x.
    use make_struct_cospan_sqr.
    - exact (α x).
    - abstract
        (split ; cbn ;
         rewrite !functor_id, !id_left, id_right ;
         apply idpath).
  Defined.

  Proposition structured_cospans_double_cat_functor_id_laws
    : double_functor_hor_id_laws
        structured_cospans_double_cat_functor_id_data.
  Proof.
    intros x y f.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    apply (nat_trans_ax α _ _ f).
  Qed.

  Definition structured_cospans_double_cat_functor_id
    : double_functor_hor_id
        (twosided_disp_cat_of_struct_cospans_functor α)
        (structured_cospans_double_cat_hor_id L₁)
        (structured_cospans_double_cat_hor_id L₂).
  Proof.
    use make_double_functor_hor_id.
    - exact structured_cospans_double_cat_functor_id_data.
    - exact structured_cospans_double_cat_functor_id_laws.
  Defined.

  (**
   2. Preservation of horizontal composition
   *)
  Definition structured_cospans_double_cat_functor_comp_data
    : double_functor_hor_comp_data
        (twosided_disp_cat_of_struct_cospans_functor α)
        (structured_cospans_double_cat_hor_comp PX₁ L₁)
        (structured_cospans_double_cat_hor_comp PX₂ L₂).
  Proof.
    intros x y z h k.
    use make_struct_cospan_sqr.
    - use PushoutArrow ; cbn.
      + exact (#FX (PushoutIn1 _)).
      + exact (#FX (PushoutIn2 _)).
      + abstract
          (rewrite !assoc' ;
           apply maponpaths ;
           rewrite <- !functor_comp ;
           apply maponpaths ;
           apply PushoutSqrCommutes).
    - abstract
        (split ;
         [ cbn ;
           rewrite !assoc' ;
           rewrite functor_id, id_left ;
           rewrite PushoutArrow_PushoutIn1 ;
           rewrite <- !functor_comp ;
           apply idpath
         | cbn ;
           rewrite !assoc' ;
           rewrite functor_id, id_left ;
           rewrite PushoutArrow_PushoutIn2 ;
           rewrite <- !functor_comp ;
           apply idpath ]).
  Defined.

  Proposition structured_cospans_double_cat_functor_comp_laws
    : double_functor_hor_comp_laws
        structured_cospans_double_cat_functor_comp_data.
  Proof.
    intro ; intros.
    use struct_cospan_sqr_eq.
    rewrite transportb_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX₂ _ _ _ _ _))) ; cbn.
    - unfold mor_of_comp_struct_cospan_mor.
      rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn1.
      cbn.
      rewrite <- !functor_comp.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite <- !functor_comp.
      apply idpath.
    - unfold mor_of_comp_struct_cospan_mor.
      rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn2.
      cbn.
      rewrite <- !functor_comp.
      rewrite !PushoutArrow_PushoutIn2.
      rewrite !assoc'.
      rewrite !PushoutArrow_PushoutIn2.
      rewrite <- !functor_comp.
      apply idpath.
  Qed.

  Definition structured_cospans_double_cat_functor_comp
    : double_functor_hor_comp
        (twosided_disp_cat_of_struct_cospans_functor α)
        (structured_cospans_double_cat_hor_comp PX₁ L₁)
        (structured_cospans_double_cat_hor_comp PX₂ L₂).
  Proof.
    use make_double_functor_hor_comp.
    - exact structured_cospans_double_cat_functor_comp_data.
    - exact structured_cospans_double_cat_functor_comp_laws.
  Defined.

  (**
   3. The coherences
   *)
  Proposition structured_cospans_double_cat_functor_lunitor
    : double_functor_lunitor
        (structured_cospans_double_cat_lunitor PX₁ L₁)
        (structured_cospans_double_cat_lunitor PX₂ L₂)
        structured_cospans_double_cat_functor_id
        structured_cospans_double_cat_functor_comp.
  Proof.
    intros x y f.
    use struct_cospan_sqr_eq.
    rewrite transportf_disp_mor2_struct_cospan ; cbn.
    unfold struct_cospan_lunitor_mor, mor_of_comp_struct_cospan_mor.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX₂ _ _ _ _ _))) ; cbn.
    - rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite PushoutArrow_PushoutIn1.
      rewrite <- functor_comp.
      rewrite PushoutArrow_PushoutIn1.
      apply idpath.
    - rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn2.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite PushoutArrow_PushoutIn2.
      rewrite <- functor_comp.
      rewrite PushoutArrow_PushoutIn2.
      rewrite functor_id.
      rewrite id_left.
      apply idpath.
  Qed.

  Proposition structured_cospans_double_cat_functor_runitor
    : double_functor_runitor
        (structured_cospans_double_cat_runitor PX₁ L₁)
        (structured_cospans_double_cat_runitor PX₂ L₂)
        structured_cospans_double_cat_functor_id
        structured_cospans_double_cat_functor_comp.
  Proof.
    intros x y f.
    use struct_cospan_sqr_eq.
    rewrite transportf_disp_mor2_struct_cospan ; cbn.
    unfold struct_cospan_runitor_mor, mor_of_comp_struct_cospan_mor.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX₂ _ _ _ _ _))) ; cbn.
    - rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn1.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite PushoutArrow_PushoutIn1.
      rewrite <- functor_comp.
      rewrite PushoutArrow_PushoutIn1.
      rewrite functor_id, id_left.
      apply idpath.
    - rewrite !assoc.
      rewrite !PushoutArrow_PushoutIn2.
      rewrite !assoc'.
      rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite PushoutArrow_PushoutIn2.
      rewrite <- functor_comp.
      rewrite PushoutArrow_PushoutIn2.
      apply idpath.
  Qed.

  Proposition structured_cospans_double_cat_functor_associator
    : double_functor_associator
        (structured_cospans_double_cat_associator PX₁ L₁)
        (structured_cospans_double_cat_associator PX₂ L₂)
        structured_cospans_double_cat_functor_comp.
  Proof.
    intro ; intros.
    use struct_cospan_sqr_eq.
    rewrite transportf_disp_mor2_struct_cospan ; cbn.
    use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX₂ _ _ _ _ _))) ; cbn.
    - refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn1.
      }
      do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn1.
      }
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn1.
      }
      refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        apply PushoutArrow_PushoutIn1.
      }
      refine (!_).
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn1.
      }
      do 2 refine (assoc' _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn1.
      }
      etrans.
      {
        apply maponpaths.
        refine (!(functor_comp _ _ _) @ _).
        apply maponpaths.
        apply PushoutArrow_PushoutIn1.
      }
      refine (_ @ functor_comp _ _ _).
      refine (_ @ id_left _).
      apply maponpaths_2 ; cbn.
      apply idpath.
    - refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn2.
      }
      refine (!_).
      refine (assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (assoc _ _ _ @ _).
        apply maponpaths_2.
        apply PushoutArrow_PushoutIn2.
      }
      use (MorphismsOutofPushoutEqual (isPushout_Pushout (PX₂ _ _ _ _ _))) ; cbn.
      + refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn1.
        }
        do 2 refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn2.
        }
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp _ _ _) @ _).
          apply maponpaths.
          apply PushoutArrow_PushoutIn2.
        }
        etrans.
        {
          refine (!(functor_comp _ _ _) @ _).
          apply maponpaths.
          apply PushoutArrow_PushoutIn1.
        }
        refine (!_).
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn1.
        }
        do 2 refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn1.
        }
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn2.
        }
        refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply PushoutArrow_PushoutIn1.
        }
        exact (!(functor_comp _ _ _)).
      + refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn2.
        }
        do 2 refine (assoc' _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn2.
        }
        etrans.
        {
          apply maponpaths.
          refine (!(functor_comp _ _ _) @ _).
          apply maponpaths.
          apply PushoutArrow_PushoutIn2.
        }
        etrans.
        {
          refine (!(functor_comp _ _ _) @ _).
          apply maponpaths.
          apply PushoutArrow_PushoutIn2.
        }
        refine (!_).
        refine (assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn2.
        }
        etrans.
        {
          apply maponpaths_2.
          apply PushoutArrow_PushoutIn2.
        }
        refine (assoc' _ _ _ @ _).
        refine (id_left _ @ _).
        apply PushoutArrow_PushoutIn2.
  Qed.

  (**
   4. The double functors between the double categories of structured cospans
   *)
  Definition structured_cospans_double_cat_functor
    : lax_double_functor
        (structured_cospans_double_cat PX₁ L₁)
        (structured_cospans_double_cat PX₂ L₂).
  Proof.
    use make_lax_double_functor.
    - exact FA.
    - exact (twosided_disp_cat_of_struct_cospans_functor α).
    - exact structured_cospans_double_cat_functor_id.
    - exact structured_cospans_double_cat_functor_comp.
    - exact structured_cospans_double_cat_functor_lunitor.
    - exact structured_cospans_double_cat_functor_runitor.
    - exact structured_cospans_double_cat_functor_associator.
  Defined.
End StructuredCospansDoubleFunctor.
