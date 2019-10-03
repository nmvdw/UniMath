(** Each 2-category gives rise to a strict bicategory *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.TwoCategories. Import TwoCategories.Notations.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.CategoryEquality.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Strictness.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

Section TwoCatToBicat.
  Variable (C : two_cat).

  Definition two_cat_to_bicat_data
    : prebicat_data.
  Proof.
    use build_prebicat_data.
    - exact (pr1 C).
    - exact (λ x y, x --> y).
    - exact (λ x y f g, f ==> g).
    - exact (λ x, id₁ x).
    - exact (λ _ _ _ f g, f · g).
    - exact (λ _ _ f, id₂ f).
    - exact (λ _ _ _ _ _ x y, x • y).
    - exact (λ _ _ _ f _ _ x, f ◃ x).
    - exact (λ _ _ _ _ _ f x, x ▹ f).
    - exact (@two_cat_lunitor (pr1 C)).
    - exact (@two_cat_linvunitor (pr1 C)).
    - exact (@two_cat_runitor (pr1 C)).
    - exact (@two_cat_rinvunitor (pr1 C)).
    - exact (@two_cat_lassociator (pr1 C)).
    - exact (@two_cat_rassociator (pr1 C)).
  Defined.

  Definition two_cat_to_bicat_laws : prebicat_laws two_cat_to_bicat_data.
  Proof.
    repeat split; cbn
    ; try (intros ; apply (pr21 C)).
    - intros ; apply two_cat_vcomp_lunitor.
    - intros ; apply two_cat_vcomp_runitor.
    - intros ; apply two_cat_lwhisker_lwhisker.
    - intros ; apply two_cat_rwhisker_lwhisker.
    - intros ; apply two_cat_rwhisker_rwhisker.
    - intros ; apply two_cat_lunitor_linvunitor.
    - intros ; apply two_cat_linvunitor_lunitor.
    - intros ; apply two_cat_runitor_rinvunitor.
    - intros ; apply two_cat_rinvunitor_runitor.
    - intros ; apply two_cat_lassociator_rassociator.
    - intros ; apply two_cat_rassociator_lassociator.
    - intros ; apply two_cat_runitor_rwhisker.
    - intros ; apply two_cat_lassociator_lassociator.
  Qed.

  Definition two_cat_to_prebicat : prebicat := _ ,, two_cat_to_bicat_laws.

  Lemma isaset_cells_two_cat_to_prebicat : isaset_cells two_cat_to_prebicat.
  Proof.
    intros a b f g.
    apply C.
  Qed.

  Definition two_cat_to_bicat : bicat
    := (two_cat_to_prebicat,, isaset_cells_two_cat_to_prebicat).

  Definition two_cat_to_bicat_strictness_structure
    : strictness_structure two_cat_to_bicat.
  Proof.
    repeat use tpair.
    - intros ; apply id_left.
    - intros ; apply id_right.
    - simpl ; intros ; apply assoc.
    - simpl.
      intros a b f.
      cbn ; unfold two_cat_lunitor.
      induction (id_left f).
      apply idpath.
    - simpl.
      intros a b f.
      cbn ; unfold two_cat_runitor.
      induction (id_right f).
      apply idpath.
    - simpl.
      intros a b c d f g h.
      cbn ; unfold two_cat_lassociator.
      induction (assoc f g h).
      apply idpath.
  Qed.

  Definition is_strict_two_cat_to_bicat
    : is_strict_bicat two_cat_to_bicat.
  Proof.
    use make_is_strict_bicat.
    - intros ? ?.
      apply (pr111 C).
    - exact two_cat_to_bicat_strictness_structure.
  Defined.
End TwoCatToBicat.
