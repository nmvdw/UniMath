(*
In this file, we show how the Rezk completion of a category has a suitable terminal object (in terms of preservation) if the original category has a terminal object.
Hence, categories with terminal objects admit a Rezk completion.

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Preservation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Reflection.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.Creation.Pullbacks.
Require Import UniMath.CategoryTheory.WeakEquivalences.LiftPreservation.Pullbacks.

Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.Core.Univalence.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.UniversalArrow.
Import PseudoFunctor.Notations.

Import DispBicat.Notations.

Require Import UniMath.Bicategories.PseudoFunctors.Examples.BicatOfCatToUnivCat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOnCatToUniv.

Require Import UniMath.Bicategories.DisplayedBicats.UniversalArrows.core.
Require Import UniMath.Bicategories.DisplayedBicats.UniversalArrows.OverCat.FromWeakEquivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.Terminal.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.ProductsBin.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.Pullbacks.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FinitelyComplete.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.SubObjectClassifier.
Require Import UniMath.Bicategories.DisplayedBicats.UniversalArrows.OverCat.SigmaConstruction.
Require Import UniMath.Bicategories.DisplayedBicats.UniversalArrows.OverCat.ToProduct.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.FiniteLimits.

Local Open Scope cat.

Section CategoriesWithSubobjectclassifiersAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Definition lexcat_has_Rezk_completions
    : disp_left_universal_arrow LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_lex
           (disp_2cells_isaprop_from_disp_2cells_iscontr disp_bicat_lex disp_2cells_is_contr_lex)).
  Proof.
    exact (cat_with_finlimits_has_RezkCompletion' LUR η_weak_equiv).
  Defined.

  Let R_Ω := (disp_psfunctor_on_cat_to_univ_cat disp_bicat_subobjectclassifier
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_subobjectclassifier)).

  Definition catswithsubobjectclassifier_has_Rezk_completions
    : disp_left_universal_arrow LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_subobjectclassifier
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_subobjectclassifier)).
  Proof.
    (* use make_disp_left_universal_arrow_if_contr_CAT.*)

    Print disp_bicat_subobjectclassifier.
    (* D : disp_bicat CAT, D_univ*)

    Check @make_disp_left_universal_arrow_if_contr_CAT_on_sigma LUR disp_bicat_lex disp_bicat_subobjectclassifier_over_lex _ _ lexcat_has_Rezk_completions.
  Admitted.

End CategoriesWithSubobjectclassifiersAdmitRezkCompletions.
