(*
In this file, we show how the Rezk completion of a category has a suitable terminal object (in terms of preservation) if the original category has a terminal object.
Hence, categories with terminal objects admit a Rezk completion.

Contents:
1. BicatOfCategoriesWithTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a terminal object (up to propositional truncation).
2. BicatOfCategoriesWithChosenTerminalHasRezkCompletion:
   A construction of the Rezk completion of categories equipped with a chosen terminal object.
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
Require Import UniMath.Bicategories.DisplayedBicats.UniversalArrows.OverCat.SigmaConstruction.
Require Import UniMath.Bicategories.DisplayedBicats.UniversalArrows.OverCat.ToProduct.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.Terminal.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.ProductsBin.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FiniteLimits.Pullbacks.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ElementaryTopoi.FinitelyComplete.

Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.TerminalObject.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.BinProducts.
Require Import UniMath.Bicategories.RezkCompletions.StructuredCats.Pullbacks.

Local Open Scope cat.

Section CategoriesWithFiniteLimitsAdmitRezkCompletions.

  Context (LUR : left_universal_arrow univ_cats_to_cats)
    (η_weak_equiv : ∏ C : category, is_weak_equiv (pr12 LUR C)).

  Let LUR_term : disp_left_universal_arrow LUR
         (disp_psfunctor_on_cat_to_univ_cat disp_bicat_chosen_terminal_obj
            (disp_2cells_isaprop_from_disp_2cells_iscontr disp_bicat_chosen_terminal_obj
               disp_2cells_is_contr_chosen_terminal_obj))
      := cat_with_chosen_terminal_obj_has_RezkCompletion LUR η_weak_equiv.

  Let LUR_prod := cat_with_binproducts_has_RezkCompletion LUR η_weak_equiv.
  Let LUR_pullb := cat_with_pullback_has_RezkCompletion LUR η_weak_equiv.

  Let t_p : disp_2cells_iscontr (Prod.disp_dirprod_bicat disp_bicat_binproducts disp_bicat_pullbacks).
  Proof.
    apply disp_dirprod_bicat_of_dirprod_iscontr.
    - apply disp_2cells_is_contr_binproducts.
    - apply disp_2cells_is_contr_pullbacks.
  Defined.

  Let LUR_pp := make_disp_left_universal_arrow_if_contr_CAT_on_dirprod LUR _ _ LUR_prod LUR_pullb.

  Let D_Lex := Prod.disp_dirprod_bicat disp_bicat_chosen_terminal_obj
               (Prod.disp_dirprod_bicat disp_bicat_have_binproducts disp_bicat_have_pullbacks).

  Let D_Lex_loc_prop : disp_2cells_isaprop D_Lex
    := (disp_2cells_isaprop_from_disp_2cells_iscontr
               (Prod.disp_dirprod_bicat disp_bicat_chosen_terminal_obj
                  (Prod.disp_dirprod_bicat disp_bicat_have_binproducts disp_bicat_have_pullbacks))
               (Prod.disp_2cells_iscontr_prod disp_bicat_chosen_terminal_obj
                  (Prod.disp_dirprod_bicat disp_bicat_have_binproducts disp_bicat_have_pullbacks)
                  disp_2cells_is_contr_chosen_terminal_obj
                  (Prod.disp_2cells_iscontr_prod disp_bicat_have_binproducts disp_bicat_have_pullbacks
                     disp_2cells_is_contr_have_binproducts disp_2cells_is_contr_have_pullbacks))).

  Definition cat_with_finlimits_has_RezkCompletion
    : disp_left_universal_arrow LUR
        (disp_psfunctor_on_cat_to_univ_cat
           D_Lex
           D_Lex_loc_prop).
  Proof.
    exact (make_disp_left_universal_arrow_if_contr_CAT_on_dirprod
             LUR _ _ LUR_term LUR_pp).
  Defined.

  (* Lemma cat_with_finlimits_psfunctor
    : disp_psfunctor_on_cat_to_univ_cat D_Lex D_Lex_loc_prop
      = disp_psfunctor_on_cat_to_univ_cat disp_bicat_lex
      (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_lex). *)

  Definition cat_with_finlimits_has_RezkCompletion'
    : disp_left_universal_arrow
        LUR
        (disp_psfunctor_on_cat_to_univ_cat disp_bicat_lex
           (disp_2cells_isaprop_from_disp_2cells_iscontr _ disp_2cells_is_contr_lex)).
  Proof.
    (* apply Previous *)
  Admitted.

End CategoriesWithFiniteLimitsAdmitRezkCompletions.
