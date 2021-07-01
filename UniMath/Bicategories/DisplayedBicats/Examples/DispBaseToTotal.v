Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

(**
If we have displayed bicateogyres [D₁] and [D₂] over [B],
then we get a displayed bicategory over [∫ D₁] from [D₂].
 *)
Section DispToTotal.
  Context {B : bicat}
          (D₁ D₂ : disp_bicat B).

  Definition disp_cat_ob_mor_to_total
    : disp_cat_ob_mor (total_bicat D₁).
  Proof.
    use tpair.
    - exact (λ z, D₂ (pr1 z)).
    - exact (λ x y xx yy f, xx -->[ pr1 f ] yy).
  Defined.

  Definition disp_cat_id_comp_to_total
    : disp_cat_id_comp (total_bicat D₁) disp_cat_ob_mor_to_total.
  Proof.
    use tpair.
    - exact (λ x xx, id_disp xx).
    - exact (λ _ _ _ _ _ _ _ _ ff gg, (ff ;; gg)%mor_disp).
  Defined.

  Definition disp_cat_data_to_total
    : disp_cat_data (total_bicat D₁).
  Proof.
    use tpair.
    - exact disp_cat_ob_mor_to_total.
    - exact disp_cat_id_comp_to_total.
  Defined.

  Definition disp_2cell_struct_to_total
    : disp_2cell_struct disp_cat_ob_mor_to_total
    := λ _ _ _ _ τ _ _ ff gg, ff ==>[ pr1 τ ] gg.

  Definition disp_prebicat_1_id_comp_cells_to_total
    : disp_prebicat_1_id_comp_cells (total_bicat D₁).
  Proof.
    use tpair.
    - exact disp_cat_data_to_total.
    - exact disp_2cell_struct_to_total.
  Defined.

  Definition disp_prebicat_ops_to_total
    : disp_prebicat_ops disp_prebicat_1_id_comp_cells_to_total.
  Proof.
    repeat split.
    - intros x y f xx yy ff.
      apply disp_id2.
    - intros x y f xx yy ff.
      apply disp_lunitor.
    - intros x y f xx yy ff.
      apply disp_runitor.
    - intros x y f xx yy ff.
      apply disp_linvunitor.
    - intros x y f xx yy ff.
      apply disp_rinvunitor.
    - intros w x y z f g h ww xx yy zz ff gg hh.
      apply disp_rassociator.
    - intros w x y z f g h ww xx yy zz ff gg hh.
      apply disp_lassociator.
    - intros x y f g h φ ψ xx yy ff gg hh φφ ψψ.
      exact (disp_vcomp2 φφ ψψ).
    - intros x y z f g₁ g₂ φ xx yy zz ff gg₁ gg₂ φφ.
      exact (disp_lwhisker ff φφ).
    - intros x y z f₁ f₂ g φ xx yy zz ff₁ ff₂ gg φφ.
      exact (disp_rwhisker gg φφ).
  Defined.

  Definition disp_prebicat_data_to_total
    : disp_prebicat_data (total_bicat D₁).
  Proof.
    use tpair.
    - exact disp_prebicat_1_id_comp_cells_to_total.
    - exact disp_prebicat_ops_to_total.
  Defined.

  Definition transportb_over_total
             {x y : total_bicat D₁}
             {f g : x --> y}
             {xx : D₂ (pr1 x)}
             {yy : D₂ (pr1 y)}
             {ff : xx -->[ pr1 f ] yy}
             {gg : xx -->[ pr1 g ] yy}
             {φ ψ : pr1 f ==> pr1 g}
             (φ' : pr2 f ==>[ φ ] pr2 g)
             (ψ' : pr2 f ==>[ ψ ] pr2 g)
             (p : φ = ψ)
             (ψψ : ff ==>[ ψ ] gg)
             (q : φ' = transportb (λ x0 : pr1 f ==> pr1 g, pr2 f ==>[ x0] pr2 g) p ψ')
    : transportb
        (λ α : pr1 f ==> pr1 g, ff ==>[ α ] gg)
        p
        ψψ
      =
      transportb
        (λ α : f ==> g, disp_2cell_struct_to_total _ _ _ _ α _ _ ff gg)
        (@total2_paths_b
           _ _
           (φ ,, φ') (ψ ,, ψ')
           p q)
        ψψ.
  Proof.
    induction p.
    cbn in q.
    induction q.
    apply idpath.
  Qed.

  Definition disp_prebicat_laws_to_total
    : disp_prebicat_laws disp_prebicat_data_to_total.
  Proof.
    repeat split ; intro ; intros ; cbn ; refine (_ @ transportb_over_total _ _ _ _ _).
    - apply disp_id2_left.
    - apply disp_id2_right.
    - apply disp_vassocr.
    - apply disp_lwhisker_id2.
    - apply disp_id2_rwhisker.
    - apply disp_lwhisker_vcomp.
    - apply disp_rwhisker_vcomp.
    - apply disp_vcomp_lunitor.
    - apply disp_vcomp_runitor.
    - apply disp_lwhisker_lwhisker.
    - apply disp_rwhisker_lwhisker.
    - apply disp_rwhisker_rwhisker.
    - apply disp_vcomp_whisker.
    - apply disp_lunitor_linvunitor.
    - apply disp_linvunitor_lunitor.
    - apply disp_runitor_rinvunitor.
    - apply disp_rinvunitor_runitor.
    - apply disp_lassociator_rassociator.
    - apply disp_rassociator_lassociator.
    - apply disp_runitor_rwhisker.
    - apply disp_lassociator_lassociator.
  Qed.

  Definition disp_prebicat_to_total
    : disp_prebicat (total_bicat D₁).
  Proof.
    use tpair.
    - exact disp_prebicat_data_to_total.
    - exact disp_prebicat_laws_to_total.
  Defined.

  Definition has_disp_cellset_to_total
    : has_disp_cellset disp_prebicat_to_total.
  Proof.
    intros x y f g φ xx yy ff gg.
    apply D₂.
  Qed.

  Definition disp_bicat_to_total
    : disp_bicat (total_bicat D₁).
  Proof.
    use tpair.
    - exact disp_prebicat_to_total.
    - exact has_disp_cellset_to_total.
  Defined.
End DispToTotal.
