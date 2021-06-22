Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Definition disp_nat_trans_eq_pointwise
           {C₁ C₂ : category}
           {F₁ F₂ : C₁ ⟶ C₂}
           {τ : F₁ ⟹ F₂}
           {D₁ : disp_precat C₁}
           {D₂ : disp_precat C₂}
           {FF₁ : disp_functor_data F₁ D₁ D₂}
           {FF₂ : disp_functor_data F₂ D₁ D₂}
           {ττ₁ ττ₂ : disp_nat_trans τ FF₁ FF₂}
           (p : ττ₁ = ττ₂)
           {x : C₁}
           (xx : D₁ x)
  : ττ₁ x xx = ττ₂ x xx.
Proof.
  induction p.
  apply idpath.
Qed.

Definition disp_codomain_functor_data
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor_data F (disp_codomain C₁) (disp_codomain C₂).
Proof.
  use tpair.
  - exact (λ x fx, F (pr1 fx) ,, #F (pr2 fx)).
  - simpl ; intros x y fx fy f ff.
    simple refine (#F (pr1 ff) ,, _) ; simpl.
    abstract
      (rewrite <- !functor_comp ;
       apply maponpaths ;
       apply (pr2 ff)).
Defined.

Definition transportf_codomain
           {C : category}
           {x₁ y₁ x₂ y₂ : C}
           (f₁ : x₁ --> y₁)
           (f₂ : x₂ --> y₂)
           {g₁ g₂ : y₁ --> y₂}
           (p : g₂ = g₁)
           (h : x₁ --> x₂)
           (q : h · f₂ = f₁ · g₂)
  : transportf
      (@mor_disp _ (disp_codomain C) _ _ (x₁ ,, f₁) (x₂ ,, f₂))
      p
      (h ,, q)
    =
    h ,, transportf (λ z, _ = _ · z) p q.
Proof.
  induction p.
  apply idpath.
Qed.

Definition disp_codomain_functor_axioms
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor_axioms (disp_codomain_functor_data F).
Proof.
  repeat split.
  - intros x fx ; simpl.
    refine (_ @ !(transportf_codomain _ _ _ _ _)).
    use subtypePath.
    {
      intro.
      apply C₂.
    }
    cbn.
    apply functor_id.
  - intros x y z fx fy fz f g ff gg ; simpl.
    refine (_ @ !(transportf_codomain _ _ _ _ _)).
    use subtypePath.
    {
      intro.
      apply C₂.
    }
    cbn.
    apply functor_comp.
Qed.

Definition disp_codomain_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor F (disp_codomain C₁) (disp_codomain C₂).
Proof.
  use tpair.
  - exact (disp_codomain_functor_data F).
  - exact (disp_codomain_functor_axioms F).
Defined.

Definition disp_codomain_nat_trans
           {C₁ C₂ : category}
           {F₁ F₂ : C₁ ⟶ C₂}
           (n : F₁ ⟹ F₂)
  : disp_nat_trans n (disp_codomain_functor F₁) (disp_codomain_functor F₂).
Proof.
  use tpair.
  - refine (λ x xx, n (pr1 xx) ,, _).
    abstract
      (simpl ;
       refine (!_) ;
       apply nat_trans_ax).
  - abstract
      (intros x y fx fy f ff ; cbn ;
       refine (_ @ !(transportf_codomain _ _ _ _ _)) ;
       use subtypePath ; [ intro ; apply C₂ | ] ; cbn ;
       apply nat_trans_ax).
Defined.

Definition disp_cat_ob_mor_comprehensions
  : disp_cat_ob_mor (total_bicat DispBicatOfFibs).
Proof.
  use tpair.
  - exact (λ C, disp_functor (functor_identity _ ) (pr12 C) (disp_codomain _)).
  - intros C C' D D' F ; simpl in *.
    exact (disp_nat_trans
             (nat_trans_comp
                _ _ _
                (nat_trans_functor_id_right _)
                (nat_trans_functor_id_left_inv _))
             (disp_functor_composite
                (pr12 F)
                D')
             (disp_functor_composite
                D
                (@disp_codomain_functor (pr1 C) (pr1 C') (pr1 F)))).
Defined.

Definition disp_cat_id_comprehensions
           (C : total_bicat DispBicatOfFibs)
           (χ : disp_cat_ob_mor_comprehensions C)
  : χ -->[ id₁ C ] χ.
Proof.
  simpl in *.
  use tpair.
  - intros x xx ; cbn.
    refine (identity _ ,, _).
    abstract
      (rewrite id_left, !id_right ;
       apply idpath).
  - abstract
      (intros x y f fx fy ff ; cbn in * ;
       refine (_ @ !(transportf_codomain _ _ _ _ _)) ;
       use subtypePath ; [ intro ; apply (pr1 C) | ] ;
       simpl ;
       rewrite id_left, !id_right ;
       apply idpath).
Defined.

Definition disp_cat_comp_comprehensions
           (C₁ C₂ C₃ : total_bicat DispBicatOfFibs)
           (F : total_bicat DispBicatOfFibs ⟦ C₁ , C₂ ⟧)
           (G : total_bicat DispBicatOfFibs ⟦ C₂ , C₃ ⟧)
           (χ₁ : disp_cat_ob_mor_comprehensions C₁)
           (χ₂ : disp_cat_ob_mor_comprehensions C₂)
           (χ₃ : disp_cat_ob_mor_comprehensions C₃)
           (Ff : χ₁ -->[ F ] χ₂)
           (Gg : χ₂ -->[ G ] χ₃)
  : χ₁ -->[ F · G ] χ₃.
Proof.
  simpl in *.
  use tpair.
  - intros x xx ; cbn.
    pose (f := pr1 Ff x xx).
    pose (g := pr1 Gg (pr1 F x) (pr12 F _ xx)).
    refine (pr1 g · # (pr1 G) (pr1 f) ,, _).
    abstract
      (rewrite !id_right ;
       rewrite assoc' ;
       rewrite <- (functor_comp (pr1 G) (pr1 f)) ;
       refine (maponpaths (λ z, _ · # (pr1 G) z) (pr2 f) @ _) ;
       simpl ;
       rewrite !id_right ;
       refine (pr2 g @ _) ;
       simpl ;
       rewrite !id_right ;
       apply idpath).
  - abstract
      (simpl ;
       intros x y f fx fy ff ; cbn in * ;
       refine (_ @ !(transportf_codomain _ _ _ _ _)) ;
       use subtypePath ; [ intro ; apply (pr1 C₃) | ] ;
       simpl ;
       assert (p := maponpaths pr1 (pr2 Ff x y f fx fy ff
                   @ transportf_codomain _ _ _ _ _)) ;
       simpl in p ;
       assert (n := pr2 Gg _ _ _ _ _ (disp_functor_on_morphisms (pr12 F) ff)) ;
       assert (q := maponpaths pr1 (n @ transportf_codomain _ _ _ _ _)) ;
       simpl in q ;
       rewrite assoc ;
       rewrite q ;
       rewrite !assoc' ;
       apply maponpaths ;
       rewrite <- !functor_comp ;
       apply maponpaths ;
       apply p).
Defined.

Definition disp_cat_id_comp_comprehensions
  : disp_cat_id_comp (total_bicat DispBicatOfFibs) disp_cat_ob_mor_comprehensions.
Proof.
  refine (_ ,, _).
  - exact disp_cat_id_comprehensions.
  - exact disp_cat_comp_comprehensions.
Defined.

Definition disp_cat_data_comprehensions : disp_cat_data (total_bicat DispBicatOfFibs).
Proof.
  use tpair.
  - exact disp_cat_ob_mor_comprehensions.
  - exact disp_cat_id_comp_comprehensions.
Defined.

Definition isaset_disp_1cells_comprehensions
           {C₁ C₂ : total_bicat DispBicatOfFibs}
           (F : C₁ --> C₂)
           (D₁ : disp_cat_data_comprehensions C₁)
           (D₂ : disp_cat_data_comprehensions C₂)
  : isaset (D₁ -->[ F ] D₂).
Proof.
  apply isaset_disp_nat_trans.
Qed.

Definition disp_prebicat_1_id_comp_cells_comprehensions
  : disp_prebicat_1_id_comp_cells (total_bicat DispBicatOfFibs).
Proof.
  use tpair.
  - exact disp_cat_data_comprehensions.
  - refine (λ C₁ C₂ F G α χ₁ χ₂ χF χG, _).
    pose (d := pr12 α).
    pose (d₁ := disp_nat_trans_comp
                  χF
                  (pre_whisker_disp_nat_trans χ₁ (disp_codomain_nat_trans (pr1 α)))).
    refine (disp_nat_trans_comp
              (post_whisker_disp_nat_trans
                 _
                 χ₂)
              χG
            =
            transportb (λ z, disp_nat_trans z _ _) _ d₁).
    + exact d.
    + abstract
        (apply nat_trans_eq ; [ apply (pr1 C₂) | ] ;
         simpl ;
         intro ;
         rewrite !id_right, !id_left ;
         apply idpath).
Defined.

Definition disp_prebicat_ops_data_comprehensions
  : disp_prebicat_ops disp_prebicat_1_id_comp_cells_comprehensions.
Proof.
  repeat split.
  - intros C₁ C₂ F χ₁ χ₂ Ff.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp Ff _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₂).
    }
    simpl in *.
    rewrite id_right.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₂ (pr12 F x xx))).
    }
    simpl.
    rewrite id_left.
    apply idpath.
  - intros C₁ C₂ F χ₁ χ₂ χF.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp
                  (id_disp χ₁ ;; χF)%mor_disp
                  _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₂).
    }
    simpl in *.
    rewrite id_right.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₂ (pr12 F x xx))).
    }
    simpl.
    rewrite functor_id.
    rewrite id_left, id_right.
    apply idpath.
  - intros C₁ C₂ F χ₁ χ₂ χF.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp
                  (χF ;; id_disp χ₂)%mor_disp
                  _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₂).
    }
    simpl in *.
    rewrite id_right.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₂ (pr12 F x xx))).
    }
    simpl.
    apply idpath.
  - intros C₁ C₂ F χ₁ χ₂ χF.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp χF _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₂).
    }
    simpl in *.
    rewrite id_right.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₂ (pr12 F x xx))).
    }
    simpl.
    rewrite functor_id, id_left, id_right.
    apply idpath.
  - intros C₁ C₂ F χ₁ χ₂ χF.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp χF _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₂).
    }
    simpl in *.
    rewrite id_right.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₂ (pr12 F x xx))).
    }
    simpl.
    rewrite !id_left.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H χ₁ χ₂ χ₃ χ₄ χF χG χH.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp
                  (χF ;; χG ;; χH)%mor_disp
                  _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₄).
    }
    simpl in *.
    rewrite id_right.
    rewrite functor_comp.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₄ _)).
    }
    simpl.
    rewrite id_left.
    apply idpath.
  - intros C₁ C₂ C₃ C₄ F G H χ₁ χ₂ χ₃ χ₄ χF χG χH.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp
                  (χF ;; (χG ;; χH))%mor_disp
                  _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₄).
    }
    simpl in *.
    rewrite id_right.
    rewrite functor_comp.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths pr1 (disp_functor_id χ₄ _)).
    }
    simpl.
    rewrite id_left.
    apply idpath.
  - intros C₁ C₂ F₁ F₂ F₃ τ₁ τ₂ χ₁ χ₂ χF χG χH χτ₁ χτ₂.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp χF _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₂).
    }
    simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (maponpaths pr1 (disp_functor_comp χ₂ _ _)).
    }
    simpl.
    assert (p := maponpaths
                   pr1
                   (disp_nat_trans_eq_pointwise χτ₁ xx
                    @ disp_nat_trans_transportf
                        _ _
                        _ _
                        (pr1 F₁ ∙ functor_identity _)
                        _
                        _ _
                        _
                        _ _
                        _
                        _ _
                    @ transportf_codomain _ _ _ _ _)).
    assert (q := maponpaths
                   pr1
                   (disp_nat_trans_eq_pointwise χτ₂ xx
                    @ disp_nat_trans_transportf
                        _ _
                        _ _
                        (pr1 F₂ ∙ functor_identity _)
                        _
                        _ _
                        _
                        _ _
                        _
                        _ _
                    @ transportf_codomain _ _ _ _ _)).
    simpl in p, q.
    simpl in *.
    rewrite assoc'.
    rewrite q.
    rewrite !assoc.
    apply maponpaths_2.
    apply p.
  - intros C₁ C₂ C₃ F G₁ G₂ τ χ₁ χ₂ χ₃ χF χG₁ χG₂ χτ.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp
                  (χF ;; χG₁)%mor_disp
                  _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₃).
    }
    assert (p := maponpaths
                   pr1
                   (disp_nat_trans_eq_pointwise χτ ((pr12 F : disp_functor _ _ _) _ xx)
                    @ disp_nat_trans_transportf
                        _ _
                        _ _
                        (pr1 G₁ ∙ functor_identity _)
                        _
                        _ _
                        _
                        _ _
                        _
                        _ _
                    @ transportf_codomain _ _ _ _ _)).
    simpl in *.
    rewrite !assoc.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact p.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (!_).
    apply nat_trans_ax.
  - intros C₁ C₂ C₃ F₁ F₂ G τ χ₁ χ₂ χ₃ χF₁ χF₂ χG χτ.
    apply disp_nat_trans_eq.
    intros x xx.
    refine (!_).
    etrans.
    {
      apply (disp_nat_trans_transportf
               _ _
               _ _
               _ _
               _ _
               _
               _ _
               (disp_nat_trans_comp
                  (χF₁ ;; χG)%mor_disp
                  _)).
    }
    refine (transportf_codomain _ _ _ _ _ @ _).
    simpl.
    use subtypePath.
    {
      intro.
      apply (pr1 C₃).
    }
    simpl.
    assert (p := maponpaths
                   pr1
                   (disp_nat_trans_eq_pointwise χτ xx
                    @ disp_nat_trans_transportf
                        _ _
                        _ _
                        (pr1 F₁ ∙ functor_identity _)
                        _
                        _ _
                        _
                        _ _
                        _
                        _ _
                    @ transportf_codomain _ _ _ _ _)).
    simpl in *.
    rewrite !assoc'.
    rewrite <- functor_comp.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!p).
    }
    rewrite functor_comp.
    rewrite !assoc.
    apply maponpaths_2.
    refine (!_).
    exact (maponpaths
             pr1
             (pr2 χG _ _ _ _ _ ((pr12 τ : disp_nat_trans _ _ _) x xx)
              @ transportf_codomain _ _ _ _ _)).
Qed.

Definition disp_prebicat_data_comprehensions
  : disp_prebicat_data (total_bicat DispBicatOfFibs).
Proof.
  use tpair.
  - exact disp_prebicat_1_id_comp_cells_comprehensions.
  - exact disp_prebicat_ops_data_comprehensions.
Defined.

Definition isaprop_disp_2cells_comprehensions
           {C₁ C₂ : total_bicat DispBicatOfFibs}
           {F₁ F₂ : C₁ --> C₂}
           (τ : F₁ ==> F₂)
           {χ₁ : disp_prebicat_data_comprehensions C₁}
           {χ₂ : disp_prebicat_data_comprehensions C₂}
           (χF₁ : χ₁ -->[ F₁ ] χ₂)
           (χF₂ : χ₁ -->[ F₂ ] χ₂)
  : isaprop (χF₁ ==>[ τ ] χF₂).
Proof.
  apply (isaset_disp_nat_trans
           _ _
           _ _
           _ _
           _
           (disp_functor_composite _ _)).
Qed.

Definition disp_prebicat_laws_comprehensions
  : disp_prebicat_laws disp_prebicat_data_comprehensions.
Proof.
  repeat split ; intro ; intros ; apply isaprop_disp_2cells_comprehensions.
Qed.

Definition disp_prebicat_comprehensions : disp_prebicat (total_bicat DispBicatOfFibs).
Proof.
  use tpair.
  - exact disp_prebicat_data_comprehensions.
  - exact disp_prebicat_laws_comprehensions.
Defined.

Definition disp_prebicat_comprehensions_has_disp_cellset
  : has_disp_cellset disp_prebicat_comprehensions.
Proof.
  intros C₁ C₂ F₁ F₂ τ χ₁ χ₂ χF₁ χF₂.
  apply isasetaprop.
  apply isaprop_disp_2cells_comprehensions.
Qed.

Definition disp_bicat_comprehensions_help : disp_bicat (total_bicat DispBicatOfFibs).
Proof.
  use tpair.
  - exact disp_prebicat_comprehensions.
  - exact disp_prebicat_comprehensions_has_disp_cellset.
Defined.

Definition disp_bicat_comprehensions
  : disp_bicat bicat_of_cats
  := sigma_bicat
       bicat_of_cats
       DispBicatOfFibs
       disp_bicat_comprehensions_help.

Definition disp_bicat_is_comprehension_category
  : disp_bicat (total_bicat disp_bicat_comprehensions)
  := disp_fullsubbicat
       (total_bicat disp_bicat_comprehensions)
       (λ C, is_cartesian_disp_functor (pr22 C)).

Definition disp_bicat_comprehension_category
  : disp_bicat bicat_of_cats
  := sigma_bicat
       bicat_of_cats
       disp_bicat_comprehensions
       disp_bicat_is_comprehension_category.

Definition comprehension_category
  : bicat
  := total_bicat disp_bicat_comprehension_category.

(* Accessors and builders for the bicategory of comprehension categories *)

(*
We also need
B : bicat
D₁ : disp_bicat B
D₂ : disp_bicat B
-------------------------------------
lift D₂ : disp_bicat (total_bicat D₁)

This way we can define extensions (∏, Σ) of comprehension categories, and layer them properly
 *)
