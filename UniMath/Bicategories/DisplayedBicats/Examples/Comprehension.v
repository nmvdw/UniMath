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
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FiniteLimits.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Definition section
           {C : precategory}
           {a b : C}
           (r : a --> b)
  : UU
  := ∑ (s : b --> a), s · r = identity b.

Definition make_section
           {C : precategory}
           {a b : C}
           {r : a --> b}
           (s : b --> a)
           (p : s · r = identity b)
  : section r
  := (s ,, p).

Definition is_cartesian_id_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           (xx : D x)
  : is_cartesian (id_disp xx).
Proof.
  intros z g zz hh.
  use iscontraprop1.
  - use invproofirrelevance.
    intros f₁ f₂.
    use subtypePath.
    {
      intro ; intros.
      apply D.
    }
    refine (id_right_disp_var _ @ _ @ !(id_right_disp_var _)).
    rewrite (pr2 f₁), (pr2 f₂).
    apply idpath.
  - use tpair.
    + exact (transportf _ (id_right _) hh).
    + simpl.
      rewrite id_right_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite pathsinv0r.
      apply idpath.
Qed.

Definition is_cartesian_comp_disp
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx : D x}
           {y : C}
           {yy : D y}
           {z : C}
           {zz : D z}
           {f : x --> y} {g : y --> z}
           {ff : xx -->[ f ] yy} {gg : yy -->[ g ] zz}
           (Hff : is_cartesian ff) (Hgg : is_cartesian gg)
  : is_cartesian (ff ;; gg)%mor_disp.
Proof.
  intros w h ww hh'.
  use iscontraprop1.
  - use invproofirrelevance.
    intros f₁ f₂.
    use subtypePath.
    {
      intro ; intros.
      apply D.
    }
    pose (hh'' := transportf _ (assoc _ _ _) hh').
    specialize (Hgg _ _ _ hh'').
    pose (pr1 Hgg) as t.
    specialize (Hff w h ww (pr1 t)).
    pose (isapropifcontr Hff) as i.
    refine (maponpaths pr1 (proofirrelevance _ i (_ ,, _) (_ ,, _))).
    + pose (isapropifcontr Hgg) as j.
      refine (maponpaths pr1 (proofirrelevance _ j (_ ,, _) (_ ,, _))).
      etrans.
      {
        apply assoc_disp_var.
      }
      unfold hh''.
      apply maponpaths.
      exact (pr2 f₁).
    + pose (isapropifcontr Hgg) as j.
      refine (maponpaths pr1 (proofirrelevance _ j (_ ,, _) (_ ,, _))).
      etrans.
      {
        apply assoc_disp_var.
      }
      unfold hh''.
      apply maponpaths.
      exact (pr2 f₂).
  - pose (transportf _ (assoc _ _ _) hh') as hh''.
    pose (Hgg _ _ _ hh'') as φ.
    pose (pr1 φ) as φar.
    pose (Hff _ _ _ (pr1 φar)) as ψ.
    use tpair.
    + exact (pr11 ψ).
    + simpl.
      rewrite assoc_disp.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact (pr21 ψ).
      }
      etrans.
      {
        apply maponpaths.
        exact (pr21 φ).
      }
      unfold hh''.
      etrans.
      {
        apply transport_f_f.
      }
      rewrite pathsinv0r.
      apply idpath.
Qed.

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
  := disp_dirprod_bicat
       disp_bicat_terminal_obj
       (sigma_bicat
          bicat_of_cats
          DispBicatOfFibs
          disp_bicat_comprehensions_help).

Definition disp_bicat_is_comprehension_category
  : disp_bicat (total_bicat disp_bicat_comprehensions)
  := disp_fullsubbicat
       (total_bicat disp_bicat_comprehensions)
       (λ C, is_cartesian_disp_functor (pr222 C)).

Definition disp_bicat_comprehension_category
  : disp_bicat bicat_of_cats
  := sigma_bicat
       bicat_of_cats
       disp_bicat_comprehensions
       disp_bicat_is_comprehension_category.

Definition comprehension_category
  : bicat
  := total_bicat disp_bicat_comprehension_category.

(** Builder for comprehension categories *)
Definition make_comprehension_category_on
           (C : univalent_category)
           (D : disp_cat C)
           (HD : is_univalent_disp D)
           (CD : cleaving D)
           (T : Terminal C)
           (χ : disp_functor
                  (functor_identity _)
                  D
                  (disp_codomain C))
           (Hχ : is_cartesian_disp_functor χ)
  : disp_bicat_comprehension_category C.
Proof.
  simple refine ((_ ,, ((_ ,, (_ ,, _)) ,, _)) ,, _).
  - exact T.
  - exact D.
  - exact HD.
  - exact CD.
  - exact χ.
  - exact Hχ.
Defined.

Definition make_comprehension_category
           (C : univalent_category)
           (D : disp_cat C)
           (HD : is_univalent_disp D)
           (CD : cleaving D)
           (T : Terminal C)
           (χ : disp_functor
                  (functor_identity _)
                  D
                  (disp_codomain C))
           (Hχ : is_cartesian_disp_functor χ)
  : comprehension_category.
Proof.
  simple refine (_ ,, _).
  - exact C.
  - use make_comprehension_category_on.
    + exact D.
    + exact HD.
    + exact CD.
    + exact T.
    + exact χ.
    + exact Hχ.
Defined.

(** Accessors for comprehension categories *)
Section Accessors.
  Variable (C : comprehension_category).

  Definition base_category_of
    : univalent_category.
  Proof.
    exact (pr1 C).
  Defined.

  Definition disp_cat_of
    : disp_cat base_category_of.
  Proof.
    exact (pr11 (pr212 C)).
  Defined.

  Definition disp_cat_of_is_univalent
    : is_univalent_disp disp_cat_of.
  Proof.
    exact (pr121 (pr212 C)).
  Defined.

  Definition disp_cat_of_cleaving
    : cleaving disp_cat_of.
  Proof.
    exact (pr221 (pr212 C)).
  Defined.

  Definition terminal_of
    : Terminal base_category_of.
  Proof.
    exact (pr112 C).
  Defined.

  Definition comprehension_of
    : disp_functor
        (functor_identity _)
        disp_cat_of
        (disp_codomain _).
  Proof.
    exact (pr2 (pr212 C)).
  Defined.

  Definition comprehension_is_cartesian
    : is_cartesian_disp_functor comprehension_of.
  Proof.
    exact (pr22 C).
  Defined.
End Accessors.

Definition make_comprehension_cat_mor_on
           {C D : comprehension_category}
           (F : base_category_of C ⟶ base_category_of D)
           (FT : preserves_terminal F (terminal_of C) (terminal_of D))
           (disp_F : disp_functor F (disp_cat_of C) (disp_cat_of D))
           (Fχ : disp_nat_trans
                   (nat_trans_comp
                      _ _ _
                      (nat_trans_functor_id_right F)
                      (nat_trans_functor_id_left_inv F))
                   (disp_functor_composite
                      disp_F
                      (comprehension_of D))
                   (disp_functor_composite
                      (comprehension_of C)
                      (disp_codomain_functor F)))
  : pr2 C -->[ F ] pr2 D.
Proof.
  simple refine ((_ ,, ((_ ,, tt) ,, _)) ,, tt) ; simpl.
  - exact FT.
  - exact disp_F.
  - exact Fχ.
Defined.

Definition make_comprehension_cat_mor
           {C D : comprehension_category}
           (F : base_category_of C ⟶ base_category_of D)
           (FT : preserves_terminal F (terminal_of C) (terminal_of D))
           (disp_F : disp_functor F (disp_cat_of C) (disp_cat_of D))
           (Fχ : disp_nat_trans
                   (nat_trans_comp
                      _ _ _
                      (nat_trans_functor_id_right F)
                      (nat_trans_functor_id_left_inv F))
                   (disp_functor_composite
                      disp_F
                      (comprehension_of D))
                   (disp_functor_composite
                      (comprehension_of C)
                      (disp_codomain_functor F)))
  : C --> D.
Proof.
  simple refine (_ ,, _).
  - exact F.
  - use make_comprehension_cat_mor_on.
    + exact FT.
    + exact disp_F.
    + exact Fχ.
Defined.

Section Accessors.
  Context {C D : comprehension_category}
          (F : C --> D).

  Definition base_functor_of
    : base_category_of C ⟶ base_category_of D
    := pr1 F.

  Definition preserves_terminal_of_comp
    : preserves_terminal
        base_functor_of
        (terminal_of C)
        (terminal_of D)
    := pr112 F.

  Definition disp_functor_of
    : disp_functor
        base_functor_of
        (disp_cat_of C)
        (disp_cat_of D)
    := pr11 (pr212 F).

  Definition preserves_comprehension
    : disp_nat_trans
        (nat_trans_comp
           _ _ _
           (nat_trans_functor_id_right _)
           (nat_trans_functor_id_left_inv _))
        (disp_functor_composite
           disp_functor_of
           (comprehension_of D))
        (disp_functor_composite
           (comprehension_of C)
           (disp_codomain_functor base_functor_of))
    := pr2 (pr212 F).
End Accessors.

Definition TODO {A : UU} : A.
Admitted.

Definition make_comprehension_cat_2cell_on
           {C D : comprehension_category}
           {F G : C --> D}
           (α : pr1 F ==> pr1 G)
           (disp_α : disp_nat_trans
                       α
                       (disp_functor_of F)
                       (disp_functor_of G))
           (αχ : ∏ (x : base_category_of C)
                   (xx : disp_cat_of C x),
                 (pr1 (preserves_comprehension F x xx)
                  · pr1 α (pr1 (comprehension_of C x xx))
                  =
                  pr1 (#(comprehension_of D) (disp_α x xx))
                  · pr1 (pr1 (preserves_comprehension G) x xx))%mor_disp)
  : pr2 F ==>[ α ] pr2 G.
Proof.
  simple refine ((tt ,, ((_ ,, tt) ,, _)) ,, tt).
  - exact disp_α.
  - (*
    use disp_nat_trans_eq.
    intros x xx.
    use subtypePath ; [ intro ; apply homset_property | ].
    cbn ; unfold transportb.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (disp_nat_trans_transportf
               _ _ _ _ _ _ _ _
               _
               _ _
               (disp_nat_trans_comp
                  (preserves_comprehension F)
                  (pre_whisker_disp_nat_trans
                     (comprehension_of C)
                     (disp_codomain_nat_trans α)))
               _ _).
    }
    rewrite transportf_codomain.
    apply αχ.
     *)
    apply TODO.
Defined.

Definition make_comprehension_2cell
           {C D : comprehension_category}
           {F G : C --> D}
           (α : pr1 F ==> pr1 G)
           (disp_α : disp_nat_trans
                       α
                       (disp_functor_of F)
                       (disp_functor_of G))
           (αχ : ∏ (x : base_category_of C)
                   (xx : disp_cat_of C x),
                 (pr1 (preserves_comprehension F x xx)
                  · pr1 α (pr1 (comprehension_of C x xx))
                  =
                  pr1 (#(comprehension_of D) (disp_α x xx))
                  · pr1 (pr1 (preserves_comprehension G) x xx))%mor_disp)
  : F ==> G.
Proof.
  simple refine (_ ,, _).
  - exact α.
  - use make_comprehension_cat_2cell_on.
    + exact disp_α.
    + exact αχ.
Defined.

(** Shallow embedding of type theory in a comprehension category *)
Local Open Scope mor_disp.

(** The sorts *)
Definition Con
           (C : comprehension_category)
  : UU
  := base_category_of C.

Definition Sub
           {C : comprehension_category}
           (Γ₁ Γ₂ : Con C)
  : UU
  := Γ₁ --> Γ₂.

Definition Ty
           {C : comprehension_category}
           (Γ : Con C)
  : UU
  := disp_cat_of C Γ.

Definition Tm
           {C : comprehension_category}
           (Γ : Con C)
           (A : Ty Γ)
  : UU
  := section (pr2 (comprehension_of C Γ A)).

(** Constructors for contexts *)
Definition emptyCon
           (C : comprehension_category)
  : Con C
  := pr1 (terminal_of C).

Definition extendCon
           {C : comprehension_category}
           (Γ : Con C)
           (A : Ty Γ)
  : Con C
  := pr1 (comprehension_of C Γ A).

(** Constructors for types *)
Definition sub_Ty
           {C : comprehension_category}
           {Γ₂ : Con C}
           (A : Ty Γ₂)
           {Γ₁ : Con C}
           (s : Sub Γ₁ Γ₂)
  : Ty Γ₁
  := object_of_cartesian_lift _ _ (disp_cat_of_cleaving C _ _ s A).

Definition sub_Ty_mor
           {C : comprehension_category}
           {Γ₂ : Con C}
           (A : Ty Γ₂)
           {Γ₁ : Con C}
           (s : Sub Γ₁ Γ₂)
  : sub_Ty A s -->[ s ] A
  := mor_disp_of_cartesian_lift _ _ (disp_cat_of_cleaving C _ _ s A).

(** Constructors for substitutions *)
Definition extend_pr
           {C : comprehension_category}
           (Γ : Con C)
           (A : Ty Γ)
  : Sub (extendCon Γ A) Γ
  := pr2 (comprehension_of C Γ A).

Definition emptySub
           {C : comprehension_category}
           (Γ : Con C)
  : Sub Γ (emptyCon C)
  := TerminalArrow _ Γ.

Definition idSub
           {C : comprehension_category}
           (Γ : Con C)
  : Sub Γ Γ
  := identity Γ.

Definition compSub
           {C : comprehension_category}
           {Γ₁ Γ₂ Γ₃ : Con C}
           (s₁ : Sub Γ₁ Γ₂)
           (s₂ : Sub Γ₂ Γ₃)
  : Sub Γ₁ Γ₃
  := s₁ · s₂.

Definition extend_pair
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : Sub Γ₁ (extendCon Γ₂ A)
  := pr1 t · pr1 (# (comprehension_of C) (sub_Ty_mor A s)).

Definition pullback_from_sub
           {C : comprehension_category}
           {Γ₂ : Con C}
           (A : Ty Γ₂)
           {Γ₁ : Con C}
           (s : Sub Γ₁ Γ₂)
  : Pullback (pr2 (comprehension_of C Γ₂ A)) s
  := make_Pullback
       (extend_pr Γ₂ A) s
       (extendCon Γ₁ (sub_Ty A s))
       (pr1 (# (comprehension_of C) (sub_Ty_mor A s)))
       (extend_pr Γ₁ (sub_Ty A s))
       _
       (cartesian_isPullback_in_cod_disp
          _
          (comprehension_is_cartesian
             C
             _ _ _ _ _ _
             (disp_cat_of_cleaving C _ _ s A))).

Definition sub_Tm_help
           {C : comprehension_category}
           {Γ₂ : Con C}
           {A : Ty Γ₂}
           (t : Tm Γ₂ A)
           {Γ₁ : Con C}
           (s : Sub Γ₁ Γ₂)
  : s · pr1 t · pr2 (comprehension_of C Γ₂ A)
    =
    id₁ (functor_identity (base_category_of C) Γ₁) · s.
Proof.
  rewrite id_left.
  rewrite assoc'.
  refine (maponpaths (λ z, s · z) (pr2 t) @ _).
  apply id_right.
Qed.

Definition sub_Tm
           {C : comprehension_category}
           {Γ₂ : Con C}
           {A : Ty Γ₂}
           (t : Tm Γ₂ A)
           {Γ₁ : Con C}
           (s : Sub Γ₁ Γ₂)
  : Tm Γ₁ (sub_Ty A s).
Proof.
  use make_section.
  - use (PullbackArrow (pullback_from_sub A s)).
    + exact (s · pr1 t).
    + exact (identity _).
    + exact (sub_Tm_help t s).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (pullback_from_sub A s))).
Defined.

(** Operations on substitutions *)
Definition extend_var
           {C : comprehension_category}
           (Γ : Con C)
           (A : Ty Γ)
  : Tm (extendCon Γ A) (sub_Ty A (extend_pr Γ A)).
Proof.
  use make_section.
  - use (PullbackArrow (pullback_from_sub A _)).
    + exact (identity _).
    + exact (identity _).
    + abstract (apply idpath).
  - abstract
      (apply (PullbackArrow_PullbackPr2 (pullback_from_sub A _))).
Defined.

(** Equations *)

(* Equality of contexts, types, and terms *)
Definition path_Con
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (f : iso Γ₁ Γ₂)
  : Γ₁ = Γ₂.
Proof.
  apply isotoid.
  - apply (base_category_of C).
  - exact f.
Defined.

Definition path_Ty_over
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (f : iso Γ₁ Γ₂)
           {A₁ : Ty Γ₁}
           {A₂ : Ty Γ₂}
           (ff : iso_disp f A₁ A₂)
  : transportf Ty (path_Con f) A₁ = A₂.
Proof.
  apply isotoid_disp.
  - apply disp_cat_of_is_univalent.
  - unfold path_Con.
    rewrite idtoiso_isotoid.
    exact ff.
Qed.

Definition path_Ty
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (ff : iso_disp (identity_iso Γ) A₁ A₂)
  : A₁ = A₂.
Proof.
  refine (isotoid_disp _ (idpath _) ff).
  apply disp_cat_of_is_univalent.
Defined.

Definition path_Tm
           {C : comprehension_category}
           {Γ : Con C}
           {A : Ty Γ}
           {t₁ t₂ : Tm Γ A}
           (p : pr1 t₁ = pr1 t₂)
  : t₁ = t₂.
Proof.
  use subtypePath.
  {
    intro.
    apply base_category_of.
  }
  exact p.
Qed.

Definition transportf_Tm
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (ff : iso_disp (identity_iso Γ) A₁ A₂)
           (t : Tm Γ A₁)
  : Tm Γ A₂.
Proof.
  use make_section.
  - exact (pr1 t · pr1 (# (comprehension_of C) ff)).
  - abstract
      (simpl ;
       rewrite assoc' ;
       refine (maponpaths
                 (λ z, _ · z)
                 (pr2 (# (comprehension_of C) ff))
               @ _) ;
       rewrite assoc ;
       simpl ;
       rewrite id_right ;
       apply (pr2 t)).
Defined.

Definition transportb_Tm
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (ff : iso_disp (identity_iso Γ) A₁ A₂)
           (t : Tm Γ A₂)
  : Tm Γ A₁.
Proof.
  use make_section.
  - exact (pr1 t · pr1 (# (comprehension_of C) (inv_mor_disp_from_iso ff))).
  - abstract
      (rewrite assoc' ;
       refine (_ @ pr2 t) ;
       apply maponpaths ;
       refine (pr2 (# (comprehension_of C) _) @ _) ;
       apply id_right).
Defined.

Definition transportf_Tm_path
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (p : A₁ = A₂)
           (t : Tm Γ A₁)
  : Tm Γ A₂.
Proof.
  use make_section ; simpl.
  - refine (pr1 t · _).
    exact (pr1 (# (comprehension_of C) (idtoiso_disp (idpath _) p))).
  - abstract
      (rewrite assoc' ;
       refine (maponpaths
                 (λ z, _ · z)
                 (pr2 (# (comprehension_of C) _))
               @ _) ;
       rewrite assoc ;
       simpl ;
       rewrite id_right ;
       apply (pr2 t)).
Defined.

Definition transportb_Tm_path
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (p : A₁ = A₂)
           (t : Tm Γ A₂)
  : Tm Γ A₁.
Proof.
  use make_section ; simpl.
  - refine (pr1 t · _).
    exact (pr1 (# (comprehension_of C) (idtoiso_disp (idpath _) (!p)))).
  - abstract
      (rewrite assoc' ;
       refine (maponpaths
                 (λ z, _ · z)
                 (pr2 (# (comprehension_of C) _))
               @ _) ;
       rewrite assoc ;
       simpl ;
       rewrite id_right ;
       apply (pr2 t)).
Defined.

Definition path_transportf_path_Tm
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (p : A₁ = A₂)
           (t : Tm Γ A₁)
  : transportf (Tm Γ) p t
    =
    transportf_Tm_path p t.
Proof.
  apply path_Tm.
  induction p ; cbn.
  refine (!_).
  refine (_ @ id_right _).
  apply maponpaths.
  exact (maponpaths pr1 (disp_functor_id (comprehension_of C) _)).
Qed.

Definition path_transportf_Tm
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (ff : iso_disp (identity_iso Γ) A₁ A₂)
           (t : Tm Γ A₁)
  : transportf
      (Tm Γ)
      (path_Ty ff)
      t
    =
    transportf_Tm ff t.
Proof.
  pose (path_transportf_path_Tm
          (isotoid_disp (disp_cat_of_is_univalent C) (idpath _) ff)
          t)
    as p.
  refine (p @ _) ; clear p.
  use path_Tm.
  cbn -[idtoiso_disp].
  rewrite idtoiso_isotoid_disp.
  apply idpath.
Qed.

Definition path_comprehension
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A₁ : Ty Γ₁}
           {A₂ : Ty Γ₂}
           {s₁ s₂ : Sub Γ₁ Γ₂}
           (χs₁ : A₁ -->[ s₁ ] A₂)
           (χs₂ : A₁ -->[ s₂ ] A₂)
           (p : s₁ = s₂)
           (q : transportf _ p χs₁ = χs₂)
  : pr1 (# (comprehension_of C) χs₁)
    =
    pr1 (# (comprehension_of C) χs₂).
Proof.
  induction p, q.
  apply idpath.
Qed.

Definition path_transportb_Tm
           {C : comprehension_category}
           {Γ : Con C}
           {A₁ A₂ : Ty Γ}
           (ff : iso_disp (identity_iso Γ) A₁ A₂)
           (t : Tm Γ A₂)
  : transportb
      (Tm Γ)
      (path_Ty ff)
      t
    =
    transportb_Tm ff t.
Proof.
  use transportb_transpose_left.
  refine (!_).
  refine (path_transportf_Tm _ _ @ _).
  use path_Tm ; cbn.
  refine (_ @ id_right _).
  rewrite assoc'.
  apply maponpaths.
  pose (p := maponpaths
               pr1
               (disp_functor_comp
                  (comprehension_of C)
                  (inv_mor_disp_from_iso ff)
                  ff)).
  simpl in p.
  refine (!p @ _) ; clear p.
  pose (p := maponpaths
               pr1
               (disp_functor_id
                  (comprehension_of C)
                  A₂)).
  simpl in p.
  refine (_ @ p) ; clear p.
  use path_comprehension.
  - apply id_left.
  - etrans.
    {
      apply maponpaths.
      exact (iso_disp_after_inv_mor ff).
    }
    refine (transport_f_f _ _ _ _ @ _).
    apply transportf_set.
    apply (base_category_of C).
Qed.

(** Laws of the category *)
Definition compSub_id_left
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (s : Sub Γ₁ Γ₂)
  : compSub (idSub _) s = s.
Proof.
  apply id_left.
Qed.

Definition compSub_id_right
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (s : Sub Γ₁ Γ₂)
  : compSub s (idSub _) = s.
Proof.
  apply id_right.
Qed.

Definition compSub_assoc
           {C : comprehension_category}
           {Γ₁ Γ₂ Γ₃ Γ₄ : Con C}
           (s₁ : Sub Γ₁ Γ₂)
           (s₂ : Sub Γ₂ Γ₃)
           (s₃ : Sub Γ₃ Γ₄)
  : compSub s₁ (compSub s₂ s₃)
    =
    compSub (compSub s₁ s₂) s₃.
Proof.
  apply assoc.
Qed.

(* Laws for empty substitution *)
Definition postcomp_emptySub
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (s : Sub Γ₁ Γ₂)
  : compSub s (emptySub _)
    =
    emptySub _.
Proof.
  apply TerminalArrowEq.
Qed.

Definition id_emptySub
           (C : comprehension_category)
  : emptySub (emptyCon C) = identity _.
Proof.
  apply TerminalArrowEq.
Qed.

(* Substitution laws *)
Definition sub_Ty_id_iso
           {C : comprehension_category}
           {Γ : Con C}
           (A : Ty Γ)
  : iso_disp (identity_iso Γ) (sub_Ty A (idSub Γ)) A.
Proof.
  use (cartesian_lifts_iso (sub_Ty A (idSub Γ) ,, _) (A ,, _)).
  simpl.
  refine (id_disp _ ,, _).
  apply is_cartesian_id_disp.
Defined.

Definition sub_Ty_id
           {C : comprehension_category}
           {Γ : Con C}
           (A : Ty Γ)
  : sub_Ty A (idSub Γ) = A.
Proof.
  apply path_Ty.
  exact (sub_Ty_id_iso A).
Defined.

Definition sub_Ty_comp_iso
           {C : comprehension_category}
           {Γ₁ Γ₂ Γ₃ : Con C}
           (s₁ : Sub Γ₁ Γ₂) (s₂ : Sub Γ₂ Γ₃)
           (A : Ty Γ₃)
  : iso_disp
      (identity_iso Γ₁)
      (sub_Ty A (compSub s₁ s₂))
      (sub_Ty (sub_Ty A s₂) s₁).
Proof.
  use (cartesian_lifts_iso
         (sub_Ty A (compSub s₁ s₂) ,, _)
         (sub_Ty (sub_Ty A s₂) s₁ ,, _)).
  simpl.
  simple refine (_ ,, _).
  - pose (sub_Ty_mor A s₂) as m.
    pose (sub_Ty_mor (sub_Ty A s₂) s₁) as m'.
    exact (m' ;; m).
  - simpl.
    apply is_cartesian_comp_disp.
    + apply cartesian_lift_is_cartesian.
    + apply cartesian_lift_is_cartesian.
Defined.

Definition sub_Ty_comp
           {C : comprehension_category}
           {Γ₁ Γ₂ Γ₃ : Con C}
           (s₁ : Sub Γ₁ Γ₂) (s₂ : Sub Γ₂ Γ₃)
           (A : Ty Γ₃)
  : sub_Ty A (compSub s₁ s₂)
    =
    sub_Ty (sub_Ty A s₂) s₁.
Proof.
  apply path_Ty.
  exact (sub_Ty_comp_iso s₁ s₂ A).
Defined.

Definition sub_Tm_id
           {C : comprehension_category}
           {Γ : Con C}
           {A : Ty Γ}
           (t : Tm Γ A)
  : transportf
      (Tm Γ)
      (sub_Ty_id A)
      (sub_Tm t (idSub Γ))
    =
    t.
Proof.
  refine (path_transportf_Tm _ _ @ _).
  apply path_Tm.
  cbn -[sub_Ty_id_iso].
  pose (p := PullbackArrow_PullbackPr1
               (pullback_from_sub A (idSub _))
               _
               (idSub _ · pr1 t)
               (idSub _)
               (sub_Tm_help t (idSub Γ))).
  cbn in p.
  rewrite id_left in p.
  refine (_ @ p).
  do 3 apply maponpaths.
  use (cartesian_factorisation_unique (is_cartesian_id_disp A)).
  refine (cartesian_factorisation_commutes _ _ _ @ _).
  rewrite id_right_disp.
  use transportf_paths.
  apply (base_category_of C).
Qed.

Definition sub_Tm_comp
           {C : comprehension_category}
           {Γ₁ Γ₂ Γ₃ : Con C}
           (s₁ : Sub Γ₁ Γ₂) (s₂ : Sub Γ₂ Γ₃)
           {A : Ty Γ₃}
           (t : Tm Γ₃ A)
  : transportf
      (Tm Γ₁)
      (sub_Ty_comp s₁ s₂ A)
      (sub_Tm t (compSub s₁ s₂))
    =
    sub_Tm (sub_Tm t s₂) s₁.
Proof.
  use transportf_transpose_left.
  refine (_ @ !(path_transportb_Tm _ _)).
  apply path_Tm.
  cbn -[sub_Ty_comp_iso].
  refine (!_).
  use (@PullbackArrowUnique'
         _ _ _ _ _ _
         (pullback_from_sub A (compSub s₁ s₂))).
  - pose (PullbackArrow_PullbackPr1
            (pullback_from_sub (sub_Ty A s₂) s₁)
            _ _ _
            (sub_Tm_help (sub_Tm t s₂) s₁))
      as p.
    cbn in p.
    pose (PullbackArrow_PullbackPr1
            (pullback_from_sub A s₂)
            _ _ _
            (sub_Tm_help t s₂)) as q.
    cbn in q.
    unfold compSub.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!q).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      exact (!p).
    }
    clear p q.
    rewrite !assoc'.
    apply maponpaths.
    cbn -[sub_Ty_comp_iso].
    etrans.
    {
      exact (!(maponpaths
                 pr1
                 (disp_functor_comp (comprehension_of C) _ _))).
    }
    refine (!_).
    etrans.
    {
      exact (!(maponpaths
                 pr1
                 (disp_functor_comp (comprehension_of C) _ _))).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply (cartesian_factorisation_commutes (disp_cat_of_cleaving C _ _ (s₁ · s₂) A)).
    }
    cbn.
    use path_comprehension.
    + apply id_left.
    + etrans.
      {
        apply transport_f_f.
      }
      rewrite pathsinv0l.
      apply idpath.
  - pose (PullbackArrow_PullbackPr2
            (pullback_from_sub (sub_Ty A s₂) s₁)
            _ _ _
            (sub_Tm_help (sub_Tm t s₂) s₁))
      as p.
    cbn in p.
    refine (_ @ p).
    rewrite !assoc'.
    apply maponpaths.
    refine (pr2 (# (comprehension_of C)
                   (inv_mor_disp_from_iso (sub_Ty_comp_iso s₁ s₂ A)))
            @ _).
    apply id_right.
Qed.

(* Laws related to comprehension *)
Definition extend_pr_pair
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : compSub (extend_pair s t) (extend_pr Γ₂ A)
    =
    s.
Proof.
  pose (pr2 (# (comprehension_of C) (sub_Ty_mor A s)))
    as p.
  cbn in p.
  unfold extend_pair, extend_pr, compSub.
  rewrite assoc'.
  etrans.
  {
    apply maponpaths.
    exact p.
  }
  rewrite assoc.
  etrans.
  {
    apply maponpaths_2.
    apply (pr2 t).
  }
  apply id_left.
Qed.

Definition extend_pair_comp
           {C : comprehension_category}
           {Γ₁ Γ₂ Γ₃ : Con C}
           {A : Ty Γ₃}
           (s₁ : Sub Γ₁ Γ₂)
           (s₂ : Sub Γ₂ Γ₃)
           (t : Tm Γ₂ (sub_Ty A s₂))
  : compSub s₁ (extend_pair s₂ t)
    =
    extend_pair
      (compSub s₁ s₂)
      (transportf
         _
         (!sub_Ty_comp _ _ _)
         (sub_Tm t s₁)).
Proof.
  unfold extend_pair, compSub.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    unfold sub_Ty_comp.
    exact (maponpaths
             pr1
             (path_transportb_Tm
                (sub_Ty_comp_iso s₁ s₂ A)
                (sub_Tm t s₁))).
  }
  cbn -[sub_Ty_comp_iso].
  pose (p := PullbackArrow_PullbackPr1
               (pullback_from_sub (sub_Ty A s₂) s₁)
               _ _ _
               (sub_Tm_help t s₁)).
  simpl in p.
  rewrite assoc.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    exact (!p).
  }
  clear p.
  rewrite !assoc'.
  apply maponpaths.
  cbn -[sub_Ty_comp_iso].
  etrans.
  {
    exact (!(maponpaths
               pr1
               (disp_functor_comp (comprehension_of C) _ _))).
  }
  refine (!_).
  etrans.
  {
    exact (!(maponpaths
               pr1
               (disp_functor_comp (comprehension_of C) _ _))).
  }
  etrans.
  {
    do 2 apply maponpaths.
    apply cartesian_factorisation_commutes.
  }
  cbn.
  use path_comprehension.
  - apply id_left.
  - etrans.
    {
      apply transport_f_f.
    }
    rewrite pathsinv0l.
    apply idpath.
Qed.

Definition extend_pair_id
           {C : comprehension_category}
           {Γ : Con C}
           {A : Ty Γ}
  : extend_pair
      (extend_pr Γ A)
      (extend_var Γ A)
    =
    idSub _.
Proof.
  apply (PullbackArrow_PullbackPr1 (pullback_from_sub A (extend_pr Γ A))).
Qed.

Definition sub_Ty_path_sub_is_cartesian
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (A : Ty Γ₂)
           {s₁ s₂ : Sub Γ₁ Γ₂}
           (p : s₂ = s₁)
  : is_cartesian
      (transportf
         (λ z, sub_Ty A s₂ -->[ z] A)
         p
         (sub_Ty_mor A s₂)).
Proof.
  induction p ; cbn.
  apply cartesian_lift_is_cartesian.
Defined.

Definition sub_Ty_path_sub
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           (A : Ty Γ₂)
           {s₁ s₂ : Sub Γ₁ Γ₂}
           (p : s₂ = s₁)
  : iso_disp (identity_iso _) (sub_Ty A s₁) (sub_Ty A s₂).
Proof.
  use (cartesian_lifts_iso (sub_Ty A s₁ ,, _) (sub_Ty A s₂ ,, _)).
  simpl.
  simple refine (_ ,, _).
  - exact (transportf (λ z, _ -->[ z ] _) p (sub_Ty_mor A s₂)).
  - apply sub_Ty_path_sub_is_cartesian.
Defined.

Definition extend_pair_iso_path
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : id₁ Γ₁ · (pr1 t · pr1 (# (comprehension_of C) (sub_Ty_mor A s)) · extend_pr Γ₂ A)
    =
    s.
Proof.
  rewrite id_left.
  unfold extend_pr.
  rewrite assoc'.
  refine (maponpaths
            (λ z, _ · z)
            (pr2 (# (comprehension_of C) (sub_Ty_mor A s))) @ _).
  rewrite assoc.
  simpl.
  refine (maponpaths (λ z, z · _) (pr2 t) @ _).
  apply id_left.
Qed.

Definition extend_pair_iso_mor
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : sub_Ty A s
    -->[ identity Γ₁]
    sub_Ty (sub_Ty A (extend_pr Γ₂ A)) (extend_pair s t).
Proof.
  use (cartesian_factorisation
         (is_cartesian_comp_disp
            (cartesian_lift_is_cartesian
               (sub_Ty A (extend_pr Γ₂ A))
               (pr1 t · pr1 (# (comprehension_of C) (sub_Ty_mor A s)))
               _)
            (cartesian_lift_is_cartesian
               A
               (extend_pr Γ₂ A)
               _))).
  refine (transportb
            (mor_disp (sub_Ty A s) A)
            _
            (sub_Ty_mor A s)).
  apply extend_pair_iso_path.
Defined.

Definition extend_pair_iso'
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : iso_disp
      (identity_iso Γ₁)
      (sub_Ty A s)
      (sub_Ty (sub_Ty A (extend_pr Γ₂ A)) (extend_pair s t)).
Proof.
  simple refine
         (transportf
            (λ z, iso_disp z _ _)
            _
            (iso_disp_comp
               (sub_Ty_path_sub _ (extend_pr_pair _ _))
               (sub_Ty_comp_iso _ _ A))).
  use subtypePath.
  {
    intro ; apply isaprop_is_iso.
  }
  simpl.
  apply id_left.
Defined.

Definition extend_pair_iso_eq_alt
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : extend_pair_iso_mor s t
    =
    pr1 (extend_pair_iso' s t).
Proof.
  unfold extend_pair_iso_mor, extend_pair_iso'.
  use (cartesian_factorisation_unique
         (is_cartesian_comp_disp
            (cartesian_lift_is_cartesian
               (sub_Ty A (extend_pr Γ₂ A))
               (pr1 t · pr1 (# (comprehension_of C) (sub_Ty_mor A s)))
               _)
            (cartesian_lift_is_cartesian
               A
               (extend_pr Γ₂ A)
               _))).
  etrans.
  {
    apply cartesian_factorisation_commutes.
  }
  refine (!_).
  rewrite transportf_iso_disp.
  rewrite !mor_disp_transportf_postwhisker.
  cbn -[sub_Ty_comp_iso sub_Ty_path_sub].
  rewrite assoc_disp_var.
  rewrite transport_f_f.
  etrans.
  {
    do 2 apply maponpaths.
    apply (cartesian_factorisation_commutes
             (is_cartesian_comp_disp
                (disp_cat_of_cleaving C (extendCon Γ₂ A) Γ₁ (extend_pair s t)
                                      (sub_Ty A (extend_pr Γ₂ A)))
                (disp_cat_of_cleaving C Γ₂ (extendCon Γ₂ A) (extend_pr Γ₂ A) A))).
  }
  unfold transportb.
  rewrite mor_disp_transportf_prewhisker.
  rewrite transport_f_f.
  use transportf_transpose_right.
  unfold transportb.
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    pose (cartesian_factorisation_commutes
             (sub_Ty_path_sub_is_cartesian A (extend_pr_pair s t))
             (identity _)
             (transportb
                _
                (id_left _)
                (sub_Ty_mor A s)))
      as p.
    cbn in p.
    rewrite mor_disp_transportf_prewhisker in p.
    exact (transportb_transpose_right p).
  }
  unfold transportb.
  rewrite !transport_f_f.
  apply transportf_set.
  apply (base_category_of C).
Qed.

Definition extend_pair_iso
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : iso_disp
      (identity_iso Γ₁)
      (sub_Ty A s)
      (sub_Ty (sub_Ty A (extend_pr Γ₂ A)) (extend_pair s t)).
Proof.
  use make_iso_disp.
  - exact (extend_pair_iso_mor s t).
  - rewrite extend_pair_iso_eq_alt.
    exact (pr2 (extend_pair_iso' s t)).
Defined.

Definition extend_pair_path
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : sub_Ty A s
    =
    sub_Ty (sub_Ty A (extend_pr Γ₂ A)) (extend_pair s t).
Proof.
  apply path_Ty.
  exact (extend_pair_iso s t).
Defined.

Definition extend_pair_var
           {C : comprehension_category}
           {Γ₁ Γ₂ : Con C}
           {A : Ty Γ₂}
           (s : Sub Γ₁ Γ₂)
           (t : Tm Γ₁ (sub_Ty A s))
  : sub_Tm
      (extend_var Γ₂ A)
      (extend_pair s t)
    =
    transportf (Tm Γ₁) (extend_pair_path s t) t.
Proof.
  refine (_ @ !(path_transportf_Tm _ _)).
  use path_Tm.
  refine (!_).
  use (PullbackArrowUnique'
         _ _
         (pullback_from_sub (sub_Ty A (extend_pr Γ₂ A)) (extend_pair s t)))
  ; cbn -[extend_pair_iso].
  - unfold extend_pair.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (postCompWithPullbackArrow
               _
               _ _ (pullback_from_sub A (extend_pr Γ₂ A)) _ _
               _).
    }
    etrans.
    {
      exact (postCompWithPullbackArrow
               _
               _ _ (pullback_from_sub A (extend_pr Γ₂ A)) _ _
               _).
    }
    refine (!_).
    use (PullbackArrowUnique'
           _ _
           (pullback_from_sub A (extend_pr Γ₂ A))).
    + cbn -[extend_pair_iso].
      rewrite id_right.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply maponpaths.
        exact (maponpaths
                 pr1
                 (disp_functor_comp (comprehension_of C) _ _)).
      }
      etrans.
      {
        refine (!_).
        exact (maponpaths
                 pr1
                 (disp_functor_comp (comprehension_of C) _ _)).
      }
      use path_comprehension.
      * apply extend_pair_iso_path.
      * use transportf_transpose_left.
        apply cartesian_factorisation_commutes.
    + cbn -[extend_pair_iso].
      rewrite id_right.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        refine (!_).
        exact (maponpaths
                 pr1
                 (disp_functor_comp
                    (comprehension_of C) _ _)).
      }
      rewrite assoc'.
      etrans.
      {
        apply maponpaths.
        apply (pr2 (# (comprehension_of C) _)).
      }
      simpl.
      rewrite !assoc.
      rewrite id_right.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply (pr2 t).
      }
      rewrite id_left.
      apply idpath.
  - refine (_ @ pr2 t).
    rewrite !assoc'.
    apply maponpaths.
    refine (pr2 (# (comprehension_of C) (extend_pair_iso s t)) @ _).
    apply id_right.
Qed.
