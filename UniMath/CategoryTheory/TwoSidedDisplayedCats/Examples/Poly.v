(*****************************************************************************************

 Polynomial functors

 Let `C` be a locally cartesian closed category. A polynomial functor from objects `i : C`
 to `j : C` is given by morphisms `i <-- x --> y --> j`. Such morphisms give rise to a
 functor `C/i ⟶ C/j`. More specifically, from a morphism  `f : x --> i`, we get a functor
 `C/i ⟶ C/x` given by pullback. From `g : x --> y` we get a functor `C/x ⟶ C/y` given
 by the dependent product, and from `f : y --> z` we get a functor `C/y ⟶ C/z` given by
 composition. By composing these functors, we get `C/i ⟶ C/j`.

 To make this concrete, a polynomial `I <-- X --> Y --> J` of sets consists of
 - set `I` and `J`
 - a family `S : J → hSet` of shapes
 - a family `P : ∏ (j : J), S j → hSet`
 - a function `n : ∏ (j : J) (s : S j), P j s → I`
 This data represents a functor that sends a family `X : I → hSet` to the family that sends
 a `j : J` to the set `∑ (s : S j), ∏ (p : P j s), X (n j s p)`.

 In this file, we construct the 2-sided displayed category of polynomial functors. We do
 so in multiple steps. We start with the constant 2-sided displayed category over `C` and
 `C`, whose objects are given by `(i ,, y ,, j)``. Over that, we define two 2-sided
 displayed categories
 - the first one adds the morphism `y --> j`
 - the second one adds `x` and the morphism `x --> y`
 Note that the second one is defined in one step, because the displayed morphisms for that
 are given by maps from a certain pullback.

 Then we take the product and we obtain a 2-sided displayed category over `C` and `C`. For
 that one the objects from `i` to `j` are given by `x --> y --> j`. Hence, to get polynomial
 functors, we must add one more displayed category, which adds the morphism `i --> x`.

 *****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.FiberwiseProduct.

Local Open Scope cat.

Section Polynomials.
  Context {C : category}
          (PB : Pullbacks C).

  Definition poly_cod_twosided_disp_cat
    : twosided_disp_cat C C
    := constant_twosided_disp_cat C C C.

  (**
     A polynomial from `i` to `j` looks like `i <-- x --> y --> j`.
     An object over `i` and `j` in [poly_cod_twosided_disp_cat] looks like `i     y    j`.
     This means that we still need to add `x` and the morphisms.
     The objects of the total category of [poly_cod_twosided_disp_cat] are `(i ,, j ,, y)`.

     We first define [poly_cod_mor_twosided_disp_cat] where we add a morphisms `y --> j`.
   *)

  (** * *)
  Definition poly_cod_mor_twosided_disp_cat_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category poly_cod_twosided_disp_cat).
  Proof.
    simple refine (_ ,, _).
    - exact (λ ijy, pr22 ijy --> pr12 ijy).
    - exact (λ ijxy ijy₂ h h' φ, pr22 φ · h' = h · pr12 φ).
  Defined.

  Definition poly_cod_mor_twosided_disp_cat_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category poly_cod_twosided_disp_cat)
        poly_cod_mor_twosided_disp_cat_ob_mor.
  Proof.
    split ; cbn.
    - intros ijy f.
      rewrite id_left, id_right.
      apply idpath.
    - intros ijy₁ ijy₂ ijy₃ φ₁ φ₂ h₁ h₂ h₃ p q.
      rewrite !assoc'.
      rewrite q.
      rewrite !assoc.
      rewrite p.
      apply idpath.
  Qed.

  Definition poly_cod_mor_twosided_disp_cat_data
    : disp_cat_data (total_twosided_disp_category poly_cod_twosided_disp_cat).
  Proof.
    simple refine (_ ,, _).
    - exact poly_cod_mor_twosided_disp_cat_ob_mor.
    - exact poly_cod_mor_twosided_disp_cat_id_comp.
  Defined.

  Proposition poly_cod_mor_twosided_disp_axioms
    : disp_cat_axioms
        (total_twosided_disp_category poly_cod_twosided_disp_cat)
        poly_cod_mor_twosided_disp_cat_data.
  Proof.
    repeat split ; intro ; intros.
    - apply homset_property.
    - apply homset_property.
    - apply homset_property.
    - apply isasetaprop.
      apply homset_property.
  Qed.

  Definition poly_cod_mor_twosided_disp_cat
    : disp_cat (total_twosided_disp_category poly_cod_twosided_disp_cat).
  Proof.
    simple refine (_ ,, _).
    - exact poly_cod_mor_twosided_disp_cat_data.
    - exact poly_cod_mor_twosided_disp_axioms.
  Defined.

  (**
     Now we define another displayed category.
     To an object `i   y   j` we add:
     - an object `x`
     - a morphism `x --> y`
     Note that we do not split this into two separate displayed categories due to how
     morphisms of polynomials are defined.
     This is because a morphism from a polynomial `i₁ <-- x₁ --> y₁ --> j₁` to a
     polynomial `i₂ <-- x₂ --> y₂ --> j₂` consists of
     - a morphism `i₁ --> i₂`
     - a morphism `j₁ --> j₂`
     - a morphism `y₁ --> y₂`
     - a morphism from the pullback of `x₂ --> y₂` and `y₁ --> y₂` to `x₁`.
     For the final part, we use both the added object and morphism.
   *)

  (** * *)
  Definition poly_dom_twosided_disp_ob_mor_data
    : disp_cat_ob_mor (total_twosided_disp_category poly_cod_twosided_disp_cat).
  Proof.
    simple refine (_ ,, _).
    - exact (λ ijy, ∑ (x : C), x --> pr22 ijy).
    - exact (λ ijy₁ ijy₂ xg₁ xg₂ φ,
             ∑ (ζ : PB _ _ _ (pr2 xg₂) (pr22 φ) --> pr1 xg₁),
             ζ · pr2 xg₁ = PullbackPr2 _).
  Defined.

  Definition poly_dom_id
             {ijy : total_twosided_disp_category poly_cod_twosided_disp_cat}
             (xg : poly_dom_twosided_disp_ob_mor_data ijy)
    : xg -->[ identity ijy ] xg.
  Proof.
    refine (PullbackPr1 _ ,, _).
    abstract
      (refine (PullbackSqrCommutes _ @ _) ;
       apply id_right).
  Defined.

  Definition poly_dom_comp_mor₂
             {ijy₁ ijy₂ ijy₃ : total_twosided_disp_category poly_cod_twosided_disp_cat}
             {φ₁ : ijy₁ --> ijy₂}
             {φ₂ : ijy₂ --> ijy₃}
             {xg₁ : poly_dom_twosided_disp_ob_mor_data ijy₁}
             {xg₂ : poly_dom_twosided_disp_ob_mor_data ijy₂}
             {xg₃ : poly_dom_twosided_disp_ob_mor_data ijy₃}
             (ψ : xg₁ -->[ φ₁ ] xg₂)
             (ψ' : xg₂ -->[ φ₂ ] xg₃)
    : PB _ _ _ (pr2 xg₃) (pr22 φ₁ · pr22 φ₂) --> pr1 xg₂.
  Proof.
    simple refine (PullbackArrow _ _ _ _ _ · pr1 ψ').
    - exact (PullbackPr1 _).
    - exact (PullbackPr2 _ · pr22 φ₁).
    - abstract
        (refine (PullbackSqrCommutes _ @ _) ;
         rewrite assoc ;
         apply idpath).
  Defined.

  Definition poly_dom_comp_mor₁
             {ijy₁ ijy₂ ijy₃ : total_twosided_disp_category poly_cod_twosided_disp_cat}
             {φ₁ : ijy₁ --> ijy₂}
             {φ₂ : ijy₂ --> ijy₃}
             {xg₁ : poly_dom_twosided_disp_ob_mor_data ijy₁}
             {xg₂ : poly_dom_twosided_disp_ob_mor_data ijy₂}
             {xg₃ : poly_dom_twosided_disp_ob_mor_data ijy₃}
             (ψ : xg₁ -->[ φ₁ ] xg₂)
             (ψ' : xg₂ -->[ φ₂ ] xg₃)
    : PB _ _ _ (pr2 xg₃) (pr22 φ₁ · pr22 φ₂) --> pr1 xg₁.
  Proof.
    simple refine (PullbackArrow _ _ _ _ _ · pr1 ψ).
    - exact (poly_dom_comp_mor₂ ψ ψ').
    - exact (PullbackPr2 _).
    - abstract
        (unfold poly_dom_comp_mor₂ ;
         rewrite !assoc' ;
         rewrite (pr2 ψ') ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Definition poly_dom_comp
             {ijy₁ ijy₂ ijy₃ : total_twosided_disp_category poly_cod_twosided_disp_cat}
             {φ₁ : ijy₁ --> ijy₂}
             {φ₂ : ijy₂ --> ijy₃}
             {xg₁ : poly_dom_twosided_disp_ob_mor_data ijy₁}
             {xg₂ : poly_dom_twosided_disp_ob_mor_data ijy₂}
             {xg₃ : poly_dom_twosided_disp_ob_mor_data ijy₃}
             (ψ : xg₁ -->[ φ₁ ] xg₂)
             (ψ' : xg₂ -->[ φ₂ ] xg₃)
    : xg₁ -->[ φ₁ · φ₂ ] xg₃.
  Proof.
    simple refine (_ ,, _).
    - exact (poly_dom_comp_mor₁ ψ ψ').
    - abstract
        (unfold poly_dom_comp_mor₁ ;
         cbn ;
         rewrite !assoc' ;
         rewrite (pr2 ψ) ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Definition poly_dom_twosided_disp_cat_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category poly_cod_twosided_disp_cat)
        poly_dom_twosided_disp_ob_mor_data.
  Proof.
    split.
    - exact (λ _ xg, poly_dom_id xg).
    - exact (λ ijy₁ ijy₂ ijy₃ φ₁ φ₂ xg₁ xg₂ xg₃ ψ ψ', poly_dom_comp ψ ψ').
  Defined.

  Definition poly_dom_twosided_disp_cat_data
    : disp_cat_data (total_twosided_disp_category poly_cod_twosided_disp_cat).
  Proof.
    simple refine (_ ,, _).
    - exact poly_dom_twosided_disp_ob_mor_data.
    - exact poly_dom_twosided_disp_cat_id_comp.
  Defined.

  Proposition eq_mor_poly_dom
              {ijy₁ ijy₂ : total_twosided_disp_category poly_cod_twosided_disp_cat}
              {φ : ijy₁ --> ijy₂}
              {xg₁ : poly_dom_twosided_disp_cat_data ijy₁}
              {xg₂ : poly_dom_twosided_disp_cat_data ijy₂}
              {ψ ψ' : xg₁ -->[ φ ] xg₂}
              (p : pr1 ψ = pr1 ψ')
    : ψ = ψ'.
  Proof.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    exact p.
  Qed.

  Proposition transportf_poly_dom_pr1_eq
              {ijy₁ ijy₂ : total_twosided_disp_category poly_cod_twosided_disp_cat}
              {φ φ' : ijy₁ --> ijy₂}
              (p : φ = φ')
              (xg₁ : poly_dom_twosided_disp_cat_data ijy₁)
              (xg₂ : poly_dom_twosided_disp_cat_data ijy₂)
    : PullbackPr1 (PB (pr22 ijy₂) (pr1 xg₂) (pr22 ijy₁) (pr2 xg₂) (pr22 φ')) · pr2 xg₂
      =
      PullbackPr2 (PB (pr22 ijy₂) (pr1 xg₂) (pr22 ijy₁) (pr2 xg₂) (pr22 φ')) · pr22 φ.
  Proof.
    refine (PullbackSqrCommutes _ @ _).
    apply maponpaths.
    induction p.
    apply idpath.
  Qed.

  Proposition transportf_poly_dom_pr1
              {ijy₁ ijy₂ : total_twosided_disp_category poly_cod_twosided_disp_cat}
              {φ φ' : ijy₁ --> ijy₂}
              (p : φ = φ')
              {xg₁ : poly_dom_twosided_disp_cat_data ijy₁}
              {xg₂ : poly_dom_twosided_disp_cat_data ijy₂}
              (ψ : xg₁ -->[ φ ] xg₂)
    : pr1 (transportf (λ z, _ -->[ z ] _) p ψ)
      =
      PullbackArrow
        _ _
        (PullbackPr1 _) (PullbackPr2 _)
        (transportf_poly_dom_pr1_eq p xg₁ xg₂)
      · pr1 ψ.
  Proof.
    induction p ; cbn.
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
    - rewrite PullbackArrow_PullbackPr1.
      rewrite id_left.
      apply idpath.
    - rewrite PullbackArrow_PullbackPr2.
      rewrite id_left.
      apply idpath.
  Qed.

  Proposition poly_dom_twosided_disp_cat_axioms
    : disp_cat_axioms
        (total_twosided_disp_category poly_cod_twosided_disp_cat)
        poly_dom_twosided_disp_cat_data.
  Proof.
    repeat split.
    - intros ijy₁ ijy₂ φ xg₁ xg₂ ψ.
      unfold transportb.
      use eq_mor_poly_dom.
      rewrite transportf_poly_dom_pr1 ; cbn.
      etrans.
      {
        apply PullbackArrow_PullbackPr1.
      }
      unfold poly_dom_comp_mor₂.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      + rewrite !PullbackArrow_PullbackPr1.
        apply idpath.
      + rewrite !PullbackArrow_PullbackPr2.
        cbn.
        rewrite id_right.
        apply idpath.
    - intros ijy₁ ijy₂ φ xg₁ xg₂ ψ.
      unfold transportb.
      use eq_mor_poly_dom.
      rewrite transportf_poly_dom_pr1 ; cbn.
      unfold poly_dom_comp_mor₁.
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      + rewrite !PullbackArrow_PullbackPr1.
        etrans.
        {
          apply PullbackArrow_PullbackPr1.
        }
        apply idpath.
      + rewrite !PullbackArrow_PullbackPr2.
        apply idpath.
    - intros ijy₁ ijy₂ ijy₃ ijy₄ φ₁ φ₂ φ₃ xg₁ xg₂ xg₃ xg₄ ψ₁ ψ₂ ψ₃.
      unfold transportb.
      use eq_mor_poly_dom.
      rewrite transportf_poly_dom_pr1 ; cbn.
      unfold poly_dom_comp_mor₁.
      do 2 refine (_ @ assoc' _ _ _).
      apply maponpaths_2.
      use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
      + rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr1.
        refine (assoc _ _ _ @ _) ; cbn.
        do 2 refine (_ @ assoc' _ _ _).
        apply maponpaths_2.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
        * rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr1.
          refine (assoc _ _ _ @ _).
          refine (_ @ assoc' _ _ _).
          apply maponpaths_2.
          use (MorphismsIntoPullbackEqual (isPullback_Pullback _)).
          ** rewrite !assoc'.
             rewrite !PullbackArrow_PullbackPr1.
             apply idpath.
          ** rewrite !assoc'.
             rewrite !PullbackArrow_PullbackPr2.
             refine (assoc _ _ _ @ _ @ assoc' _ _ _).
             rewrite !PullbackArrow_PullbackPr2.
             cbn.
             rewrite !assoc'.
             apply idpath.
        * rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr2.
          do 2 refine (_ @ assoc' _ _ _).
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite !PullbackArrow_PullbackPr2.
          apply idpath.
      + cbn.
        rewrite !assoc'.
        rewrite !PullbackArrow_PullbackPr2.
        apply idpath.
    - intros xy₁ xy₂ φ xg₁ xg₂.
      use isaset_total2.
      {
        apply homset_property.
      }
      intro.
      apply isasetaprop.
      apply homset_property.
  Qed.

  Definition poly_dom_twosided_disp_cat
    : disp_cat (total_twosided_disp_category poly_cod_twosided_disp_cat).
  Proof.
    simple refine (_ ,, _).
    - exact poly_dom_twosided_disp_cat_data.
    - exact poly_dom_twosided_disp_cat_axioms.
  Defined.

  Definition poly_dom_cod_mor
    : disp_cat (total_twosided_disp_category poly_cod_twosided_disp_cat)
    := dirprod_disp_cat
         poly_dom_twosided_disp_cat
         poly_cod_mor_twosided_disp_cat.

  Definition TODO { A : UU } : A.
  Admitted.

  Definition poly_disp_cat_ob_mor
    : disp_cat_ob_mor (total_category poly_dom_cod_mor).
  Proof.
    simple refine (_ ,, _).
    - exact (λ ijyxgh, pr112 ijyxgh --> pr11 ijyxgh).
    - exact (λ _ _ f f' φ,
             pr112 φ · f · pr11 φ
             =
             PullbackPr1 _ · f').
  Defined.

  Proposition poly_disp_cat_id_comp
    : disp_cat_id_comp
        (total_category poly_dom_cod_mor)
        poly_disp_cat_ob_mor.
  Proof.
    split.
    - cbn ; intros.
      rewrite id_right.
      apply idpath.
    - cbn ; intros.
  Admitted.

  Definition poly_disp_cat_data
    : disp_cat_data (total_category poly_dom_cod_mor).
  Proof.
    simple refine (_ ,, _).
    - exact poly_disp_cat_ob_mor.
    - apply TODO.
  Defined.

  Definition poly_disp_cat
    : disp_cat (total_category poly_dom_cod_mor).
  Proof.
    simple refine (_ ,, _).
    - exact poly_disp_cat_data.
    - apply TODO.
  Defined.

  Definition poly_twosided_disp_cat
    : twosided_disp_cat C C
    := sigma_twosided_disp_cat
         poly_cod_twosided_disp_cat
         (sigma_disp_cat poly_disp_cat).

  Definition poly_functor
             (i j : C)
    : UU
    := poly_twosided_disp_cat i j.

  Definition poly_functor_dom
             {i j : C}
             (P : poly_functor i j)
    : C
    := pr1 (pr112 P).

  Definition poly_functor_cod
             {i j : C}
             (P : poly_functor i j)
    : C
    := pr1 P.

  Definition poly_functor_left
             {i j : C}
             (P : poly_functor i j)
    : poly_functor_dom P --> i
    := pr22 P.

  Definition poly_functor_middle
             {i j : C}
             (P : poly_functor i j)
    : poly_functor_dom P --> poly_functor_cod P
    := pr2 (pr112 P).

  Definition poly_functor_right
             {i j : C}
             (P : poly_functor i j)
    : poly_functor_cod P --> j
    := pr212 P.

  Definition poly_functor_middle_right
             {i j : C}
             (P : poly_functor i j)
    : poly_functor_dom P --> j
    := poly_functor_middle P · poly_functor_right P.

  Definition make_poly_functor
             {i j : C}
             {x y : C}
             (f : x --> i)
             (g : x --> y)
             (h : y --> j)
    : poly_functor i j
    := y ,, (((x ,, g) ,, h) ,, f).

  Definition poly_square
             {i₁ i₂ j₁ j₂ : C}
             (φ : i₁ --> i₂)
             (ψ : j₁ --> j₂)
             (P : poly_functor i₁ j₁)
             (Q : poly_functor i₂ j₂)
    : UU
    := P -->[ φ ][ ψ ] Q.

  Definition poly_square_cod_mor
             {i₁ i₂ j₁ j₂ : C}
             {φ : i₁ --> i₂}
             {ψ : j₁ --> j₂}
             {P : poly_functor i₁ j₁}
             {Q : poly_functor i₂ j₂}
             (s : poly_square φ ψ P Q)
    : poly_functor_cod P --> poly_functor_cod Q
    := pr1 s.

  Proposition poly_square_right
              {i₁ i₂ j₁ j₂ : C}
              {φ : i₁ --> i₂}
              {ψ : j₁ --> j₂}
              {P : poly_functor i₁ j₁}
              {Q : poly_functor i₂ j₂}
              (s : poly_square φ ψ P Q)
    : poly_square_cod_mor s · poly_functor_right Q
      =
      poly_functor_right P · ψ.
  Proof.
    exact (pr212 s).
  Qed.

  Definition poly_square_pb
             {i₁ i₂ j₁ j₂ : C}
             {φ : i₁ --> i₂}
             {ψ : j₁ --> j₂}
             {P : poly_functor i₁ j₁}
             {Q : poly_functor i₂ j₂}
             (s : poly_square φ ψ P Q)
    : Pullback (poly_functor_middle Q) (poly_square_cod_mor s)
    := PB _ _ _ (poly_functor_middle Q) (poly_square_cod_mor s).

  Definition poly_square_dom_mor
             {i₁ i₂ j₁ j₂ : C}
             {φ : i₁ --> i₂}
             {ψ : j₁ --> j₂}
             {P : poly_functor i₁ j₁}
             {Q : poly_functor i₂ j₂}
             (s : poly_square φ ψ P Q)
    : poly_square_pb s --> poly_functor_dom P
    := pr1 (pr112 s).

  Proposition poly_square_left
              {i₁ i₂ j₁ j₂ : C}
              {φ : i₁ --> i₂}
              {ψ : j₁ --> j₂}
              {P : poly_functor i₁ j₁}
              {Q : poly_functor i₂ j₂}
              (s : poly_square φ ψ P Q)
    : poly_square_dom_mor s · poly_functor_left P · φ
      =
      PullbackPr1 _ · poly_functor_left Q.
  Proof.
    exact (pr22 s).
  Qed.

  Proposition poly_square_middle
              {i₁ i₂ j₁ j₂ : C}
              {φ : i₁ --> i₂}
              {ψ : j₁ --> j₂}
              {P : poly_functor i₁ j₁}
              {Q : poly_functor i₂ j₂}
              (s : poly_square φ ψ P Q)
    : poly_square_dom_mor s · poly_functor_middle P = PullbackPr2 _.
  Proof.
    exact (pr2 (pr112 s)).
  Qed.

  Definition make_poly_square
             {i₁ i₂ j₁ j₂ : C}
             {φ : i₁ --> i₂}
             {ψ : j₁ --> j₂}
             {P : poly_functor i₁ j₁}
             {Q : poly_functor i₂ j₂}
             (ζ : poly_functor_cod P --> poly_functor_cod Q)
             (ξ : PB _ _ _ (poly_functor_middle Q) ζ --> poly_functor_dom P)
             (p₁ : ξ · poly_functor_middle P = PullbackPr2 _)
             (p₂ : ζ · poly_functor_right Q = poly_functor_right P · ψ)
             (p₃ : ξ · poly_functor_left P · φ = PullbackPr1 _ · poly_functor_left Q)
    : poly_square φ ψ P Q
    := ζ ,, (((ξ ,, p₁) ,, p₂) ,, p₃).

  Definition id_poly_functor
             (i : C)
    : poly_functor i i.
  Proof.
    use make_poly_functor.
    - exact i.
    - exact i.
    - apply identity.
    - apply identity.
    - apply identity.
  Defined.



  Definition comp_poly_functor
             {i j k : C}
             (P₁ : poly_functor i j)
             (P₂ : poly_functor j k)
    : poly_functor i k.
  Proof.
    pose (pb := PB _ _ _ (poly_functor_left P₂) (poly_functor_middle_right P₁)).
    use make_poly_functor.
    - exact pb.
    - exact (poly_functor_cod P₂).
    - exact (PullbackPr2 pb · poly_functor_left P₁).
    - exact (PullbackPr1 pb · poly_functor_middle _).
    - exact (poly_functor_right P₂).
  Defined.

  Definition poly_square_lunitor
             {i j : C}
             (P : poly_functor i j)
    : poly_square
        (identity _)
        (identity _)
        (comp_poly_functor (id_poly_functor i) P)
        P.
  Proof.
    use make_poly_square.
    - apply identity.
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr1 _ · poly_functor_left P).
      + abstract
          (unfold poly_functor_middle_right ; cbn ;
           rewrite !id_right ;
           apply idpath).
    - cbn.
      admit.
    - cbn.
      rewrite id_right.
      admit.
    - cbn.
      rewrite !id_right.
      rewrite PullbackArrow_PullbackPr2.
  Admitted.

  Definition poly_square_runitor
             {i j : C}
             (P : poly_functor i j)
    : poly_square
        (identity _)
        (identity _)
        (comp_poly_functor P (id_poly_functor j))
        P.
  Proof.
    use make_poly_square.
    - cbn.
      Check poly_functor_right P.
      admit.
    - cbn.
      use PullbackArrow.
      + refine (PullbackPr2 _).
      + exact (PullbackPr1 _).
      + rewrite !id_right.
        unfold poly_functor_middle_right.
        rewrite !assoc.
        rewrite PullbackSqrCommutes.
        cbn.
        refine (_ @ !(PullbackSqrCommutes _)).
        cbn.
      Check poly_functor_right P.
      apply identity.
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr1 _ · poly_functor_left P).
      + abstract
          (unfold poly_functor_middle_right ; cbn ;
           rewrite !id_right ;
           apply idpath).
    - abstract
        (cbn ;
         rewrite !assoc ;
         rewrite PullbackArrow_PullbackPr1 ;
         refine (PullbackSqrCommutes _ @ _) ;
         apply id_right).
    - abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite !id_right ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.




  Definition comp_poly_functor
             {i j k : C}
             (P₁ : poly_functor i j)
             (P₂ : poly_functor j k)
    : poly_functor i k.
  Proof.
    pose (pb := PB _ _ _ (poly_functor_left P₂) (poly_functor_middle_right P₁)).
    use make_poly_functor.
    - exact pb.
    - exact (poly_functor_dom P₂).
    - exact (PullbackPr2 pb · poly_functor_left P₁).
    - exact (PullbackPr1 pb).
    - exact (poly_functor_middle_right P₂).
  Defined.

  Definition poly_square_lunitor
             {i j : C}
             (P : poly_functor i j)
    : poly_square
        (identity _)
        (identity _)
        (comp_poly_functor (id_poly_functor i) P)
        P.
  Proof.
    use make_poly_square.
    - exact (poly_functor_middle P).
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr1 _ · poly_functor_left P).
      + abstract
          (unfold poly_functor_middle_right ; cbn ;
           rewrite !id_right ;
           apply idpath).
    - cbn.
      rewrite PullbackArrow_PullbackPr1.
      admit.
    - cbn.
      rewrite id_right.
      apply idpath.
    - cbn.
      rewrite !id_right.
      rewrite PullbackArrow_PullbackPr2.
      apply idpath.
  Admitted.

  Definition poly_square_runitor
             {i j : C}
             (P : poly_functor i j)
    : poly_square
        (identity _)
        (identity _)
        (comp_poly_functor P (id_poly_functor j))
        P.
  Proof.
    use make_poly_square.
    - cbn.
      Check poly_functor_right P.
      admit.
    - cbn.
      use PullbackArrow.
      + refine (PullbackPr2 _).
      + exact (PullbackPr1 _).
      + rewrite !id_right.
        unfold poly_functor_middle_right.
        rewrite !assoc.
        rewrite PullbackSqrCommutes.
        cbn.
        refine (_ @ !(PullbackSqrCommutes _)).
        cbn.
      Check poly_functor_right P.
      apply identity.
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr1 _ · poly_functor_left P).
      + abstract
          (unfold poly_functor_middle_right ; cbn ;
           rewrite !id_right ;
           apply idpath).
    - abstract
        (cbn ;
         rewrite !assoc ;
         rewrite PullbackArrow_PullbackPr1 ;
         refine (PullbackSqrCommutes _ @ _) ;
         apply id_right).
    - abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite !id_right ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.




  Definition comp_poly_functor
             {i j k : C}
             (P₁ : poly_functor i j)
             (P₂ : poly_functor j k)
    : poly_functor i k.
  Proof.
    pose (pb := PB _ _ _ (poly_functor_left P₂) (poly_functor_middle_right P₁)).
    use make_poly_functor.
    - exact pb.
    - exact (poly_functor_cod P₂).
    - exact (PullbackPr2 pb · poly_functor_left P₁).
    - exact (PullbackPr1 pb · poly_functor_middle P₂).
    - exact (poly_functor_right P₂).
  Defined.

  Definition poly_square_lunitor
             {i j : C}
             (P : poly_functor i j)
    : poly_square
        (identity _)
        (identity _)
        (comp_poly_functor (id_poly_functor i) P)
        P.
  Proof.
    use make_poly_square.
    - cbn.
      apply identity.
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr1 _ · poly_functor_left P).
      + abstract
          (unfold poly_functor_middle_right ; cbn ;
           rewrite !id_right ;
           apply idpath).
    - abstract
        (cbn ;
         rewrite !assoc ;
         rewrite PullbackArrow_PullbackPr1 ;
         refine (PullbackSqrCommutes _ @ _) ;
         apply id_right).
    - abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite !id_right ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.

  Definition poly_square_runitor
             {i j : C}
             (P : poly_functor i j)
    : poly_square
        (identity _)
        (identity _)
        (comp_poly_functor P (id_poly_functor j))
        P.
  Proof.
    use make_poly_square.
    - cbn.
      Check poly_functor_right P.
      admit.
    - cbn.
      use PullbackArrow.
      + refine (PullbackPr2 _).
      + exact (PullbackPr1 _).
      + rewrite !id_right.
        unfold poly_functor_middle_right.
        rewrite !assoc.
        rewrite PullbackSqrCommutes.
        cbn.
        refine (_ @ !(PullbackSqrCommutes _)).
        cbn.
      Check poly_functor_right P.
      apply identity.
    - use PullbackArrow.
      + exact (PullbackPr1 _).
      + exact (PullbackPr1 _ · poly_functor_left P).
      + abstract
          (unfold poly_functor_middle_right ; cbn ;
           rewrite !id_right ;
           apply idpath).
    - abstract
        (cbn ;
         rewrite !assoc ;
         rewrite PullbackArrow_PullbackPr1 ;
         refine (PullbackSqrCommutes _ @ _) ;
         apply id_right).
    - abstract
        (cbn ;
         rewrite id_left, id_right ;
         apply idpath).
    - abstract
        (cbn ;
         rewrite !id_right ;
         rewrite PullbackArrow_PullbackPr2 ;
         apply idpath).
  Defined.
