Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.ContravariantFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Fibrations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.CodomainFibration.Pullback.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** If: locally univalent and all 2-cells invertible, then local fibration *)
Section LocalCleavingCodomain.
  Context {B : bicat}
          (HB : is_univalent_2_1 B)
          (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                   is_invertible_2cell x)
          {X Y : B}
          {dX : (cod_prod_disp_bicat B) X}
          {dY : (cod_prod_disp_bicat B) Y}
          {f g : X --> Y}
          (pg : dX -->[ g] dY)
          (p : f ==> g).

  Definition lift_dep_cod
    : dX -->[ f] dY.
  Proof.
    use tpair.
    - exact (pr1 pg).
    - exact (_ ◃ p • pr2 pg).
  Defined.

  Definition lift_dep_cod_cell
    : lift_dep_cod ==>[ p] pg.
  Proof.
    use tpair.
    - exact (id₂ _).
    - abstract
        (cbn ;
         rewrite id2_rwhisker, id2_right ;
         apply idpath).
  Defined.

  Definition lift_dep_cod_cell_is_cartesian_2cell_lift
             {h : X --> Y}
             {ph : dX -->[ h] dY}
             {q : h ==> f}
             (β : ph ==>[ q • p] pg)
    : ph ==>[ q ] lift_dep_cod.
  Proof.
    use tpair.
    - exact (pr1 β).
    - abstract
        (simpl ;
         pose (pr2 β) as r ;
         cbn in r ;
         rewrite r ;
         rewrite <- lwhisker_vcomp ;
         rewrite !vassocl ;
         apply idpath).
  Defined.

  Definition lift_dep_cod_cell_is_cartesian_2cell_prop
             {h : X --> Y}
             {ph : dX -->[ h] dY}
             {q : h ==> f}
             (β : ph ==>[ q • p] pg)
    : lift_dep_cod_cell_is_cartesian_2cell_lift β •• lift_dep_cod_cell
      =
      β.
  Proof.
    use subtypePath.
    { intro ; apply B. }
    apply id2_right.
  Qed.

  Definition lift_dep_cod_cell_is_cartesian_2cell
    : is_cartesian_2cell (cod_prod_disp_bicat B) lift_dep_cod_cell.
  Proof.
    intros h ph q β.
    apply iscontraprop1.
    - abstract
        (apply invproofirrelevance ;
         intros x y ;
         use subtypePath ; [ intro ; apply cod_prod_disp_bicat | ] ;
         use subtypePath ; [ intro ; apply B | ] ;
         refine (!(id2_right _) @ _ @ id2_right _) ;
         exact (maponpaths pr1 (pr2 x) @ !(maponpaths pr1 (pr2 y)))).
    - use tpair.
      + exact (lift_dep_cod_cell_is_cartesian_2cell_lift β).
      + exact (lift_dep_cod_cell_is_cartesian_2cell_prop β).
  Defined.
End LocalCleavingCodomain.

Definition cod_local_cleaving
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
  : local_cleaving (cod_prod_disp_bicat B).
Proof.
  intros X Y dX dY f g pg p.
  use tpair.
  - exact (lift_dep_cod pg p).
  - use tpair.
    + exact (lift_dep_cod_cell pg p).
    + exact (lift_dep_cod_cell_is_cartesian_2cell pg p).
Defined.

(*
Definition test
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {X Y : B}
           {dX : (cod_prod_disp_bicat B) X}
           {dY : (cod_prod_disp_bicat B) Y}
           {f g : X --> Y}
           {ff : dX -->[ f ] dY}
           {gg : dX -->[ g ] dY}
           {p : f ==> g}
           (pp : ff ==>[ p ] gg)
           (hpp : is_invertible_2cell (pr1 pp))
  : is_cartesian_2cell (cod_prod_disp_bicat B) pp.
Proof.
  intros h ph q qq.
  apply iscontraprop1.
  - apply invproofirrelevance.
    intros x y.
    use subtypePath ; [ intro ; apply cod_prod_disp_bicat | ].
    use subtypePath ; [ intro ; apply B | ].
    pose (maponpaths pr1 (pr2 x) @ !(maponpaths pr1 (pr2 y))) as r.
    cbn in r.
    use (vcomp_rcancel (pr1 pp)).
    + exact hpp.
    + exact r.
  - use tpair.
    + use tpair.
      * exact (pr1 qq • hpp^-1).
      * abstract
          (simpl ;
           pose (pr2 pp) as d ;
           cbn in d ;
           rewrite <- rwhisker_vcomp ;
           rewrite !vassocr ;
           use vcomp_move_R_Mp ; is_iso ;
           cbn ;
           rewrite !vassocl ;
           rewrite d ; clear d ;
           pose (pr2 qq) as d ;
           cbn in d ;
           rewrite d ;
           rewrite !vassocr ;
           rewrite lwhisker_vcomp ;
           apply idpath).
    + abstract
        (use subtypePath ; [ intro ; apply B | ] ;
         cbn ;
         rewrite !vassocl ;
         rewrite vcomp_lid ;
         apply id2_right).
Defined.

Definition test2
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {X Y : B}
           {dX : (cod_prod_disp_bicat B) X}
           {dY : (cod_prod_disp_bicat B) Y}
           {f g : X --> Y}
           {ff : dX -->[ f ] dY}
           {gg : dX -->[ g ] dY}
           {p : f ==> g}
           (pp : ff ==>[ p ] gg)
           (hpp : is_cartesian_2cell (cod_prod_disp_bicat B) pp)
  : is_invertible_2cell (pr1 pp).
Proof.
  unfold is_cartesian_2cell in hpp.
  pose (hpp g gg) as i.
  simpl in i.
  cbn in i.
  use make_is_invertible_2cell.
  - simpl in i.
    cbn in i.
    cbn in hpp.
    simpl in hpp.
 *)

(** Left whiskering preserves cartesia 1-cells *)
Definition cod_lwhisker_lift
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
           {X Y Z : B}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {dZ : cod_prod_disp_bicat B Z}
           {f : X --> Y}
           {g₁ g₂ : Y --> Z}
           {pf : dX -->[ f] dY}
           {pg₁ : dY -->[ g₁] dZ}
           {pg₂ : dY -->[ g₂] dZ}
           {p : g₁ ==> g₂}
           (pp : pg₁ ==>[ p] pg₂)
           {h : X --> Z}
           {ph : dX -->[ h] dZ}
           {q : h ==> f · g₁}
           (qq : ph ==>[ q • (f ◃ p)] pf;; pg₂)
  : pr1 ph ==> pr1 (pf;; pg₁)
  := pr1 qq • (pr1 pf ◃ (inv_B _ _ _ _ (pr1 pp))^-1).

Definition cod_lwhisker_lift_homot
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
           {X Y Z : B}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {dZ : cod_prod_disp_bicat B Z}
           {f : X --> Y}
           {g₁ g₂ : Y --> Z}
           {pf : dX -->[ f] dY}
           {pg₁ : dY -->[ g₁] dZ}
           {pg₂ : dY -->[ g₂] dZ}
           {p : g₁ ==> g₂}
           (pp : pg₁ ==>[ p] pg₂)
           (hp : is_cartesian_2cell (cod_prod_disp_bicat B) pp)
           {h : X --> Z}
           {ph : dX -->[ h] dZ}
           {q : h ==> f · g₁}
           (qq : ph ==>[ q • (f ◃ p)] pf;; pg₂)
  : coherent_homot q (cod_lwhisker_lift HB inv_B pp qq).
Proof.
  unfold coherent_homot, cod_lwhisker_lift.
  cbn.
  pose (r1 := pr2 qq).
  pose (r2 := pr2 pp).
  cbn in r1, r2.
  etrans.
  {
    rewrite <- rwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    exact r1.
  }
  clear r1.
  rewrite <- lwhisker_vcomp.
  rewrite !vassocl.
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite lwhisker_lwhisker.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite <- vcomp_whisker.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite <- lwhisker_lwhisker_rassociator.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite lwhisker_vcomp.
    rewrite <- r2.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite rwhisker_lwhisker.
    rewrite !vassocl.
    apply idpath.
  }
  refine (_ @ id2_right _).
  apply maponpaths.
  rewrite rwhisker_vcomp, lwhisker_vcomp.
  refine (_ @ id2_rwhisker _ _).
  apply maponpaths.
  refine (_ @ lwhisker_id2 _ _).
  apply maponpaths.
  apply inv_B.
Qed.

Definition cod_lwhisker_lift_help
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
           {X Y Z : B}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {dZ : cod_prod_disp_bicat B Z}
           {f : X --> Y}
           {g₁ g₂ : Y --> Z}
           {pf : dX -->[ f] dY}
           {pg₁ : dY -->[ g₁] dZ}
           {pg₂ : dY -->[ g₂] dZ}
           {p : g₁ ==> g₂}
           (pp : pg₁ ==>[ p] pg₂)
           (hp : is_cartesian_2cell (cod_prod_disp_bicat B) pp)
           {h : X --> Z}
           {ph : dX -->[ h] dZ}
           {q : h ==> f · g₁}
           (qq : ph ==>[ q • (f ◃ p)] pf;; pg₂)
  : make_disp_2cell_cod
      (cod_lwhisker_lift HB inv_B pp qq)
      (cod_lwhisker_lift_homot HB inv_B pp hp qq)
    •• (pf ◃◃ pp)
    =
    qq.
Proof.
  use subtypePath.
  { intro. apply B. }
  cbn.
  unfold cod_lwhisker_lift.
  rewrite !vassocl.
  refine (_ @ id2_right _).
  apply maponpaths.
  etrans.
  {
    apply lwhisker_vcomp.
  }
  refine (_ @ lwhisker_id2 _ _).
  apply maponpaths.
  apply inv_B.
Qed.

Definition cod_lwhisker_cartesian
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
  : lwhisker_cartesian (cod_prod_disp_bicat B).
Proof.
  intros X Y Z dX dY dZ f g₁ g₂ pf pg₁ pg₂ p pp hp.
  intros h ph q qq.
  apply iscontraprop1.
  - abstract
      (apply invproofirrelevance ;
       intros x y ;
       use subtypePath ; [ intro ; apply cod_prod_disp_bicat | ] ;
       use subtypePath ; [ intro ; apply B | ] ;
       pose (maponpaths pr1 (pr2 x) @ !(maponpaths pr1 (pr2 y))) as r ;
       use (vcomp_rcancel (pr1 pf ◃ pr1 pp)); try apply inv_B ;
       exact r).
  - use tpair.
    + use make_disp_2cell_cod.
      * exact (cod_lwhisker_lift HB inv_B pp qq).
      * exact (cod_lwhisker_lift_homot HB inv_B pp hp qq).
    + exact (cod_lwhisker_lift_help HB inv_B pp hp qq).
Defined.

(** Right whiskering preserves cartesia 1-cells *)
Definition cod_rwhisker_lift
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
           {X Y Z : B}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {dZ : cod_prod_disp_bicat B Z}
           {f₁ f₂ : B ⟦ X, Y ⟧}
           {g : B ⟦ Y, Z ⟧}
           {pf₁ : dX -->[ f₁] dY}
           {pf₂ : dX -->[ f₂] dY}
           {pg : dY -->[ g] dZ}
           {p : f₁ ==> f₂}
           (pp : pf₁ ==>[ p] pf₂)
           {h : B ⟦ X, Z ⟧}
           {ph : dX -->[ h] dZ}
           {q : h ==> f₁ · g}
           (qq : ph ==>[ q • (p ▹ g)] pf₂;; pg)
  : pr1 ph ==> pr1 (pf₁;; pg)
  := pr1 qq • ((inv_B _ _ _ _ (pr1 pp))^-1 ▹ pr1 pg).

Definition cod_rwhisker_lift_homot
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
           {X Y Z : B}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {dZ : cod_prod_disp_bicat B Z}
           {f₁ f₂ : B ⟦ X, Y ⟧}
           {g : B ⟦ Y, Z ⟧}
           {pf₁ : dX -->[ f₁] dY}
           {pf₂ : dX -->[ f₂] dY}
           {pg : dY -->[ g] dZ}
           {p : f₁ ==> f₂}
           (pp : pf₁ ==>[ p] pf₂)
           (hp : is_cartesian_2cell (cod_prod_disp_bicat B) pp)
           {h : B ⟦ X, Z ⟧}
           {ph : dX -->[ h] dZ}
           {q : h ==> f₁ · g}
           (qq : ph ==>[ q • (p ▹ g)] pf₂;; pg)
  : coherent_homot q (cod_rwhisker_lift HB inv_B pp qq).
Proof.
  unfold coherent_homot, cod_rwhisker_lift.
  cbn.
  pose (r1 := pr2 qq).
  pose (r2 := pr2 pp).
  cbn in r1, r2.
  etrans.
  {
    rewrite <- rwhisker_vcomp.
    rewrite !vassocr.
    apply maponpaths_2.
    exact r1.
  }
  clear r1.
  rewrite <- lwhisker_vcomp.
  rewrite !vassocl.
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite rwhisker_lwhisker.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite rwhisker_vcomp.
    rewrite <- r2.
    rewrite <- rwhisker_vcomp.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite vcomp_whisker.
    rewrite !vassocl.
    apply idpath.
  }
  apply maponpaths.
  etrans.
  {
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker.
    rewrite !vassocl.
    apply idpath.
  }
  refine (_ @ id2_right _).
  apply maponpaths.
  rewrite !rwhisker_vcomp.
  refine (_ @ id2_rwhisker _ _).
  apply maponpaths.
  refine (_ @ id2_rwhisker _ _).
  apply maponpaths.
  apply inv_B.
Qed.

Definition cod_rwhisker_lift_help
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
           {X Y Z : B}
           {dX : cod_prod_disp_bicat B X}
           {dY : cod_prod_disp_bicat B Y}
           {dZ : cod_prod_disp_bicat B Z}
           {f₁ f₂ : B ⟦ X, Y ⟧}
           {g : B ⟦ Y, Z ⟧}
           {pf₁ : dX -->[ f₁] dY}
           {pf₂ : dX -->[ f₂] dY}
           {pg : dY -->[ g] dZ}
           {p : f₁ ==> f₂}
           (pp : pf₁ ==>[ p] pf₂)
           (hp : is_cartesian_2cell (cod_prod_disp_bicat B) pp)
           {h : B ⟦ X, Z ⟧}
           {ph : dX -->[ h] dZ}
           {q : h ==> f₁ · g}
           (qq : ph ==>[ q • (p ▹ g)] pf₂;; pg)
  : make_disp_2cell_cod
      (cod_rwhisker_lift HB inv_B pp qq)
      (cod_rwhisker_lift_homot HB inv_B pp hp qq)
    •• (pp ▹▹ pg)
    = qq.
Proof.
  use subtypePath.
  { intro. apply B. }
  cbn.
  unfold cod_rwhisker_lift.
  rewrite !vassocl.
  refine (_ @ id2_right _).
  apply maponpaths.
  etrans.
  {
    apply rwhisker_vcomp.
  }
  refine (_ @ id2_rwhisker _ _).
  apply maponpaths.
  apply inv_B.
Qed.

Definition cod_rwhisker_cartesian
           {B : bicat}
           (HB : is_univalent_2_1 B)
           (inv_B : ∏ (a b : B) (f g : a --> b) (x : f ==> g),
                    is_invertible_2cell x)
  : rwhisker_cartesian (cod_prod_disp_bicat B).
Proof.
  intros X Y Z dX dY dZ f₁ f₂ g pf₁ pf₂ pg p pp hp.
  intros h ph q qq.
  apply iscontraprop1.
  - abstract
      (apply invproofirrelevance ;
       intros x y ;
       use subtypePath ; [ intro ; apply cod_prod_disp_bicat | ] ;
       use subtypePath ; [ intro ; apply B | ] ;
       pose (maponpaths pr1 (pr2 x) @ !(maponpaths pr1 (pr2 y))) as r ;
       use (vcomp_rcancel (pr1 pp ▹ pr1 pg)); try apply inv_B ;
       exact r).
  - use tpair.
    + use make_disp_2cell_cod.
      * exact (cod_rwhisker_lift HB inv_B pp qq).
      * exact (cod_rwhisker_lift_homot HB inv_B pp hp qq).
    + exact (cod_rwhisker_lift_help HB inv_B pp hp qq).
Defined.

Section PullBackToCartesian.
  Context {X Y Z : one_types}
          {f : X --> Z} {g : Y --> Z}
          {P : one_types}
          {p : P --> X} {q : P --> Y}
          {c : ∏ (z : (P : one_type)), f(p z) = g(q z)}
          (hP : is_pb f g P p q c).

  Definition pb_to_cartesian_lift
             {Q : one_types}
             {dQ : (cod_prod_disp_bicat one_types) Q}
             {h : one_types ⟦ Q, X ⟧}
             (gg : dQ -->[ h · f] make_ar g)
    : lift_1cell
        (cod_prod_disp_bicat one_types)
        (@make_disp_1cell_cod
           one_types
           X Z f
           (make_ar p)
           (make_ar g)
           q
           c)
        gg.
  Proof.
    use tpair.
    - use tpair.
      + exact (is_pb_ump hP (pr2 gg)).
      + exact (invhomot (pr1_is_pb_ump hP (pr2 gg))).
    - use tpair.
      + use tpair.
        * exact (pr2_is_pb_ump hP (pr2 gg)).
        * abstract
            (use funextsec ;
             intro z ;
             simpl ;
             cbn ;
             cbn ; unfold homotcomp, homotfun, invhomot, funhomotsec ; cbn ;
             refine (maponpaths (λ z, z @ _) (pathscomp0rid _) @ _) ;
             refine (!(path_assoc _ _ _) @ _) ;
             refine (maponpaths (λ z, _ @ z) (commute_is_pb_ump hP (pr2 gg) z) @ _) ;
             refine (maponpaths (λ z, z @ _) (pathscomp0rid _) @ _) ;
             refine (path_assoc _ _ _ @ _) ;
             refine (maponpaths (λ z, z @ _) (!(maponpathscomp0 _ _ _)) @ _) ;
             refine (maponpaths
                       (λ z, z @ _)
                       (maponpaths (maponpaths f) (pathsinv0l _))
                       @ _) ;
             apply idpath).
      + apply disp_locally_groupoid_cod_one_types.
  Defined.

  Definition pb_to_cartesian_lift_2cell_help
             {Q : one_types}
             {dQ : (cod_prod_disp_bicat one_types) Q}
             {h₁ h₂ : one_types ⟦ Q, X ⟧}
             {p₁ : dQ -->[ h₁ · f] make_ar g}
             {p₂ : dQ -->[ h₂ · f] make_ar g}
             (σ : h₁ ==> h₂)
             (σσ : p₁ ==>[ σ ▹ (f : one_types ⟦ X , Z ⟧)] p₂)
    : ∏ (z : (dom dQ : one_type)),
      c (is_pb_ump hP (pr2 p₂) z)
      @ maponpaths g (pr2_is_pb_ump hP (pr2 p₂) z @ ! pr1 σσ z)
      =
      maponpaths f (pr1_is_pb_ump hP (pr2 p₂) z @ ! σ (pr2 dQ z))
      @ pr2 p₁ z.
  Proof.
    intro z.
    etrans.
    {
      apply maponpaths.
      apply maponpathscomp0.
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (commute_is_pb_ump hP (pr2 p₂) z).
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!_).
    use hornRotation.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (!_).
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply pathsinv0inv0.
      }
      exact (eqtohomot (pr2 σσ) z).
    }
    unfold homotcomp, funhomotsec, homotfun.
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        simpl ; cbn.
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply maponpaths.
      apply pathsinv0l.
    }
    apply idpath.
  Qed.

  Definition pb_to_cartesian_lift_2cell
             {Q : one_types}
             {dQ : (cod_prod_disp_bicat one_types) Q}
             {h₁ h₂ : one_types ⟦ Q, X ⟧}
             {p₁ : dQ -->[ h₁ · f] make_ar g}
             {p₂ : dQ -->[ h₂ · f] make_ar g}
             (σ : h₁ ==> h₂)
             (σσ : p₁ ==>[ σ ▹ (f : one_types ⟦ X , Z ⟧)] p₂)
    : homotsec (is_pb_ump hP (pr2 p₁)) (is_pb_ump hP (pr2 p₂)).
  Proof.
    use (is_pb_ump_path
           hP (pr2 p₁)
           _ _
           (pr1_is_pb_ump _ _)
           (λ z, pr1_is_pb_ump hP (pr2 p₂) z @ !(σ _))
           (pr2_is_pb_ump _ _)
           (λ z, pr2_is_pb_ump hP (pr2 p₂) z @ !(pr1 σσ z))
           (commute_is_pb_ump _ _)
        ).
    exact (pb_to_cartesian_lift_2cell_help σ σσ).
  Defined.

  Definition pb_to_cartesian_lift_2cell_coherent
             {Q : one_types}
             {dQ : (cod_prod_disp_bicat one_types) Q}
             {h₁ h₂ : one_types ⟦ Q, X ⟧}
             {p₁ : dQ -->[ h₁ · f] make_ar g}
             {p₂ : dQ -->[ h₂ · f] make_ar g}
             (σ : h₁ ==> h₂)
             (σσ : p₁ ==>[ σ ▹ (f : one_types ⟦ X , Z ⟧)] p₂)
    : @coherent_homot
        one_types
        Q X h₁ h₂ σ dQ (make_ar p)
        (disp_mor_lift_1cell
           (cod_prod_disp_bicat one_types) _
           (pb_to_cartesian_lift p₁))
        (disp_mor_lift_1cell
           (cod_prod_disp_bicat one_types) _
           (pb_to_cartesian_lift p₂))
        (pb_to_cartesian_lift_2cell σ σσ).
  Proof.
    use funextsec.
    intro z.
    simpl ; cbn ; unfold homotcomp, invhomot, homotfun, funhomotsec ; cbn.
    etrans.
    {
      apply maponpaths.
      apply pr1_is_pb_ump_path.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply pathsinv0l.
    }
    etrans.
    {
      etrans.
      {
        simpl.
        apply pathscomp_inv.
      }
      apply maponpaths_2.
      apply pathsinv0inv0.
    }
    apply idpath.
  Qed.

  Definition pb_to_cartesian_uniqueness
             {Q : one_types}
             {dQ : cod_prod_disp_bicat one_types Q}
             {h₁ h₂ : one_types ⟦ Q, X ⟧}
             {p₁ : dQ -->[ h₁ · f] make_ar g}
             {p₂ : dQ -->[ h₂ · f] make_ar g}
             {σ : h₁ ==> h₂}
             (σσ : p₁ ==>[ σ ▹ f] p₂)
    : isaprop
        (lift_2cell_type
           (cod_prod_disp_bicat one_types)
           _
           σσ
           (pb_to_cartesian_lift p₁)
           (pb_to_cartesian_lift p₂)).
  Proof.
    apply invproofirrelevance.
    intros x y.
    use subtypePath.
    { intro ; apply (cod_prod_disp_bicat one_types). }
    use subtypePath.
    { intro ; apply one_types. }
    use funextsec.
    intro z.
    use (is_pb_homot hP).
    - exact (λ z, h₁ (pr2 dQ z)).
    - exact (pr1 p₁).
    - exact (pr2 p₁).
    - apply pr1_is_pb_ump.
    - exact (λ w, pr1_is_pb_ump hP (pr2 p₂) w @ !(σ _)).
    - apply pr2_is_pb_ump.
    - exact (λ w, pr2_is_pb_ump hP (pr2 p₂) w @ !(pr1 σσ _)).
    - apply commute_is_pb_ump.
    - intro w.
      pose (commute_is_pb_ump hP (pr2 p₂) w) as r.
      simpl in r.
      simpl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact r.
      }
      clear r.
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp0.
        }
        exact (!(path_assoc _ _ _)).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathsinv0.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpathsinv0.
      }
      refine (!_).
      use path_inv_rotate_rr.
      refine (!(path_assoc _ _ _) @ _).
      use path_inv_rotate_ll.
      pose (eqtohomot (pr2 σσ) w) as r.
      simpl in r.
      cbn in r.
      unfold homotcomp, homotfun, funhomotsec in r.
      exact r.
    - intro w.
      pose (eqtohomot (pr21 x) w) as r.
      simpl in r.
      cbn in r.
      unfold homotcomp, invhomot, funhomotsec, homotfun in r.
      cbn in r.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply pathscomp_inv.
        }
        apply maponpaths_2.
        apply pathsinv0inv0.
      }
      etrans.
      {
        apply maponpaths.
        exact (!r).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0r.
      }
      apply idpath.
    - intro w.
      pose (eqtohomot (pr21 y) w) as r.
      simpl in r.
      cbn in r.
      unfold homotcomp, invhomot, funhomotsec, homotfun in r.
      cbn in r.
      cbn.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply pathscomp_inv.
        }
        apply maponpaths_2.
        apply pathsinv0inv0.
      }
      etrans.
      {
        apply maponpaths.
        exact (!r).
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0r.
      }
      apply idpath.
    - intro w.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply pathscomp_inv.
        }
        apply maponpaths_2.
        apply pathsinv0inv0.
      }
      pose (maponpaths pr1 (pr2 x)) as r.
      simpl in r ; cbn in r.
      rewrite pr1_transportf in r.
      rewrite transportf_const in r.
      unfold idfun in r.
      cbn in r.
      unfold homotcomp, homotfun in r.
      pose (eqtohomot r w) as r'.
      cbn in r'.
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (!r').
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    - intro w.
      pose (maponpaths pr1 (pr2 y)) as r.
      simpl in r ; cbn in r.
      rewrite pr1_transportf in r.
      rewrite transportf_const in r.
      unfold idfun in r.
      cbn in r.
      unfold homotcomp, homotfun in r.
      pose (eqtohomot r w) as r'.
      cbn in r'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply pathscomp_inv.
        }
        apply maponpaths_2.
        apply pathsinv0inv0.
      }
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (!r').
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
  Qed.

  Definition pb_to_cartesian
    : cartesian_1cell
        (cod_prod_disp_bicat one_types)
        (@make_disp_1cell_cod
           one_types
           X Z f
           (make_ar p)
           (make_ar g)
           q
           c).
  Proof.
    use tpair.
    - exact (λ _ _ _ gg, pb_to_cartesian_lift gg).
    - intros Q dQ h₁ h₂ p₁ p₂ σ σσ.
      unfold lift_2cell.
      apply iscontraprop1.
      + apply pb_to_cartesian_uniqueness.
      + use tpair.
        * use make_disp_2cell_cod.
          ** exact (pb_to_cartesian_lift_2cell σ σσ).
          ** exact (pb_to_cartesian_lift_2cell_coherent σ σσ).
        * abstract
            (use subtypePath ; [ intro ; apply one_types | ] ;
             simpl ;
             cbn ;
             unfold homotcomp, funhomotsec, homotfun ;
             cbn ;
             rewrite pr1_transportf ;
             rewrite transportf_const ;
             use funextsec ;
             intro z ;
             cbn ; unfold idfun ;
             refine (maponpaths
                       (λ z, z @ _)
                       (pr2_is_pb_ump_path _ _ _ _ _ _ _ _)
                     @ _) ;
             refine (!(path_assoc _ _ _) @ _) ;
             apply maponpaths ;
             refine (maponpaths (λ z, z @ _) (pathscomp_inv _ _) @ _) ;
             refine (maponpaths (λ z, (z @ _) @ _) (pathsinv0inv0 _) @ _) ;
             refine (!(path_assoc _ _ _) @ _) ;
             refine (maponpaths (λ z, _ @ z) (pathsinv0l _) @ _) ;
             apply pathscomp0rid).
  Defined.
End PullBackToCartesian.

Section GlobalCleavingOneTypes.
  Context {X Y : one_types}
          (dY : cod_prod_disp_bicat one_types Y)
          (f : one_types ⟦ X, Y ⟧).

  Definition cod_prod_one_types_global_lift
    : cod_prod_disp_bicat one_types X.
  Proof.
    use tpair.
    - exact (pb_one_types f (pr2 dY)).
    - exact pb_pr1.
  Defined.

  Definition help2
    : cod_prod_one_types_global_lift -->[ f] dY.
  Proof.
    use tpair.
    - exact pb_pr2.
    - exact pb_commute.
  Defined.

  Definition help2_cartesian_1cell
    : cartesian_1cell (cod_prod_disp_bicat one_types) help2.
  Proof.
    apply pb_to_cartesian.
    apply pb_is_pb.
  Defined.
End GlobalCleavingOneTypes.

Definition cod_one_types_global_cleaving
  : global_cleaving (cod_prod_disp_bicat one_types).
Proof.
  intros X Y dY f.
  use tpair.
  - exact (cod_prod_one_types_global_lift dY f).
  - use tpair.
    + exact (help2 dY f).
    + exact (help2_cartesian_1cell dY f).
Defined.

(** Codomain fibration for 1-types *)
Definition cod_one_types_fibration
  : fibration_of_bicats (cod_prod_disp_bicat one_types).
Proof.
  repeat split.
  - apply cod_local_cleaving.
    + exact one_types_is_univalent_2_1.
    + exact @one_type_2cell_iso.
  - exact cod_one_types_global_cleaving.
  - apply cod_lwhisker_cartesian.
    + exact one_types_is_univalent_2_1.
    + exact @one_type_2cell_iso.
  - apply cod_rwhisker_cartesian.
    + exact one_types_is_univalent_2_1.
    + exact @one_type_2cell_iso.
Defined.
