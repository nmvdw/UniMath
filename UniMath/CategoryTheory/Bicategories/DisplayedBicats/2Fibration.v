Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat.
Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Definition rwhisker_of_invertible_2cell
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           (g : y --> z)
           (α : invertible_2cell f₁ f₂)
  : invertible_2cell (f₁ · g) (f₂ · g).
Proof.
  use make_invertible_2cell.
  - exact (α ▹ g).
  - is_iso.
    apply α.
Defined.

Section BicatFibration.
  Context {B : bicat}.
  Variable (D : disp_bicat B).

  Section Cartesian1cell.
    Context {a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}.
    Variable (ff : aa -->[ f ] bb).

    Definition lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               (gg : cc -->[ g ] bb)
               {h : c --> a}
               (α : invertible_2cell (h · f) g)
      : UU
      := ∑ (hh : cc -->[ h ] aa),
         disp_invertible_2cell
           α
           (hh ;; ff)
           gg.

    Definition disp_mor_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : cc -->[ h ] aa
      := pr1 Lh.

    Definition disp_cell_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : disp_invertible_2cell α (disp_mor_lift_1cell Lh;; ff) gg
      := pr2 Lh.

    Definition lift_2cell
               {c : B} {cc : D c}
               {g g' : c --> b}
               {σ : g ==> g'}
               {gg : cc -->[ g ] bb}
               {gg' : cc -->[ g' ] bb}
               (σσ : gg ==>[ σ ] gg')
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               {h' : c --> a}
               {α' : invertible_2cell (h' · f) g'}
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ)
      : UU
      := ∃! (δδ : pr1 Lh ==>[ δ ] pr1 Lh'),
         transportf
           (λ z, _ ==>[ z ] _)
           Pδ
           (δδ ▹▹ ff •• disp_cell_lift_1cell Lh')
         =
         disp_cell_lift_1cell Lh •• σσ.

    Definition cartesian_1cell
      : UU
      :=
        (∏ (c : B) (cc : D c)
           (g : c --> b)
           (gg : cc -->[ g ] bb)
           (h : c --> a)
           (α : invertible_2cell (h · f) g),
         lift_1cell gg α)
          × (∏ (c : B) (cc : D c)
               (g g' : c --> b)
               (σ : g ==> g')
               (gg : cc -->[ g ] bb)
               (gg' : cc -->[ g' ] bb)
               (σσ : gg ==>[ σ ] gg')
               (h : c --> a)
               (α : invertible_2cell (h · f) g)
               (h' : c --> a)
               (α' : invertible_2cell (h' · f) g')
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ),
             lift_2cell σσ Lh Lh' δ Pδ).
  End Cartesian1cell.

  Definition cartesian_2cell
             {x y : B}
             {xx : D x} {yy : D y}
             {f g : x --> y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             {α : f ==> g}
             (αα : ff ==>[ α ] gg)
    : UU
    := ∏ (h : x --> y)
         (hh : xx -->[ h ] yy)
         (γ : h ==> f)
         (ββ : hh ==>[ γ • α ] gg),
       ∃! (γγ : hh ==>[ γ ] ff),
        (γγ •• αα) = ββ.

  Definition locally_fibered
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       ∑ (αα : ff ==>[ α ] gg), cartesian_2cell αα.

  Definition globally_fibered
    : UU
    := ∏ (a b : B)
         (aa : D a) (bb : D b)
         (f : a --> b),
       ∑ (ff : aa -->[ f ] bb), cartesian_1cell ff.

  Definition lwhisker_cartesian
    : UU
    := ∏ (w x y : B)
         (ww : D w) (xx : D x) (yy : D y)
         (h : w --> x)
         (f g : x --> y)
         (hh : ww -->[ h ] xx)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       cartesian_2cell αα → cartesian_2cell (hh ◃◃ αα).

  Definition rwhisker_cartesian
    : UU
    := ∏ (x y z : B)
         (xx : D x) (yy : D y) (zz : D z)
         (f g : x --> y) (h : y --> z)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (hh : yy -->[ h ] zz)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       cartesian_2cell αα → cartesian_2cell (αα ▹▹ hh).

  Definition fibration_of_bicats
    : UU
    := locally_fibered
         × globally_fibered
         × lwhisker_cartesian
         × rwhisker_cartesian.
End BicatFibration.
(*
Definition vcomp_disp_is_invertible
           {B : bicat}
           {D : disp_bicat B}
           {a b : B}
           {aa : D a} {bb : D b}
           {f g h : a --> b}
           {ff : aa -->[ f ] bb}
           {gg : aa -->[ g ] bb}
           {hh : aa -->[ h ] bb}
           {α : invertible_2cell f g}
           {β : invertible_2cell g h}
           (αα : disp_invertible_2cell α ff gg)
           (ββ : disp_invertible_2cell β gg hh)
  : is_disp_invertible_2cell (comp_of_invertible_2cell α β) (αα •• ββ).
Proof.
  use tpair.
  - exact (disp_inv_cell ββ •• disp_inv_cell αα).
  - split.
    + cbn.
      rewrite disp_vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply disp_vcomp_rinv.
      }
      unfold transportb.
      rewrite !disp_mor_transportf_postwhisker, !disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite !disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        exact (disp_vcomp_rinv αα).
      }
      unfold transportb.
      rewrite !transport_f_f.
      refine (maponpaths (λ p, transportf (λ z, _ ==>[ z ] _) p _) _).
      apply B.
    + cbn.
      etrans.
      {
        rewrite disp_vassocl.
        do 2 apply maponpaths.
        rewrite disp_vassocr.
        apply maponpaths.
        apply maponpaths_2.
        apply disp_vcomp_linv.
      }
      unfold transportb.
      rewrite !disp_mor_transportf_postwhisker, !disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite !disp_mor_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        exact (disp_vcomp_linv ββ).
      }
      unfold transportb.
      rewrite !transport_f_f.
      refine (maponpaths (λ p, transportf (λ z, _ ==>[ z ] _) p _) _).
      apply B.
Defined.

Definition vcomp_disp_invertible
           {B : bicat}
           {D : disp_bicat B}
           {a b : B}
           {aa : D a} {bb : D b}
           {f g h : a --> b}
           {ff : aa -->[ f ] bb}
           {gg : aa -->[ g ] bb}
           {hh : aa -->[ h ] bb}
           {α : invertible_2cell f g}
           {β : invertible_2cell g h}
           (αα : disp_invertible_2cell α ff gg)
           (ββ : disp_invertible_2cell β gg hh)
  : disp_invertible_2cell (comp_of_invertible_2cell α β) ff hh.
Proof.
  use tpair.
  repeat use tpair.
  - exact (αα •• ββ).
  - apply vcomp_disp_is_invertible.
Defined.
*)

Definition id1_cartesian_1cell
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {D : disp_bicat B}
           {a : B}
           (aa : D a)
  : cartesian_1cell D (id_disp aa).
Proof.
  split.
  - intros c cc g gg h α.
    admit.
  - intros c cc g g' σ gg gg' σσ h α h' α' Lh Lh' δ Pδ.
    repeat use tpair.
    + pose (pr2 Lh) as d.
      pose (pr2 Lh') as d'.
      cbn in *.
      refine (transportf
                (λ p, _ ==>[ p ] _)
                _
                (disp_rinvunitor _ •• d •• σσ •• disp_inv_cell d' •• disp_runitor _)).
      assert ((((rinvunitor h • α) • σ) • α' ^-1) • runitor h' = δ) as X.
      {
        admit.
        (*
        etrans.
        {
          do 2 apply maponpaths_2.
          rewrite !vassocl.
          rewrite <- Pδ.
          rewrite !vassocr.
          rewrite rwhisker_hcomp.
          rewrite <- rinvunitor_natural.
          apply idpath.
        }
        rewrite !vassocl.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_rinv.
          apply id2_left.
        }
        rewrite rinvunitor_runitor.
        apply id2_right.*)
      }
      abstract (exact X).
    + cbn.
      unfold transportb, disp_cell_lift_1cell ; cbn.
      destruct Lh.
      destruct Lh'.
      cbn.
      Check (pr2 Lh).
      Search disp_rinvunitor.


(*
Definition rwhisker_of_invertible_2cell
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           (g : y --> z)
           (α : invertible_2cell f₁ f₂)
  : invertible_2cell (f₁ · g) (f₂ · g).
Proof.
  use make_invertible_2cell.
  - exact (α ▹ g).
  - is_iso.
    apply α.
Defined.

Section BicatFibration.
  Context {B : bicat}.
  Variable (D : disp_bicat B).

  Section Cartesian1cell.
    Context {a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}.
    Variable (ff : aa -->[ f ] bb).

    Definition lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               (gg : cc -->[ g ] bb)
               {h : c --> a}
               (α : invertible_2cell (h · f) g)
      : UU
      := ∑ (h' : c --> a)
           (hh' : cc -->[ h' ] aa)
           (β : invertible_2cell h' h),
         disp_invertible_2cell
           (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell f β)
              α)
           (hh' ;; ff)
           gg.

    Definition mor_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : c --> a
      := pr1 Lh.

    Definition disp_mor_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : cc -->[ mor_lift_1cell Lh ] aa
      := pr12 Lh.

    Definition cell_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : invertible_2cell (mor_lift_1cell Lh) h
      := pr122 Lh.

    Definition disp_cell_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : disp_invertible_2cell
          (comp_of_invertible_2cell
             (rwhisker_of_invertible_2cell f (cell_lift_1cell Lh))
             α)
          (disp_mor_lift_1cell Lh ;; ff)
          gg
      := pr222 Lh.

    Definition lift_2cell_help
               {c : B} {cc : D c}
               {g g' : c --> b}
               {σ : g ==> g'}
               {gg : cc -->[ g ] bb}
               {gg' : cc -->[ g' ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               {h' : c --> a}
               {α' : invertible_2cell (h' · f) g'}
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ)
      : ((cell_lift_1cell Lh ▹ f) • α) • σ
        =
        (((cell_lift_1cell Lh • δ)
            • (cell_lift_1cell Lh') ^-1) ▹ f)
          • ((cell_lift_1cell Lh' ▹ f) • α').
    Proof.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite vcomp_lid, id2_right.
        rewrite <- rwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      exact Pδ.
    Qed.

    Definition lift_2cell
               {c : B} {cc : D c}
               {g g' : c --> b}
               {σ : g ==> g'}
               {gg : cc -->[ g ] bb}
               {gg' : cc -->[ g' ] bb}
               (σσ : gg ==>[ σ ] gg')
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               {h' : c --> a}
               {α' : invertible_2cell (h' · f) g'}
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ)
      : UU
      := ∃! (δδ : (pr12 Lh)
                    ==>[ (cell_lift_1cell Lh)
                           • δ
                           • (cell_lift_1cell Lh')^-1 ]
                    pr12 Lh'),
         transportb
           (λ z, _ ==>[ z ] _)
           (lift_2cell_help Lh Lh' δ Pδ)
           (δδ ▹▹ ff •• disp_cell_lift_1cell Lh')
         =
         disp_cell_lift_1cell Lh •• σσ.

    Definition cartesian_1cell
      : UU
      :=
        (∏ (c : B) (cc : D c)
           (g : c --> b)
           (gg : cc -->[ g ] bb)
           (h : c --> a)
           (α : invertible_2cell (h · f) g),
         lift_1cell gg α)
          × (∏ (c : B) (cc : D c)
               (g g' : c --> b)
               (σ : g ==> g')
               (gg : cc -->[ g ] bb)
               (gg' : cc -->[ g' ] bb)
               (σσ : gg ==>[ σ ] gg')
               (h : c --> a)
               (α : invertible_2cell (h · f) g)
               (h' : c --> a)
               (α' : invertible_2cell (h' · f) g')
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ),
             lift_2cell σσ Lh Lh' δ Pδ).
  End Cartesian1cell.

  Definition cartesian_2cell
             {x y : B}
             {xx : D x} {yy : D y}
             {f g : x --> y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             {α : f ==> g}
             (αα : ff ==>[ α ] gg)
    : UU
    := ∏ (h : x --> y)
         (hh : xx -->[ h ] yy)
         (β : h ==> g)
         (ββ : hh ==>[ β ] gg)
         (γ : h ==> f)
         (p : β = γ • α),
       ∃! (γγ : hh ==>[ γ ] ff),
       transportb (λ z, _ ==>[ z ] _) p (γγ •• αα) = ββ.

  Definition locally_fibered
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       ∑ (αα : ff ==>[ α ] gg), cartesian_2cell αα.

  Definition globally_fibered
    : UU
    := ∏ (a b : B)
         (aa : D a) (bb : D b)
         (f : a --> b),
       ∑ (ff : aa -->[ f ] bb), cartesian_1cell ff.

  Definition lwhisker_cartesian
    : UU
    := ∏ (w x y : B)
         (ww : D w) (xx : D x) (yy : D y)
         (h : w --> x)
         (f g : x --> y)
         (hh : ww -->[ h ] xx)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       cartesian_2cell αα → cartesian_2cell (hh ◃◃ αα).

  Definition rwhisker_cartesian
    : UU
    := ∏ (x y z : B)
         (xx : D x) (yy : D y) (zz : D z)
         (f g : x --> y) (h : y --> z)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (hh : yy -->[ h ] zz)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       cartesian_2cell αα → cartesian_2cell (αα ▹▹ hh).

  Definition fibration_of_bicats
    : UU
    := locally_fibered
         × globally_fibered
         × lwhisker_cartesian
         × rwhisker_cartesian.
End BicatFibration.

Definition id2_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {xx : D x} {yy : D y}
           {f g h : x --> y}
           (ff : xx -->[ f ] yy)
  : cartesian_2cell D (disp_id2 ff).
Proof.
  intros k kk α αα δ p.
  repeat use tpair.
  - refine (transportf (λ z, _ ==>[ z ] _) _ αα).
    abstract (rewrite p, id2_right ; apply idpath).
  - abstract
      (cbn ;
       rewrite disp_id2_right ;
       unfold transportb ;
       rewrite !transport_f_f ;
       apply (transportf_set (λ z, _ ==>[ z ] _)) ;
       apply B).
  - cbn.
    intro t.
    apply subtypePath.
    { intro ; apply D. }
    abstract
    (cbn ;
     rewrite <- (pr2 t) ;
     unfold transportb ;
     rewrite disp_id2_right ;
     unfold transportb ;
     rewrite !transport_f_f ;
     refine (!_) ;
     apply (transportf_set (λ z, _ ==>[ z ] _)) ;
     apply B).
Defined.

Definition vcomp_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {xx : D x} {yy : D y}
           {f g h : x --> y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {hh : xx -->[ h ] yy}
           {α : f ==> g} {β : g ==> h}
           (αα : ff ==>[ α ] gg)
           (ββ : gg ==>[ β ] hh)
  : cartesian_2cell D αα
    → cartesian_2cell D ββ
    → cartesian_2cell D (αα •• ββ).
Proof.
  intros Hα Hβ k kk γ γγ δ p.
  assert (γ = (δ • α) • β) as q.
  { rewrite vassocl. exact p. }
  pose (Hβ k kk γ γγ (δ • α) q) as H.
  destruct H as [[δαδα Hδα] Unδα].
  pose (Hα k kk (δ • α) δαδα δ (idpath _)) as H2.
  destruct H2 as [[δδ Hδδ] Unδδ].
  cbn in * ; unfold idfun in *.
  repeat use tpair.
  - exact δδ.
  - abstract
      (cbn ;
       refine (_ @ Hδα) ;
       rewrite <- Hδδ ;
       rewrite disp_vassocr ;
       unfold transportb ;
       rewrite !transport_f_f ;
       cbn ;
       refine (maponpaths (λ p, transportf (λ z, _ ==>[ z ] _) p _) _) ;
       apply B).
  - intros t.
    apply subtypePath.
    { intro ; apply D. }
    abstract
    (cbn ;
     refine (maponpaths pr1 (Unδδ (pr1 t ,, _))) ;
     refine (maponpaths pr1 (Unδα (pr1 t •• αα ,, _))) ;
     rewrite <- (pr2 t) ;
     rewrite disp_vassocr ;
     unfold transportb ;
     rewrite !transport_f_f ;
     refine (maponpaths (λ p, transportf (λ z, _ ==>[ z ] _) p _) _) ;
     apply B).
Defined.



{a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}.
Variable (ff : aa -->[ f ] bb).

cartesian_1cell
