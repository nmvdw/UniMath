Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

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
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : UU
      := ∑ (hh : cc -->[ h ] aa),
         disp_invertible_2cell
           (id2_invertible_2cell _)
           (hh ;; ff)
           gg.

    Definition disp_mor_lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell gg)
      : cc -->[ h ] aa
      := pr1 Lh.

    Definition disp_cell_lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell gg)
      : disp_invertible_2cell _ (disp_mor_lift_1cell Lh;; ff) gg
      := pr2 Lh.

    Definition lift_2cell_type
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : UU
      := ∑ (δδ : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh'),
         transportf
           (λ z, _ ==>[ z ] _)
           (id2_right _ @ ! id2_left _ )
           (δδ ▹▹ ff •• disp_cell_lift_1cell Lh')
         =
         disp_cell_lift_1cell Lh •• σσ.

    Definition lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : UU
      := iscontr (lift_2cell_type σσ Lh Lh').

    Definition cartesian_1cell
      : UU
      :=
        ∑ (Lh : ∏ (c : B)
                 (cc : D c)
                 (h : c --> a)
                 (gg : cc -->[ h · f ] bb),
                lift_1cell gg),
        ∏ (c : B)
          (cc : D c)
          (h h' : c --> a)
          (gg : cc -->[h · f ] bb)
          (gg' : cc -->[h' · f ] bb)
          (δ : h ==> h')
          (σσ : gg ==>[ δ ▹ f] gg'),
        lift_2cell
          σσ
          (Lh _ _ _ gg)
          (Lh _ _ _ gg').

  End Cartesian1cell.


  Definition is_cartesian_2cell
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
       ∃! (γγ : hh ==>[ γ ] ff), (γγ •• αα) = ββ.

  Definition cartesian_lift_2cell
             {x y : B}
             {xx : D x}
             {yy : D y}
             {f g : x --> y}
             (gg : xx -->[ g ] yy)
             (α : f ==> g)
    : UU
    := ∑ (ff : xx -->[ f ] yy) (αα : ff ==>[ α ] gg), is_cartesian_2cell αα.

  Definition local_cleaving
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       cartesian_lift_2cell gg α.

  Definition global_cleaving
    : UU
    := ∏ (a b : B)
         (bb : D b)
         (f : a --> b),
       ∑ (aa : D a) (ff : aa -->[ f ] bb), cartesian_1cell ff.

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
       is_cartesian_2cell αα → is_cartesian_2cell (hh ◃◃ αα).

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
       is_cartesian_2cell αα → is_cartesian_2cell (αα ▹▹ hh).

  Definition fibration_of_bicats
    : UU
    := local_cleaving
         × global_cleaving
         × lwhisker_cartesian
         × rwhisker_cartesian.

End BicatFibration.
