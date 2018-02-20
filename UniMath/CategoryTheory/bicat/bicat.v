Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

(* Needed?
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.equivalences.
 *)

Open Scope cat.

Definition bicat_cell_struct (C : precategory_ob_mor) : UU :=
  ∏ (a b: C), C⟦a, b⟧ → C⟦a, b⟧ → UU.

(*
Definition bicat_ob_mor_cells : UU := ∑ (C : precategory_ob_mor), bicat_cell_struct C.

Coercion precat_ob_mor_from_bicat_ob_mor_cells (T : bicat_ob_mor_cells)
  : precategory_ob_mor := pr1 T.

Definition bicat_cells (C : bicat_ob_mor_cells) {a b : C} (f g : C⟦a, b⟧) : UU :=
  pr2 C a b f g.
 *)

Definition bicat_1_id_comp_cells : UU := ∑ (C : precategory_data), bicat_cell_struct C.
Coercion precat_data_from_bicat_1_id_comp_cells (C : bicat_1_id_comp_cells)
  : precategory_data
  := pr1 C.

Definition bicat_cells (C : bicat_1_id_comp_cells) {a b : C} (f g : C⟦a, b⟧) : UU :=
  pr2 C a b f g.


Notation "f '==>' g" := (bicat_cells _ f g) (at level 60).
Notation "f '<==' g" := (bicat_cells _ g f) (at level 60, only parsing).
(*
Definition bicat_cells_1_id_comp : UU := ∑ C : bicat_ob_mor_cells, precategory_id_comp C.

Coercion precat_data_from_bicat_cells_1_id_comp (C : bicat_cells_1_id_comp) : precategory_data.
Proof.
  exists (pr1 C).
  exact (pr2 C).
Defined.

Check (fun (C : bicat_cells_1_id_comp) (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) => f · g).
*)



Definition bicat_2_id_comp_struct (C : bicat_1_id_comp_cells) : UU
  :=
    (* 2-unit *)
    (∏ (a b : C) (f : C⟦a, b⟧), f ==> f)
      ×
    (* left unitor *)
    (∏ (a b : C) (f : C⟦a, b⟧), identity _ · f ==> f)
      ×
    (* right unitor *)
    (∏ (a b : C) (f : C⟦a, b⟧), f · identity _  ==> f)
      ×
    (* left inverse unitor *)
    (∏ (a b : C) (f : C⟦a, b⟧), identity _ · f <== f)
      ×
    (* right inverse unitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), f · identity _  <== f)
      ×
    (* right associator *)
    (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
     (f · g) · h ==> f · (g · h))
          ×
    (* left associator *)
    (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
       f · (g · h) ==> (f · g) · h)
      ×
    (* vertical composition *)
    (∏ (a b : C) (f g h : C⟦a, b⟧), f ==> g -> g ==> h -> f ==> h)
    ×
    (* left whiskering *)
    (∏ (a b c : C) (f : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧),
     g1 ==> g2 → f · g1 ==> f · g2)
    ×
    (* right whiskering *)
    (∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g : C⟦b, c⟧),
     f1 ==> f2 → f1 · g ==> f2 · g).




(* Horizontal composition, to be derived from whiskering
    ( ∏ (a b c : C) (f1 f2 : C⟦a, b⟧) (g1 g2 : C⟦b, c⟧),
           f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2).
*)

Definition bicat_data : UU := ∑ C, bicat_2_id_comp_struct C.

Coercion bicat_cells_1_id_comp_from_bicat_data (C : bicat_data) : bicat_1_id_comp_cells
  := pr1 C.

Definition id2 {C : bicat_data} {a b : C} (f : C⟦a, b⟧) : f ==> f
  := pr1 (pr2 C) a b f.
Check (λ (C : bicat_data) , pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (C))))))) ))).


Definition lunitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : identity _ · f ==> f
  := pr1 (pr2 (pr2 C)) a b f.

Definition runitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : f · identity _ ==> f
  := pr1 (pr2 (pr2 (pr2 C))) a b f.

Definition linvunitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : identity _ · f <== f
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) a b f.

Definition rinvunitor {C : bicat_data} {a b : C} (f : C⟦a, b⟧)
  : f · identity _ <== f
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) a b f.

Definition rassociator {C : bicat_data} {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : (f · g) · h ==> f · (g · h)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) a b c d f g h.

Definition lassociator {C : bicat_data} {a b c d : C}
           (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : f · (g · h) ==> (f · g) · h
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) a b c d f g h.

Definition vcomp2 {C : bicat_data} {a b : C} {f g h: C⟦a, b⟧}
  : f ==> g → g ==> h → f ==> h
  := λ x y, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ _ _ _  x y.

Definition lwhisker {C : bicat_data} {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
  : g1 ==> g2 → f · g1 ==> f · g2
  := λ x, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.

Definition rwhisker {C : bicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
  : f1 ==> f2 → f1 · g ==> f2 · g
  := λ x, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ _ _ _ _ x.


Notation "x • y" := (vcomp2 x y) (at level 60).
Notation "f ◃ x" := (lwhisker f x) (at level 60). (* \tw *)
Notation "y ▹ g" := (rwhisker g y) (at level 60). (* \tw nr 2 *)

Definition hcomp1 {C : bicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2.
Proof.
  intros x y.
  set (xg1 := x ▹ g1).
  set (f2y := f2 ◃ y).
  exact (xg1 • f2y).
Defined.

Definition hcomp2 {C : bicat_data} {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
  : f1 ==> f2 -> g1 ==> g2 -> f1 · g1 ==> f2 · g2.
Proof.
  intros x y.
  set (f1y := f1 ◃ y).
  set (xg2 := x ▹ g2).
  exact (f1y • xg2).
Defined.

(*
Notation "x ⋆ y" := (hcomp2 x y) (at level 50).
 *)

Definition bicat_laws (C : bicat_data) : UU
  :=  (* 1a id2_left *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), id2 f • x = x)
        ×
      (* 1b id2_right *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g), x • id2 g = x)
      ×
      (* 2 vassocr *)
      (∏ (a b : C) (f g h k : C⟦a, b⟧) (x : f ==> g) (y : g ==> h) (z : h ==> k),
       x • (y • z) = (x • y) • z)
      ×
      (* 3a lwhisker_id2 *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), f ◃ id2 g = id2 _ )
      ×
      (* 3b id2_rwhisker *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧), id2 f ▹ g = id2 _ )
      ×
      (* 4 lwhisker_vcomp *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g h i : C⟦b, c⟧) (x : g ==> h) (y : h ==> i),
       (f ◃ x) • (f ◃ y) = f ◃ (x • y))
      ×
      (* 5 rwhisker_vcomp *)
      (∏ (a b c : C) (f g h : C⟦a, b⟧) (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h),
       (x ▹ i) • (y ▹ i) = (x • y) ▹ i)
      ×
      (* 6  vcomp_lunitor *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
       (identity _ ◃ x) • lunitor g = lunitor f • x )
      ×
      (* 7 vcomp_runitor *)
      (∏ (a b : C) (f g : C⟦a, b⟧) (x : f ==> g),
       (x ▹ identity _ ) • runitor g = runitor f • x )
      ×
      (* 8 lwhisker_lwhisker *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i),
       f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x))
      ×
      (* 9 rwhisker_lwhisker *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g h : C⟦b, c⟧) (i : c --> d) (x : g ==> h),
       (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i))
      ×
      (* 10 rwhisker_rwhisker *)
      (∏ (a b c d : C) (f g : C⟦a, b⟧) (h : C⟦b, c⟧) (i : c --> d) (x : f ==> g),
       lassociator _ _ _ • ((x ▹ h) ▹ i) = (x ▹ h · i) • lassociator _ _ _ )
      ×
      (* 11 vcomp_whisker *)
      (∏ (a b c : C) (f g : C⟦a, b⟧) (h i : C⟦b, c⟧) (x : f ==> g) (y : h ==> i),
       (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i))
      ×
      (* 12a lunitor_linvunitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), lunitor f • linvunitor _ = id2 _ )
      ×
      (* 12b linvunitor_lunitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), linvunitor f • lunitor _ = id2 _ )
      ×
      (* 13a runitor_rinvunitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), runitor f • rinvunitor _ = id2 _ )
      ×
      (* 13b rinvunitor_runitor *)
      (∏ (a b : C) (f : C⟦a, b⟧), rinvunitor f • runitor _ = id2 _ )
      ×
      (* 14a lassociator_rassociator *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d),
       lassociator f g h • rassociator _ _ _ = id2 _ )
      ×
      (* 14b rassociator_lassociator *)
      (∏ (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d),
       rassociator f g h • lassociator _ _ _ = id2 _ )
      ×
      (* 15 runitor_rwhisker *)
      (∏ (a b c : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧),
       lassociator _ _ _ • (runitor f ▹ g) = f ◃ lunitor g )
      ×
      (* 16  lassociator_lassociator *)
      (∏ (a b c d e: C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧),
       (f ◃ lassociator g h i) • lassociator _ _ _  • (lassociator _ _ _ ▹ i) =
       lassociator f g _  • lassociator _ _ _
      ).

Definition bicat : UU := ∑ C : bicat_data, bicat_laws C.

Coercion bicat_data_from_bicat (C : bicat) : bicat_data := pr1 C.
Coercion bicat_laws_from_bicat (C : bicat) : bicat_laws C := pr2 C.


Section bicat_law_projections.

Context {C : bicat}.

Definition id2_left
           (* 1a id2_left *)
           {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : id2 f • x = x
  := pr1 (pr2 C) _ _ _ _ x.

Definition id2_right
           (* 1b id2_right *)
           {a b : C} {f g : C⟦a, b⟧} (x : f ==> g)
  : x • id2 g = x
  := pr1 (pr2 (pr2 C)) _ _ _ _ x.

Definition vassocr
           (* 2 vassocr *)
           {a b : C} {f g h k : C⟦a, b⟧} (x : f ==> g) (y : g ==> h) (z : h ==> k)
  : x • (y • z) = (x • y) • z
  := pr1 (pr2 (pr2 (pr2 C))) _ _ _ _ _ _ x y z.

Definition lwhisker_id2
           (* 3a lwhisker_id2 *)
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : f ◃ id2 g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 C)))) _ _ _ f g.

Definition id2_rwhisker
           (* 3b id2_rwhisker *)
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : id2 f ▹ g = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 C))))) _ _ _ f g.

Definition lwhisker_vcomp
           (* 4 lwhisker_vcomp *)
           {a b c : C} (f : C⟦a, b⟧) {g h i : C⟦b, c⟧}
           (x : g ==> h) (y : h ==> i)
  : (f ◃ x) • (f ◃ y) = f ◃ (x • y)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))) _ _ _ f _ _ _ x y.

Definition rwhisker_vcomp
           (* 5 rwhisker_vcomp *)
           {a b c : C} {f g h : C⟦a, b⟧} (i : C⟦b, c⟧) (x : f ==> g) (y : g ==> h)
  : (x ▹ i) • (y ▹ i) = (x • y) ▹ i
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))) _ _ _ _ _ _ i x y.

Definition vcomp_lunitor
           (* 6  vcomp_lunitor *)
           {a b : C} (f g : C⟦a, b⟧) (x : f ==> g)
  : (identity _ ◃ x) • lunitor g = lunitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))) _ _ f g x.

Definition vcomp_runitor
           (* 7 vcomp_runitor *)
           {a b : C} (f g : C⟦a, b⟧) (x : f ==> g)
  : (x ▹ identity _ ) • runitor g = runitor f • x
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))) _ _ f g x.

Definition lwhisker_lwhisker
           (* 8 lwhisker_lwhisker *)
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) {h i : c --> d} (x : h ==> i)
  : f ◃ (g ◃ x) • lassociator _ _ _ = lassociator _ _ _ • (f · g ◃ x)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))) _ _ _ _ f g _ _ x.

Definition rwhisker_lwhisker
           (* 9 rwhisker_lwhisker *)
           {a b c d : C} (f : C⟦a, b⟧) {g h : C⟦b, c⟧} (i : c --> d) (x : g ==> h)
  : (f ◃ (x ▹ i)) • lassociator _ _ _ = lassociator _ _ _ • ((f ◃ x) ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))) _ _ _ _ f _ _ i x.

Definition rwhisker_rwhisker
           (* 10 rwhisker_rwhisker *)
           {a b c d : C} {f g : C⟦a, b⟧} (h : C⟦b, c⟧) (i : c --> d) (x : f ==> g)
  : lassociator _ _ _ • ((x ▹ h) ▹ i) = (x ▹ h · i) • lassociator _ _ _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))) _ _ _ _ _ _ h i x.

Definition vcomp_whisker
           (* 11 vcomp_whisker *)
           {a b c : C} {f g : C⟦a, b⟧} {h i : C⟦b, c⟧} (x : f ==> g) (y : h ==> i)
  : (x ▹ h) • (g ◃ y) = (f ◃ y) • (x ▹ i)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))) _ _ _ _ _ _ _ x y.

Definition lunitor_linvunitor
           (* 12a lunitor_linvunitor *)
           {a b : C} (f : C⟦a, b⟧)
  : lunitor f • linvunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))) _ _ f.

Definition linvunitor_lunitor
           (* 12b linvunitor_lunitor *)
           {a b : C} (f : C⟦a, b⟧)
  : linvunitor f • lunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))) _ _ f.

Definition runitor_rinvunitor
           (* 13a runitor_rinvunitor *)
           {a b : C} (f : C⟦a, b⟧)
  : runitor f • rinvunitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))) _ _ f.

Definition rinvunitor_runitor
           (* 13b rinvunitor_runitor *)
           {a b : C} (f : C⟦a, b⟧)
  : rinvunitor f • runitor _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))))) _ _ f.

Definition lassociator_rassociator
           (* 14a lassociator_rassociator *)
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
  : lassociator f g h • rassociator _ _ _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))) _ _ _ _ f g h.

Definition rassociator_lassociator
           (* 14b rassociator_lassociator *)
           {a b c d : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d)
  : rassociator f g h • lassociator _ _ _ = id2 _
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C))))))))))))))))))) _ _ _ _ f g h.

Definition runitor_rwhisker
           (* 15 runitor_rwhisker *)
           {a b c : C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : lassociator _ _ _ • (runitor f ▹ g) = f ◃ lunitor g
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))))) _ _ _ f g .

Definition lassociator_lassociator
           (* 16  lassociator_lassociator *)
           {a b c d e: C} (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : c --> d) (i : C⟦d, e⟧)
  : (f ◃ lassociator g h i) • lassociator _ _ _  • (lassociator _ _ _ ▹ i) =
    lassociator f g _  • lassociator _ _ _

  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 C)))))))))))))))))))) _ _ _ _ _ f g h i.

(** TODO: there is an analog to law nr 8 for right associator.
          can it be derived from 8 plus l being inverse to r associator?

 (a b c d : C) (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h i : c --> d) (x : h ==> i),
         (f · g) ◃ x • rassociator _ _ _ = rassociator _ _ _ • (f ◃ (g ◃ x))

*)

End bicat_law_projections.


(* ----------------------------------------------------------------------------------- *)
(** ** Derived laws *)

Section Derived_laws.

Context {C : bicat}.

Lemma hcomp1_hcomp2 {a b c : C} {f1 f2 : C⟦a, b⟧} {g1 g2 : C⟦b, c⟧}
      (η : f1 ==> f2) (φ : g1 ==> g2)
  : hcomp1 η φ = hcomp2 η φ.
Proof.
  unfold hcomp1.
  unfold hcomp2.
  apply vcomp_whisker.
Defined.

Lemma hcomp1_lassoc {a b c d : C}
      {f1 g1 : C ⟦ a, b ⟧} {f2 g2 : C ⟦ b, c ⟧} {f3 g3 : C ⟦ c, d ⟧}
      (x1 : f1 ==> g1) (x2 : f2 ==> g2) (x3 : f3 ==> g3)
  :  hcomp1 x1 (hcomp1 x2 x3) • lassociator g1 g2 g3 =
     lassociator f1 f2 f3 • hcomp1 (hcomp1 x1 x2) x3.
Proof.
  unfold hcomp1.
  rewrite <- lwhisker_vcomp.
  repeat rewrite <- vassocr.
  rewrite lwhisker_lwhisker.
  repeat rewrite vassocr.
  apply maponpaths_2.
  rewrite <- vassocr.
  rewrite rwhisker_lwhisker.
  rewrite vassocr.
  rewrite <- rwhisker_rwhisker.
  rewrite <- vassocr.
  apply maponpaths.
  apply rwhisker_vcomp.
Defined.

Lemma lassociator_to_rassociator_post {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : k ==> (f · g) · h)
      (y : k ==> f · (g · h))
  : x = y • lassociator f g h → x • rassociator f g h = y.
Proof.
  intros p.
  rewrite p.
  rewrite <- vassocr.
  rewrite lassociator_rassociator.
  apply id2_right.
Defined.

Lemma lassociator_to_rassociator_pre {a b c d : C}
      {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧} {h : C ⟦ c, d ⟧} {k : C ⟦ a, d ⟧}
      (x : f · (g · h) ==> k)
      (y : (f · g) · h ==> k) :
  x = lassociator f g h • y → rassociator f g h • x = y.
Proof.
  intros p.
  rewrite p.
  rewrite vassocr.
  rewrite rassociator_lassociator.
  apply id2_left.
Defined.

Lemma hcomp1_rassoc {a b c d : C}
      (f1 g1 : C ⟦ a, b ⟧) (f2 g2 : C ⟦ b, c ⟧) (f3 g3 : C ⟦ c, d ⟧)
      (x1 : f1 ==> g1) (x2 : f2 ==> g2) (x3 : f3 ==> g3)
  : hcomp1 (hcomp1 x1 x2) x3 • rassociator g1 g2 g3 =
    rassociator f1 f2 f3 • hcomp1 x1 (hcomp1 x2 x3).
Proof.
  apply lassociator_to_rassociator_post.
  apply pathsinv0.
  repeat rewrite <- vassocr.
  apply lassociator_to_rassociator_pre.
  apply hcomp1_lassoc.
Defined.

Lemma hcomp1_identity {a b c : C} (f1 : C ⟦ a, b ⟧) (f2 : C ⟦ b, c ⟧)
  : hcomp1 (id2 f1) (id2 f2) = id2 (f1 · f2).
Proof.
  unfold hcomp1.
  rewrite id2_rwhisker.
  rewrite id2_left.
  apply lwhisker_id2.
Defined.

Lemma hcomp_vcomp {a b c : C}
      (f1 g1 h1 : C ⟦ a, b ⟧)
      (f2 g2 h2 : C ⟦ b, c ⟧)
      (x1 : f1 ==> g1)
      (x2 : f2 ==> g2)
      (y1 : g1 ==> h1)
      (y2 : g2 ==> h2)
  : hcomp1 (x1 • y1) (x2 • y2) = hcomp1 x1 x2 • hcomp1 y1 y2.
Proof.
  unfold hcomp1 at 2 3.
  rewrite vassocr.
  rewrite vcomp_whisker.
  transitivity (((f1 ◃ x2) • ((x1 ▹ g2) • (y1 ▹ g2))) • (h1 ◃ y2)).
  2: repeat rewrite vassocr; reflexivity.
  rewrite rwhisker_vcomp.
  rewrite <- vcomp_whisker.
  rewrite <- vassocr.
  rewrite lwhisker_vcomp.
  unfold hcomp1.
  reflexivity.
Defined.

End Derived_laws.

(* ----------------------------------------------------------------------------------- *)
(** ** Homs are categories. *)

Section Hom_Spaces.

Context {C : bicat} (a b : C).

Definition hom_ob_mor : precategory_ob_mor.
Proof.
  exists (C ⟦a, b⟧). exact (λ f g, f ==> g).
Defined.

Definition hom_data : precategory_data.
Proof.
  exists hom_ob_mor. split.
  - exact id2.
  - exact (λ f g h x y, x • y).
Defined.

Lemma is_precategory_hom : is_precategory hom_data.
Proof.
  repeat split; simpl.
  - intros f g. apply id2_left.
  - intros f g. apply id2_right.
  - intros f g h i. apply vassocr.
Defined.

Definition hom : precategory.
Proof.
  exists hom_data.
  exact is_precategory_hom.
Defined.

End Hom_Spaces.

(* ----------------------------------------------------------------------------------- *)
(** Functor structure on horizontal composition. *)

Section hcomp_functor.

Context {C : bicat} {a b c : C}.

Definition hcomp_functor_data
  : functor_data (precategory_binproduct (hom a b) (hom b c)) (hom a c).
Proof.
  exists (λ p : (a-->b) × (b-->c), pr1 p · pr2 p).
  unfold hom_ob_mor. simpl. intros (f1, f2) (g1, g2).
  unfold precategory_binproduct_mor. simpl.
  intros (x, y). apply hcomp1; assumption.
Defined.

Lemma is_functor_hcomp : is_functor hcomp_functor_data.
Proof.
  split; red; simpl.
  - intros (f1, f2). simpl. apply hcomp1_identity.
  - intros (f1, f2) (g1, g2) (h1, h2).
    unfold precategory_binproduct_mor. simpl.
    intros (x1, x2) (y1, y2). cbn. apply hcomp_vcomp.
Defined.

Definition hcomp_functor : precategory_binproduct (hom a b) (hom b c) ⟶ hom a c.
Proof.
  exists hcomp_functor_data. exact is_functor_hcomp.
Defined.

End hcomp_functor.


(** Equivalences *)

Section equivalences.

Context {C : bicat_data}.

Definition is_equivalence {a b : C} {f g : a --> b} (η : f ==> g)
  : UU
  := ∑ φ : g ==> f, η • φ = id2 _ × φ • η = id2 _ .

Definition equivalence {a b : C} (f g : a --> b) : UU
  := ∑ η : f ==> g, is_equivalence η.

Coercion cell_from_equivalence {a b : C} {f g : a --> b} (η : equivalence f g) : f ==> g := pr1 η.

Definition inv_cell {a b : C} {f g : a --> b} (η : equivalence f g)
  : g ==> f
  := pr1 (pr2 η).

Definition equivalence_after_inv_cell {a b : C} {f g : a --> b} (η : equivalence f g)
  : η • inv_cell η = id2 _
  := pr1 (pr2 (pr2 η)).

Definition inv_cell_after_equivalence {a b : C} {f g : a --> b} (η : equivalence f g)
  : inv_cell η • η = id2 _
  := pr2 (pr2 (pr2 η)).

Definition inv_equivalence {a b : C} {f g : a --> b} (η : equivalence f g)
  : equivalence g f
  := (inv_cell η ,, cell_from_equivalence η ,, inv_cell_after_equivalence η ,, equivalence_after_inv_cell η ).


(* requires cell types to be sets
Lemma isaprop_isequivalence
*)

End equivalences.

Definition id2_equivalence {C : bicat} {a b : C} (f : a --> b) : equivalence f f.
Proof.
  repeat (use tpair).
  - apply (id2 _ ).
  - apply (id2 _ ).
  - apply id2_left.
  - apply id2_left.
Defined.


(** TODO:
    construct a prebicategory (see CT/bicategories) from a bicat
    Bonus:
    Equivalence of types between these two
 *)
(** TODO:
    define saturation/univalence for bicats
 *)


(** Chaotic bicat *)

Section chaotic_bicat.

Variable C : precategory.

Definition chaotic_bicat_data : bicat_data.
Proof.
  use tpair.
  - use tpair.
    + exact C.
    + cbn. intros a b f g. exact unit.
  - cbn; repeat (use tpair).
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + intros; exact tt.
    + cbn. intros. exact tt.
Defined.

Definition chaotic_bicat_laws : bicat_laws chaotic_bicat_data.
Proof.
  repeat (use tpair); cbn; intros;
    apply isProofIrrelevantUnit.
Qed.

End chaotic_bicat.


Section discrete_bicat.

Variable C : category.

Definition discrete_bicat_data : bicat_data.
Proof.
  use tpair.
  - use tpair.
    + exact C.
    + cbn. intros a b f g. exact (f = g).
  - cbn; repeat (use tpair); cbn.
    + intros. apply idpath.
    + intros. apply id_left.
    + intros. apply id_right.
    + intros. apply (!id_left _).
    + intros. apply (!id_right _).
    + intros. apply (! assoc _ _ _ ).
    + intros. apply assoc.
    + intros a b f g h r s. apply (r @ s).
    + intros. apply (maponpaths). assumption.
    + intros. apply (maponpaths_2). assumption.
Defined.

Definition discrete_bicat_laws : bicat_laws discrete_bicat_data.
Proof.
  repeat (use tpair); cbn.
  - intros. apply idpath.
  - intros. apply pathscomp0rid.
  - intros. apply path_assoc.
  - intros. apply idpath.
  - intros. apply idpath.
  - intros. apply pathsinv0. apply maponpathscomp0.
  - intros. unfold maponpaths_2.
    apply pathsinv0. apply (@maponpathscomp0  _ _ _ _ _ (λ x0 : C ⟦ a, b ⟧, x0 · i)).
  - intros. induction x. simpl. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. simpl. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x. simpl. apply pathsinv0. apply (pathscomp0rid).
  - intros. induction x; simpl. apply (pathscomp0rid).
  - intros. induction x; induction y; simpl. apply idpath.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply pathsinv0r.
  - intros. apply pathsinv0l.
  - intros. apply homset_property.
  - intros. apply homset_property.
Qed.

End discrete_bicat.


Definition psfunctor_ob_mor_cell (C C' : bicat_data) : UU
  := ∑ F : functor_data C C',
           ∏ a b (f g : a --> b), f ==> g → #F f ==> #F g.

Coercion functor_data_from_bifunctor_ob_mor_cell C C' (F : psfunctor_ob_mor_cell C C')
  : functor_data C C' := pr1 F.

Definition psfunctor_on_cells {C C' : bicat_data} (F : psfunctor_ob_mor_cell C C')
           {a b : C} {f g : a --> b} (x : f ==> g)
  : #F f ==> #F g
  := pr2 F a b f g x.

Notation "'##'" := (psfunctor_on_cells).

Definition psfunctor_cell_data {C C' : bicat_data} (F : psfunctor_ob_mor_cell C C') : UU
  :=
    (∏ (a : C), equivalence (#F (identity a)) (identity _) )
      ×
    (∏ (a b c : C) (f : a --> b) (g : b --> c),
     equivalence (#F (f · g)) (#F f · #F g)).

Definition psfunctor_data (C C' : bicat_data) : UU
  := ∑ F : psfunctor_ob_mor_cell C C', psfunctor_cell_data F.

Coercion psfunctor_ob_mor_cell_from_bifunctor_data C C' (F : psfunctor_data C C')
  : psfunctor_ob_mor_cell _ _ := pr1 F.




Definition psfunctor_id {C C' : bicat_data} (F : psfunctor_data C C') (a : C)
  : equivalence (#F (identity a)) (identity _)
  := pr1 (pr2 F) a.
Definition psfunctor_comp {C C' : bicat_data} (F : psfunctor_data C C') {a b c : C}
           (f : a --> b) (g : b --> c)
  : equivalence (#F (f · g)) (#F f · #F g)
  := pr2 (pr2 F) a b c f g.


Section psfunctor_laws.

Context {C C' : bicat_data} (F : psfunctor_data C C').


Definition psfunctor_id2_law : UU
  := ∏ (a b : C) (f : a --> b), ## F (id2 f) = id2 _ .

Definition psfunctor_lunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
     ## F (lunitor f) =
     (psfunctor_comp F (identity a) f) • (psfunctor_id _ _ ▹ #F f) • lunitor (#F f).

Definition psfunctor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
     ## F (runitor f) =
     (psfunctor_comp F f (identity b)) • (# F f ◃ psfunctor_id _ _ ) • runitor (#F f).


Definition psfunctor_linvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
     ## F (linvunitor f) =
     linvunitor (#F f)
                • (inv_equivalence (psfunctor_id F a) ▹ #F f)
                • (inv_equivalence (psfunctor_comp F _ _ )).

Definition psfunctor_rinvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a, b⟧),
     ## F (rinvunitor f) =
     rinvunitor (#F f)
                • (#F f ◃ inv_equivalence (psfunctor_id F b))
                • (inv_equivalence (psfunctor_comp F _ _ )).

Definition psfunctor_rassociator_law : UU
  := ∏ {a b c d : C}
       (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
     ##F (rassociator f g h) =
     (psfunctor_comp F _ _ ) • (psfunctor_comp F _ _ ▹ #F h) • rassociator (#F f) (#F g) (#F h)
                             • (#F f ◃ inv_equivalence (psfunctor_comp F _ _ ))
                             • (inv_equivalence (psfunctor_comp F _ _ )).

Definition psfunctor_lassociator_law : UU
  := ∏ {a b c d : C}
       (f : C⟦a, b⟧) (g : C⟦b, c⟧) (h : C⟦c, d⟧),
     ##F (lassociator f g h) =
     (psfunctor_comp F _ _ ) • (#F f ◃ psfunctor_comp F _ _ ) • lassociator (#F f) (#F g) (#F h)
                             • (inv_equivalence (psfunctor_comp F _ _ )▹ #F _ )
                             • (inv_equivalence (psfunctor_comp F _ _ )).

Definition psfunctor_vcomp2_law : UU
  := ∏ {a b : C} {f g h: C⟦a, b⟧}
       (η : f ==> g) (φ : g ==> h),
     ##F (η • φ) = ##F η • ##F φ.

Definition psfunctor_lwhisker_law : UU
  := ∏ {a b c : C} (f : C⟦a, b⟧) {g1 g2 : C⟦b, c⟧}
       (η : g1 ==> g2),
     ##F (f ◃ η) =
     (psfunctor_comp F _ _ ) • (#F f ◃ ##F η) • (inv_equivalence (psfunctor_comp F _ _ )).

Definition psfunctor_rwhisker_law : UU
  := ∏ {a b c : C} {f1 f2 : C⟦a, b⟧} (g : C⟦b, c⟧)
       (η : f1 ==> f2),
     ##F (η ▹ g) =
     (psfunctor_comp F _ _ ) • (##F η ▹ #F g) • (inv_equivalence (psfunctor_comp F _ _ )).

Definition psfunctor_laws : UU
  :=
    psfunctor_id2_law
      × psfunctor_lunitor_law
      × psfunctor_runitor_law
      × psfunctor_linvunitor_law
      × psfunctor_rinvunitor_law
      × psfunctor_rassociator_law
      × psfunctor_lassociator_law
      × psfunctor_vcomp2_law
      × psfunctor_lwhisker_law
      × psfunctor_rwhisker_law.

End psfunctor_laws.



Section op2.

Variable C : bicat.

Definition op2_bicat_1_id_comp_cells : bicat_1_id_comp_cells.
Proof.
  exists C.
  intros a b f g. exact (g ==> f).
Defined.

Definition op2_bicat_data : bicat_data.
Proof.
  exists op2_bicat_1_id_comp_cells.
  repeat (use tpair).
  - intros; apply id2.
  - intros; cbn. apply linvunitor.
  - intros; cbn. apply rinvunitor.
  - intros; cbn. apply lunitor.
  - intros; cbn. apply runitor.
  - intros; cbn. apply lassociator.
  - intros; cbn. apply rassociator.
  - intros; cbn. apply ( X0 • X ).
  - intros; cbn. apply ( f ◃ X ).
  - cbn; intros. apply (X ▹ g).
Defined.

Definition op2_bicat_laws : bicat_laws op2_bicat_data.
Proof.
  repeat split; intros; cbn.
  - apply id2_right.
  - apply id2_left.
  - apply (!vassocr _ _ _ ).
  - apply lwhisker_id2.
  - apply id2_rwhisker.
  - apply lwhisker_vcomp.
  - apply rwhisker_vcomp.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - apply (!vcomp_whisker _ _  ).
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
  - admit.
  - admit.
Admitted.
End op2.

(* ----------------------------------------------------------------------------------- *)
(** Associators and unitors are isos. *)

Section Associators_Unitors_Iso.

Context {C : bicat}.

Lemma lassociator_iso {a b c d : C} (f : hom a b) (g : hom b c) (h : hom c d)
  : is_iso (lassociator f g h : (hom a d) ⟦ f · (g · h), (f · g) · h ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (rassociator f g h).
  split.
  - apply lassociator_rassociator.
  - apply rassociator_lassociator.
Defined.

Lemma lunitor_iso {a b : C} (f : hom a b)
  : is_iso (lunitor f : (hom a b) ⟦ identity a · f, f ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (linvunitor f).
  split.
  - apply lunitor_linvunitor.
  - apply linvunitor_lunitor.
Defined.

Lemma runitor_iso {a b : C} (f : hom a b)
  : is_iso (runitor f : (hom a b) ⟦ f · identity b, f ⟧).
Proof.
  apply is_iso_from_is_z_iso.
  exists (rinvunitor f).
  split.
  - apply runitor_rinvunitor.
  - apply rinvunitor_runitor.
Defined.

End Associators_Unitors_Iso.

(* ----------------------------------------------------------------------------------- *)
(** Functor structure on associators and unitors. *)

Section Associators_Unitors_Natural.

Context {C : bicat}.

(** Left unitor *)

Lemma lunitor_natural (a b : C)
  : is_nat_trans
      (bindelta_pair_functor
         (constant_functor (hom a b) (hom a a) (identity a))
         (functor_identity (hom a b)) ∙
       hcomp_functor)
      (functor_identity (hom a b))
      lunitor.
Proof.
  red. cbn. intros f g x. unfold hcomp1.
  rewrite <- vassocr. rewrite vcomp_lunitor.
  rewrite vassocr. apply maponpaths_2.
  rewrite id2_rwhisker. apply id2_left.
Defined.

Definition lunitor_transf (a b : C)
  : bindelta_pair_functor
      (constant_functor (hom a b) (hom a a) (identity a))
      (functor_identity (hom a b)) ∙
    hcomp_functor
    ⟹
    functor_identity (hom a b).
Proof.
  exists lunitor. apply lunitor_natural.
Defined.

(** Right unitor *)

Lemma runitor_natural (a b : C)
  : is_nat_trans
      (bindelta_pair_functor
         (functor_identity (hom a b))
         (constant_functor (hom a b) (hom b b) (identity b)) ∙
       hcomp_functor)
      (functor_identity (hom a b))
      runitor.
Proof.
  red. cbn. intros f g x.
  rewrite hcomp1_hcomp2. unfold hcomp2.
  rewrite <- vassocr.
  rewrite vcomp_runitor.
  rewrite vassocr. apply maponpaths_2.
  rewrite lwhisker_id2. apply id2_left.
Defined.

Definition runitor_transf (a b : C)
  : bindelta_pair_functor
       (functor_identity (hom a b))
       (constant_functor (hom a b) (hom b b) (identity b)) ∙
    hcomp_functor
    ⟹
    functor_identity (hom a b).
Proof.
  exists runitor. apply runitor_natural.
Defined.

Print runitor_transf.

(** Left associator. *)

Definition lassociator_fun {a b c d : C}
           (x : C ⟦ a, b ⟧ × C ⟦ b, c ⟧ × C ⟦ c, d ⟧)
  :  pr1 x · (pr12 x · pr22 x) ==> (pr1 x · pr12 x) · pr22 x
  := lassociator (pr1 x) (pr12 x) (pr22 x).

Lemma lassociator_fun_natural {a b c d : C}
  : is_nat_trans
      (pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor)
      (precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
       pair_functor hcomp_functor (functor_identity (hom c d)) ∙
       hcomp_functor)
      lassociator_fun.
Proof.
  red; cbn. intros (f1, (f2, f3)) (g1, (g2, g3)).
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  intros (x1, (x2, x3)). simpl.
  unfold lassociator_fun. simpl.
  apply hcomp1_lassoc.
Defined.

Definition lassociator_transf (a b c d : C)
  : pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor
    ⟹
    precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor.
Proof.
  exists lassociator_fun. exact lassociator_fun_natural.
Defined.

(** Right associator. *)

Definition rassociator_fun {a b c d : C}
           (x : C ⟦ a, b ⟧ × C ⟦ b, c ⟧ × C ⟦ c, d ⟧)
  : (pr1 x · pr12 x) · pr22 x ==> pr1 x · (pr12 x · pr22 x)
  := rassociator (pr1 x) (pr12 x) (pr22 x).

Lemma rassociator_fun_natural {a b c d : C}
  : is_nat_trans
      (precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
       pair_functor hcomp_functor (functor_identity (hom c d)) ∙
       hcomp_functor)
      (pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor)
      rassociator_fun.
Proof.
  red; cbn. intros (f1, (f2, f3)) (g1, (g2, g3)).
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  unfold precategory_binproduct_mor, hom_ob_mor. simpl.
  intros (x1, (x2, x3)). simpl.
  unfold rassociator_fun. simpl.
  apply hcomp1_rassoc.
Defined.

Definition rassociator_transf (a b c d : C)
  : precategory_binproduct_assoc (hom a b) (hom b c) (hom c d) ∙
    pair_functor hcomp_functor (functor_identity (hom c d)) ∙
    hcomp_functor
    ⟹
    pair_functor (functor_identity (hom a b)) hcomp_functor ∙ hcomp_functor.
Proof.
  exists rassociator_fun. exact rassociator_fun_natural.
Defined.

End Associators_Unitors_Natural.

