(** * Other structures in [HSET] *)

(** ** Contents

  - Natural numbers object ([NNO_HSET])
  - Exponentials ([Exponentials_HSET])
  - Construction of exponentials for functors into HSET
    ([Exponentials_functor_HSET])
  - Kernel pairs ([kernel_pair_HSET])
  - Effective epis ([EffectiveEpis_HSET])
  - Split epis with axiom of choice ([SplitEpis_HSET])
  - Forgetful [functor] to [type_precat]

Written by: Benedikt Ahrens, Anders Mörtberg

October 2015 - January 2016

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA. (* flip *)
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.AxiomOfChoice.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.slicecat.
Require Import UniMath.CategoryTheory.NNO.
Require Import UniMath.CategoryTheory.SubobjectClassifier.
Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.covyoneda.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Monics.

Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.

Local Open Scope cat.

(** ** Natural numbers object ([NNO_HSET]) *)

Lemma isNNO_nat : isNNO TerminalHSET natHSET (λ _, 0) S.
Proof.
  intros X z s.
  use unique_exists.
  + intros n.
    induction n as [|_ n].
    * exact (z tt).
    * exact (s n).
  + now split; apply funextfun; intros [].
  + now intros; apply isapropdirprod; apply setproperty.
  + intros q [hq1 hq2].
    apply funextfun; intros n.
    induction n as [|n IH].
    * now rewrite <- hq1.
    * cbn in *; now rewrite (toforallpaths _ _ _ hq2 n), IH.
Qed.

Definition NNO_HSET : NNO TerminalHSET.
Proof.
  use mk_NNO.
  - exact natHSET.
  - exact (λ _, 0).
  - exact S.
  - exact isNNO_nat.
Defined.

(** ** Exponentials ([Exponentials_HSET]) *)

Section exponentials.

(** Define the functor: A -> _^A *)
Definition exponential_functor (A : HSET) : functor HSET HSET.
Proof.
use tpair.
+ exists (hset_fun_space A); simpl.
  intros b c f g; apply (λ x, f (g x)).
+ abstract (use tpair;
  [ intro x; now (repeat apply funextfun; intro)
  | intros x y z f g; now (repeat apply funextfun; intro)]).
Defined.

(** This checks that if we use constprod_functor2 the flip is not necessary *)
Lemma are_adjoints_constprod_functor2 A :
  are_adjoints (constprod_functor2 BinProductsHSET A) (exponential_functor A).
Proof.
use tpair.
- use tpair.
  + use tpair.
    * intro x; simpl; apply dirprodpair.
    * abstract (intros x y f; apply idpath).
  + use tpair.
    * intros X fx; apply (pr1 fx (pr2 fx)).
    * abstract (intros x y f; apply idpath).
- abstract (use tpair;
  [ intro x; simpl; apply funextfun; intro ax; reflexivity
  | intro b; apply funextfun; intro f; apply idpath]).
Defined.

Lemma Exponentials_HSET : Exponentials BinProductsHSET.
Proof.
intro a.
exists (exponential_functor a).
use tpair.
- use tpair.
  + use tpair.
    * intro x; simpl; apply flip, dirprodpair.
    * abstract (intros x y f; apply idpath).
  + use tpair.
    * intros x xf; simpl in *; apply (pr2 xf (pr1 xf)).
    * abstract (intros x y f; apply idpath).
- abstract (use tpair;
  [ now intro x; simpl; apply funextfun; intro ax; reflexivity
  | now intro b; apply funextfun; intro f]).
Defined.

End exponentials.

(** ** Construction of exponentials for functors into HSET *)

(** This section defines exponential in [C,HSET] following a slight
variation of Moerdijk-MacLane (p. 46, Prop. 1).

The formula for [C,Set] is G^F(f)=Hom(Hom(f,−)×id(F),G) taken from:

http://mathoverflow.net/questions/104152/exponentials-in-functor-categories
*)
Section exponentials_functor_cat.

Variable (C : precategory) (hsC : has_homsets C).

Let CP := BinProducts_functor_precat C _ BinProductsHSET has_homsets_HSET.
Let cy := covyoneda _ hsC.

(* Defined Q^P *)
Local Definition exponential_functor_cat (P Q : functor C HSET) : functor C HSET.
Proof.
use tpair.
- use tpair.
  + intro c.
    use hSetpair.
    * apply (nat_trans (BinProduct_of_functors C _ BinProductsHSET (cy c) P) Q).
    * abstract (apply (isaset_nat_trans has_homsets_HSET)).
  + simpl; intros a b f alpha.
    apply (BinProductOfArrows _ (CP (cy a) P) (CP (cy b) P)
                           (# cy f) (identity _) · alpha).
- abstract (
    split;
      [ intros c; simpl; apply funextsec; intro a;
        apply (nat_trans_eq has_homsets_HSET); cbn; unfold prodtofuntoprod; intro x;
        apply funextsec; intro f;
        destruct f as [cx Px]; simpl; unfold covyoneda_morphisms_data;
        now rewrite id_left
      | intros a b c f g; simpl; apply funextsec; intro alpha;
        apply (nat_trans_eq has_homsets_HSET); cbn; unfold prodtofuntoprod; intro x;
        apply funextsec; intro h;
        destruct h as [cx pcx]; simpl; unfold covyoneda_morphisms_data;
        now rewrite assoc ]).
Defined.

Local Definition eval (P Q : functor C HSET) :
  nat_trans (BinProductObject _ (CP P (exponential_functor_cat P Q)) : functor _ _) Q.
Proof.
use tpair.
- intros c ytheta; set (y := pr1 ytheta); set (theta := pr2 ytheta);
  simpl in *.
  use (theta c).
  exact (identity c,,y).
- abstract (
    intros c c' f; simpl;
    apply funextfun; intros ytheta; destruct ytheta as [y theta];
    cbn; unfold prodtofuntoprod;
    unfold covyoneda_morphisms_data;
    assert (X := nat_trans_ax theta);
    assert (Y := toforallpaths _ _ _ (X c c' f) (identity c,, y));
    eapply pathscomp0; [|apply Y]; cbn; unfold prodtofuntoprod;
    now rewrite id_right, id_left).
Defined.

(* This could be made nicer without the big abstract blocks... *)
Lemma Exponentials_functor_HSET : Exponentials CP.
Proof.
intro P.
use left_adjoint_from_partial.
- apply (exponential_functor_cat P).
- intro Q; simpl; apply eval.
- intros Q R φ; simpl in *.
  use tpair.
  + use tpair.
    * { use mk_nat_trans.
        - intros c u; simpl.
          use mk_nat_trans.
          + simpl; intros d fx.
            apply (φ d (dirprodpair (pr2 fx) (# R (pr1 fx) u))).
          + intros a b f; simpl; cbn; unfold prodtofuntoprod.
            apply funextsec; intro x.
            etrans;
              [|apply (toforallpaths _ _ _ (nat_trans_ax φ _ _ f)
                                     (dirprodpair (pr2 x) (# R (pr1 x) u)))]; cbn.
              repeat (apply maponpaths).
              assert (H : # R (pr1 x · f) = # R (pr1 x) · #R f).
              { apply functor_comp. }
              unfold prodtofuntoprod.
              simpl (pr1 _); simpl (pr2 _).
              apply maponpaths.
              apply (eqtohomot H u).
        - intros a b f; cbn.
          apply funextsec; intros x; cbn.
          apply subtypeEquality;
            [intros xx; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|].
          apply funextsec; intro y; apply funextsec; intro z; cbn.
          repeat apply maponpaths;  unfold covyoneda_morphisms_data.
          assert (H : # R (f · pr1 z) = # R f · # R (pr1 z)).
          { apply functor_comp. }
          apply pathsinv0.
          now etrans; [apply (toforallpaths _ _ _ H x)|].
      }
    * abstract (
        apply (nat_trans_eq has_homsets_HSET); cbn; intro x;
        apply funextsec; intro p;
        apply maponpaths;
        assert (H : # R (identity x) = identity (R x));
          [apply functor_id|];
        induction p as [t p]; apply maponpaths; simpl;
        now apply pathsinv0; eapply pathscomp0; [apply (toforallpaths _ _ _ H p)|]).
  + abstract (
    intros [t p]; apply subtypeEquality; simpl;
    [intros x; apply (isaset_nat_trans has_homsets_HSET)|];
    apply (nat_trans_eq has_homsets_HSET); intros c;
    apply funextsec; intro rc;
    apply subtypeEquality;
    [intro x; apply (isaprop_is_nat_trans _ _ has_homsets_HSET)|]; simpl;
    rewrite p; cbn; clear p; apply funextsec; intro d; cbn;
    apply funextsec; intros [t0 pd]; simpl;
    assert (HH := toforallpaths _ _ _ (nat_trans_ax t c d t0) rc);
    cbn in HH; rewrite HH; cbn; unfold covyoneda_morphisms_data;
    unfold prodtofuntoprod;
    now rewrite id_right).
Qed.

End exponentials_functor_cat.

(** ** Kernel pairs ([kernel_pair_HSET]) *)

(* proof by Peter, copied from TypeTheory.Auxiliary.Auxiliary *)
Lemma pullback_HSET_univprop_elements {P A B C : HSET}
    {p1 : HSET ⟦ P, A ⟧} {p2 : HSET ⟦ P, B ⟧}
    {f : HSET ⟦ A, C ⟧} {g : HSET ⟦ B, C ⟧}
    (ep : p1 · f = p2 · g)
    (pb : isPullback f g p1 p2 ep)
  : (∏ a b (e : f a = g b), ∃! ab, p1 ab = a × p2 ab = b).
Proof.
  intros a b e.
  set (Pb := (mk_Pullback _ _ _ _ _ _ pb)).
  apply iscontraprop1.
  - apply invproofirrelevance; intros [ab [ea eb]] [ab' [ea' eb']].
    apply subtypeEquality; simpl.
      intros x; apply isapropdirprod; apply setproperty.
    use (@toforallpaths unitset _ (λ _, ab) (λ _, ab') _ tt).
    use (MorphismsIntoPullbackEqual pb);
    apply funextsec; intros []; cbn;
    (eapply @pathscomp0; [ eassumption | apply pathsinv0; eassumption]).
  - use (_,,_).
    use (_ tt).
    use (PullbackArrow Pb (unitset : HSET)
      (λ _, a) (λ _, b)).
    apply funextsec; intro; exact e.
    simpl; split.
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr1 Pb unitset).
    + generalize tt; apply toforallpaths.
      apply (PullbackArrow_PullbackPr2 Pb unitset).
Defined.


Section kernel_pair_Set.

  Context  {A B:HSET}.
  Variable (f: HSET ⟦A,B⟧).


  Definition kernel_pair_HSET : kernel_pair f.
    red.
    apply PullbacksHSET.
  Defined.

  Local Notation g := kernel_pair_HSET.

  (** Formulation in the categorical language of the universal property
      enjoyed by surjections (univ_surj) *)
  Lemma isCoeqKernelPairSet (hf:issurjective f) :
    isCoequalizer _ _ _ (PullbackSqrCommutes g).
  Proof.
    intros.
    red.
    intros C u equ.
    assert (hcompat :   ∏ x y : pr1 A, f x = f y → u x = u y).
    {
      intros x y eqfxy.
      assert (hpb:=pullback_HSET_univprop_elements
                     (PullbackSqrCommutes g) (isPullback_Pullback g) x y eqfxy).
      assert( hpb' := pr2 (pr1 hpb)); simpl in hpb'.
      etrans.
      eapply pathsinv0.
      apply maponpaths.
      exact (pr1 hpb').
      eapply pathscomp0.
      apply toforallpaths in equ.
      apply equ.
      cbn.
      apply maponpaths.
      exact (pr2 hpb').
    }
    use (unique_exists (univ_surj (setproperty C) _ _ _ hf)).
    - exact u.
    - exact hcompat.
    - simpl.
      apply funextfun.
      intros ?.
      apply univ_surj_ax.
    - intros ?. apply has_homsets_HSET.
    - intros ??; simpl.
      apply funextfun.
      use univ_surj_unique.
      simpl in X.
      apply toforallpaths in X.
      exact X.
  Qed.
End kernel_pair_Set.

(** ** Effective epis ([EffectiveEpis_HSET]) *)

Lemma EffectiveEpis_HSET : EpisAreEffective HSET.
Proof.
  red.
  clear.
  intros A B f epif.
  exists (kernel_pair_HSET f).
  apply isCoeqKernelPairSet.
  now apply EpisAreSurjective_HSET.
Qed.

(** ** Split epis with axiom of choice ([SplitEpis_HSET]) *)

Lemma SplitEpis_HSET : AxiomOfChoice_surj -> EpisAreSplit HSET.
Proof.
  intros axC A B f epif.
  apply EpisAreSurjective_HSET,axC in epif.
  unshelve eapply (hinhfun _ epif).
  intro h.
  exists (pr1 h).
  apply funextfun.
  exact (pr2 h).
Qed.

(** ** Forgetful [functor] to [type_precat] *)

Definition forgetful_HSET : functor HSET type_precat.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + exact pr1.
    + exact (λ _ _, idfun _).
  - split.
    + intro; reflexivity.
    + intros ? ? ? ? ?; reflexivity.
Defined.

(** This functor is conservative; it reflects isomorphisms. *)

Lemma conservative_forgetful_HSET : conservative forgetful_HSET.
Proof.
  unfold conservative.
  intros a b f is_iso_forget_f.
  refine (hset_equiv_is_iso a b (weqpair f _)).
  apply (type_iso_is_equiv _ _ (isopair _ is_iso_forget_f)).
Defined.

(** ** Subobject classifier *)

(* Lemma standard_pullback_inverse_image_of_point {X Y : hSet} (f : HSET⟦X, Y⟧) *)
(*       (y : Y) (y' := invweq (weqfunfromunit_HSET _) y) : *)
(*   pr1hSet (PullbackObject (PullbacksHSET _ _ _ f y')) ≃ hfiber f y. *)
(* Proof. *)
(*   unfold PullbacksHSET; cbn. *)
(*   unfold hfiber; cbn. *)
(*   apply (@weqcomp _ (∑ xy : X × unit, f (pr1 xy) = invmap (weqfunfromunit_HSET Y) y tt) _). *)
(*   - apply weqfibtototal; intro. *)
(*     apply transitive_paths_weq_reverse. *)
(*     apply maponpaths. *)
(*     apply isProofIrrelevantUnit. *)
(*   - apply (@weqcomp _ (∑ xy : X × unit, f (pr1 xy) = y)). *)
(*     + apply weqfibtototal; intro. *)
(*       apply transitive_paths_weq_reverse. *)
(*       reflexivity. *)
(*     + apply invweq. *)
(*       apply (weqfp (weqtodirprodwithunit X) (fun z => f (pr1 z) = y)). *)
(* Defined. *)


Local Lemma switchPullbackPr1 {C : category} {A B D : C} {f : A --> D} {g : B --> D}
           (pb : Pullback f g) : PullbackPr1 pb = PullbackPr2 (switchPullback pb).
Proof.
  reflexivity.
Qed.

Local Lemma switchPullbackPr2 {C : category} {A B D : C} {f : A --> D} {g : B --> D}
           (pb : Pullback f g) : PullbackPr2 pb = PullbackPr1 (switchPullback pb).
Proof.
  reflexivity.
Qed.

Definition hProp_set : hSet := (_,, isasethProp).

Lemma isaprop_hfiber_monic {A B : hSet} (f : HSET⟦A, B⟧) (isM : isMonic f) :
  isPredicate (hfiber f).
Proof.
  intro.
  apply incl_injectivity.
  apply MonosAreInjective_HSET.
  assumption.
Qed.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Local Definition const_unit {X : hSet} : HSET⟦X, hProp_set⟧ :=
  (fun _ => (unit,, isapropunit) : hProp_set).

(** Existence of the pullback square
    <<
      X -------> TerminalHSET
      V              V
    m |              | true
      V     ∃!       V
      Y - - - - -> hProp
    >>
  *)
Local Definition subobject_classifier_HSET_pullback {X Y : HSET}
  (m : Monic HSET X Y) :
    ∑ (chi : HSET ⟦ Y, hProp_set ⟧)
    (H : m · chi = TerminalArrow TerminalHSET X · const_unit),
      isPullback chi const_unit m (TerminalArrow TerminalHSET X) H.
Proof.
  exists (fun z => (hfiber (pr1 m) z,, isaprop_hfiber_monic (pr1 m) (pr2 m) z)).
  use tpair.
  + apply funextfun; intro.
    apply weqtopathshProp, weqimplimpl.
    * intro; exact tt.
    * intro; cbn.
      use tpair.
      -- assumption.
      -- reflexivity.
    * apply propproperty.
    * apply propproperty.
  + (** The aforementioned square is a pullback *)
    cbn beta.
    unfold isPullback; cbn.
    intros Z f g H.
    use iscontrpair.
    * use tpair.
      -- (** The hypothesis H states that that each [f x] is in the image of [m],
              and since [m] is monic (injective), this assignment extends to a map
              [Z -> X] defined by [z ↦ m^-1 (f z)]. *)
          intro z.
          eapply hfiberpr1.
          eapply eqweqmap.
          ++ apply pathsinv0.
            apply (maponpaths pr1 (toforallpaths _ _ _ H z)).
          ++ exact tt.
      -- split.
          ++ (** The first triangle commutes by definition of the above map:
                [m] sends the preimage [m^-1 (f z)] to [f z]. *)
            apply funextfun; intro z; cbn.
            apply hfiberpr2.
          ++ (** All maps to the terminal object are equal *)
            apply proofirrelevance, impred.
            intro; apply isapropunit.
    * intro.
      apply subtypeEquality.
      -- intro.
          apply isapropdirprod.
          ++ apply (setproperty (hset_fun_space _ _)).
          ++ apply (setproperty (hset_fun_space _ unitset)).
      -- cbn.
          apply funextsec; intro; cbn.
          (** Precompose with [m] and use the commutative square *)
          apply (invweq (weqpair _ (MonosAreInjective_HSET (pr1 m) (pr2 m) _ _))).
          eapply pathscomp0.
          ++ apply (toforallpaths _ _ _ (pr1 (pr2 t))).
          ++ apply pathsinv0.
             apply hfiberpr2.
Defined.

(* Lemma hfiber_of_incl_weq : *)
(*   ∏ (X Y : UU) (f : X → Y), isincl f → X ≃ ∑ y : Y, hfiber f y. *)
(* Proof. *)
(*  iscontrhfiberofincl: *)
Lemma sum_of_fibers {A B:Type} (f: A -> B) :
  (∑ b:B, hfiber f b) ≃ A.
Proof.
  use weqpair.
  - intro bap. exact (pr1 (pr2 bap)).
  - intro a. use iscontrpair.
    + use hfiberpair.
      * exists (f a).
        use hfiberpair.
        { exact a. }
        { reflexivity. }
      * cbn. reflexivity.
    + intro b1a1p1p. induction b1a1p1p as [b1a1p1 p]. induction p.
      induction b1a1p1 as [b1 [a1 p1]]. induction p1. reflexivity.
Defined.

(** In the above diagram, [m] must pick out the same subset of [Y]
    that the induced arrow does. *)
Local Definition subobject_classifier_HSET_subset {X Y : HSET}
      {m : Monic HSET X Y} :
  pr1hSet X ≃ carrier (pr1 (subobject_classifier_HSET_pullback m)).
Proof.
  pose (H := pr2 (subobject_classifier_HSET_pullback m)).
  unfold subobject_classifier_HSET_pullback; cbn.
  eapply weqcomp.
  - apply invweq.
    apply (sum_of_fibers (pr1 m)).
  - apply eqweqmap.
    reflexivity.
Defined.

(** More generally, any subset that commutes with the arrow "true"
    must pick out that same subset that [m] does. *)
Local Definition subobject_classifier_HSET_pullback0 {X Y : HSET}
  (m : Monic HSET X Y) (chi : HSET ⟦ Y, hProp_set ⟧)
  (H : m · chi = TerminalArrow TerminalHSET X · const_unit)
  (isPB : isPullback chi const_unit m (TerminalArrow TerminalHSET X) H) :
  (pr1hSet X) ≃ carrier chi.
Proof.
  eapply weqcomp.
  - apply invweq.
    apply (sum_of_fibers (pr1 m)).
  - apply weqfibtototal.
    intros y.
    apply weqimplimpl.
    + (** If we have something in the fiber above [y], then we know we can get
          something in [chi], because [chi] after [m] is trivially true by [H]. *)
      intros hfib.
      pose (HH := H). (* Can't change H directly, it's used in isPB *)
      apply toforallpaths in HH.
      specialize (HH (hfiberpr1 _ _ hfib)).
      cbn in HH.
      apply (fun p => (!maponpaths _ (hfiberpr2 _ _ hfib)) @ p) in HH.
      abstract (rewrite HH; exact tt).
    + (** Conversely, if we have something in [chi], we can get something in
          the fiber above [y] because ... *)
      intros chii.
      admit.
Admitted.

Definition subobject_classifier_HSET : subobject_classifier TerminalHSET.
Proof.
  unfold subobject_classifier.
  exists hProp_set.
  exists (fun _ => ((unit,, isapropunit) : hProp_set)).
  intros ? ? m.

  use iscontrpair.

  - (** The image of m *)
    apply subobject_classifier_HSET_pullback.
  - intro O'.
    apply subtypeEquality.
    + intro.
      apply Propositions.isaproptotal2.
      * intro; apply isaprop_isPullback.
      * intros; apply proofirrelevance.
        apply setproperty.
    + cbn.
      Check subobject_classifier_HSET_pullback0 m.
      apply funextfun; intro y.
      (** If the following is a pullback square,
          <<
            X ------- ! ---> unit
            |                 |
            |                 |
            V                 V
            Y -- pr1 O' --> hProp
          >>
          then [pr1 O' = m].
       *)


      (****************************************************)
      (* apply subtypeEquality; [intro; apply isapropisaprop|]. *)
      apply weqtopathshProp.
      apply weqimplimpl.
      * (** [O'] and [∥hfiber ...∥] are both subtypes of Y.
            Why must they contain the same elements?
            The equality (pr1 (pr2 O')) tells us they must agree on
            things in the image of m. *)
        pose (pb := tpair _ (tpair _ X (dirprodpair (pr1 m) (TerminalArrow TerminalHSET X))) (pr2 O') : Pullback _ _).
        refine (PullbackArrow pb X m (TerminalArrow _ _) _).
        assert (Pullback (pr1 O') (global_element_HSET ((unit,, isapropunit) : hProp_set))).
        {
          use tpair.
          - eapply tpair.
            use dirprodpair.
            + exact m.
            + exact (TerminalArrow TerminalHSET X).
          - exact (pr2 O').
        }
        Print X0.
        eapply PullbackArrow.
        Check PullbackArrow (pr1 O' ,, _).
        intro; unfold hProptoType; cbn.
  H : (λ x : Z, hfiber (pr1 m) (f x),, isaprop_hfiber_monic (pr1 m) (pr2 m) (f x)) =
      (λ x : Z, global_element_HSET (unit,, isapropunit) (g x))
        assert (m · pr1 O' = m · (fun z => (hfiber (pr1 m) z,, isaprop_hfiber_monic (pr1 m) (pr2 m) z : pr1hSet hProp_set))).
        {
          refine (pr1 (pr2 O') @ _).
          admit. (** Proven in first part *)
        }
        pose (xx := toforallpaths _ _ _ (pr1 (pr2 O'))).
        pose (xxx := toforallpaths _ _ _ X0).
        cbn in xx.
        cbn in xxx.