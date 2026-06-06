Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Tripos.
Require Import UniMath.CategoryTheory.Hyperdoctrines.Properties.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.ElementaryTopos.ToposOperations.
Require Import UniMath.CategoryTheory.ElementaryTopos.PredicateDispCat.
Require Import UniMath.CategoryTheory.ElementaryTopos.ToposLogic.
Require Import UniMath.CategoryTheory.ElementaryTopos.FunctionalCompleteness.

Local Open Scope cat.
Local Open Scope hd.

Section ToposInitial.
  Context (E : Topos).

  Let EE : tripos := topos_logic_tripos E.

  Definition topos_initial_obj_form
    : form (𝟙 : ty EE)
    := ⊥.

  Definition topos_initial_obj
    : E
    := formula_comprehension (topos_logic_comprehension_hd E) topos_initial_obj_form.

  Proposition topos_initial_mor_eq
              {x : E}
              (f g : topos_initial_obj --> x)
    : f = g.
  Proof.
    use topos_logic_extensionality.
    use forall_intro.
    use false_elim.
    refine (hyperdoctrine_cut
              (formula_comprehension_prf_tm
                 (topos_logic_comprehension_hd E)
                 _
                 (π₂ (tm_var _)) )
              _).
    unfold topos_initial_obj_form.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Definition topos_initial_mor
             (x : E)
    : topos_initial_obj --> x.
  Proof.
    use (functional_relation_to_mor
           (topos_logic_functional_completeness E)).
    {
      exact ⊥.
    }
    use conj_intro.
    - use forall_intro.
      use false_elim.
      refine (hyperdoctrine_cut
                (formula_comprehension_prf_tm
                   (topos_logic_comprehension_hd E)
                   _
                   (π₂ (tm_var _)) )
                _).
      unfold topos_initial_obj_form.
      simplify.
      apply hyperdoctrine_hyp.
    - use forall_intro.
      use false_elim.
      refine (hyperdoctrine_cut
                (formula_comprehension_prf_tm
                   (topos_logic_comprehension_hd E)
                   _
                   (π₂ (tm_var _)) )
                _).
      unfold topos_initial_obj_form.
      simplify.
      apply hyperdoctrine_hyp.
  Defined.

  Definition topos_initial
    : Initial E.
  Proof.
    use make_Initial.
    - exact topos_initial_obj.
    - intro x.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           exact topos_initial_mor_eq).
      + exact (topos_initial_mor x).
  Defined.


  Definition isEmpty_form
             {x : ty EE}
    : form (ℙ x)
    := (∀h ¬(π₂ (tm_var _) ∈ π₁ (tm_var _))).

  Proposition empty_form_false
              {Γ x : ty EE}
              (s : tm Γ (ℙ x))
              (a : tm Γ x)
              {Δ : form Γ}
              (p : Δ ⊢ isEmpty_form [ s ])
              (q : Δ ⊢ a ∈ s)
    : Δ ⊢ ⊥.
  Proof.
    refine (weaken_cut _ _).
    {
      refine (hyperdoctrine_cut p _).
      unfold isEmpty_form.
      simplify.
      refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) a) _).
      simplify.
      apply hyperdoctrine_hyp.
    }
    refine (neg_elim _ _).
    - use weaken_left.
      exact q.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition empty_map
             (x y : ty EE)
    : x --> ℙ y
    := {{ ⊥ }}.

  Proposition isEmpty_empty_map
              (x y : ty EE)
    : ⊤ ⊢ isEmpty_form [ empty_map x y ].
  Proof.
    unfold isEmpty_form, empty_map.
    simplify.
    use forall_intro.
    simplify.
    rewrite (topos_tripos_compr_subst E).
    rewrite (topos_tripos_compr_in E).
    simplify.
    use impl_intro.
    use weaken_right.
    apply hyperdoctrine_hyp.
  Qed.

  Definition isSubSingleton_form
             {x : ty EE}
    : form (ℙ x)
    := (∀h ∀h
        let a₁ := π₂ (π₁ (tm_var _)) in
        let a₂ := π₂ (tm_var _) in
        let s := π₁ (π₁ (tm_var _)) in
        (a₁ ∈ s ⇒ a₂ ∈ s ⇒ a₁ ≡ a₂)).

  Proposition isSubSingleton_form_eq
              {x Γ : ty EE}
              {s : tm Γ (ℙ x)}
              {Δ : form Γ}
              (p : Δ ⊢ isSubSingleton_form [ s ])
              {t₁ t₂ : tm Γ x}
              (q₁ : Δ ⊢ t₁ ∈ s)
              (q₂ : Δ ⊢ t₂ ∈ s)
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    refine (weaken_cut _ _).
    - refine (hyperdoctrine_cut p _).
      unfold isSubSingleton_form.
      simplify.
      refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) t₁) _).
      simplify.
      refine (hyperdoctrine_cut (forall_elim (hyperdoctrine_hyp _) t₂) _).
      simplify.
      apply hyperdoctrine_hyp.
    - refine (impl_elim _ _).
      {
        refine (hyperdoctrine_cut _ q₂).
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      refine (impl_elim _ _).
      {
        refine (hyperdoctrine_cut _ q₁).
        use weaken_left.
        apply hyperdoctrine_hyp.
      }
      use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition inhabited_form
             {x : ty EE}
    : form (ℙ x)
    := (∃h
        let s := π₁ (tm_var _) in
        let a := π₂ (tm_var _) in
        (a ∈ s)).

  Proposition inhabited_form_el
              {Γ x : ty EE}
              (s : tm Γ (ℙ x))
              {Δ : form Γ}
              (p : Δ ⊢ inhabited_form [ s ])
    : (Δ ⊢ ∃h (π₂ (tm_var _) ∈ s [ π₁ (tm_var _) ]tm)).
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold inhabited_form.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Definition isSingleton_form
             {x : ty EE}
    : form (ℙ x)
    := isSubSingleton_form ∧ inhabited_form.

  Definition singleton_map
             (x : ty EE)
    : x --> ℙ x
    := {{ π₁ (tm_var _) ≡ π₂ (tm_var _) }}.

  Proposition isSingleton_singleton_map
              (x : ty EE)
    : ⊤ ⊢ isSingleton_form [ singleton_map x ].
  Proof.
    unfold isSingleton_form, singleton_map.
    simplify.
    use conj_intro.
    - unfold isSubSingleton_form ; simplify.
      do 2 use forall_intro.
      rewrite (topos_tripos_compr_subst E).
      rewrite !(topos_tripos_compr_in E).
      simplify.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      refine (hyperdoctrine_eq_trans _ _).
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use hyperdoctrine_eq_sym.
        apply hyperdoctrine_hyp.
    - unfold inhabited_form ; simplify.
      use exists_intro.
      {
        exact (tm_var _).
      }
      simplify.
      rewrite (topos_tripos_compr_in E).
      simplify.
      apply hyperdoctrine_refl.
  Qed.

  Definition coprod_form_left
             (x y : ty EE)
    : form (ℙ x ×h ℙ y)
    := let s₁ := π₁ (tm_var _) in
       let s₂ := π₂ (tm_var _) in
       isEmpty_form [ s₁ ] ∧ isSingleton_form [ s₂ ].

  Definition coprod_form_right
             (x y : ty EE)
    : form (ℙ x ×h ℙ y)
    := let s₁ := π₁ (tm_var _) in
       let s₂ := π₂ (tm_var _) in
       isEmpty_form [ s₂ ] ∧ isSingleton_form [ s₁ ].

  Definition coprod_form
             (x y : ty EE)
    : form (ℙ x ×h ℙ y)
    := coprod_form_left x y ∨ coprod_form_right x y.

  Definition topos_coprod_obj
             (x y : ty EE)
    : ty EE
    := formula_comprehension (topos_logic_comprehension_hd E) (coprod_form x y).

  Definition topos_coprod_obj_incl
             (x y : ty EE)
    : topos_coprod_obj x y --> (ℙ x ×h ℙ y)
    := formula_inclusion (topos_logic_comprehension_hd E) (coprod_form x y).

  Notation "'ι'" := (topos_coprod_obj_incl _ _).

  Proposition topos_coprod_obj_prf
              {Γ x y : ty EE}
              (Δ : form Γ)
              (t : tm Γ (topos_coprod_obj x y))
    : Δ ⊢ (coprod_form x y) [ ι [ t ]tm ].
  Proof.
    exact (formula_comprehension_prf_tm (topos_logic_comprehension_hd E) Δ t).
  Qed.

  Proposition topos_coprod_obj_subsingleton_left
              {Γ x y : ty EE}
              (Δ : form Γ)
              (s : tm Γ (topos_coprod_obj x y))
    : Δ ⊢ isSubSingleton_form [ π₁ (ι [ s ]tm) ].
  Proof.
    refine (disj_elim _ _ _).
    - refine (hyperdoctrine_cut (topos_coprod_obj_prf Δ s) _).
      unfold coprod_form.
      simplify.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      unfold coprod_form_left, isSubSingleton_form.
      simplify.
      do 2 use forall_intro.
      simplify.
      use impl_intro.
      use false_elim.
      refine (empty_form_false _ _ _ _).
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - use weaken_right.
      unfold coprod_form_right, isSingleton_form.
      simplify.
      use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition topos_coprod_obj_subsingleton_right
              {Γ x y : ty EE}
              (Δ : form Γ)
              (s : tm Γ (topos_coprod_obj x y))
    : Δ ⊢ isSubSingleton_form [ π₂ (ι [ s ]tm) ].
  Proof.
    refine (disj_elim _ _ _).
    - refine (hyperdoctrine_cut (topos_coprod_obj_prf Δ s) _).
      unfold coprod_form.
      simplify.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      unfold coprod_form_left, isSingleton_form.
      simplify.
      use weaken_right.
      use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      unfold coprod_form_right, isSubSingleton_form.
      simplify.
      do 2 use forall_intro.
      simplify.
      use impl_intro.
      use false_elim.
      refine (empty_form_false _ _ _ _).
      + do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition topos_coprod_obj_both
              {Γ x y : ty EE}
              (Δ : form Γ)
              {s : tm Γ (topos_coprod_obj x y)}
              {t₁ : tm Γ x}
              {t₂ : tm Γ y}
              (p : Δ ⊢ t₁ ∈ π₁ (ι [ s ]tm))
              (q : Δ ⊢ t₂ ∈ π₂ (ι [ s ]tm))
    : Δ ⊢ ⊥.
  Proof.
    refine (disj_elim _ _ _).
    - refine (hyperdoctrine_cut (topos_coprod_obj_prf Δ s) _).
      unfold coprod_form.
      simplify.
      apply hyperdoctrine_hyp.
    - unfold coprod_form_left.
      simplify.
      refine (empty_form_false _ _ _ _).
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_left.
        exact p.
    - unfold coprod_form_right.
      simplify.
      refine (empty_form_false _ _ _ _).
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_left.
        exact q.
  Qed.

  Definition topos_coprod_inl
             (x y : ty EE)
    : x --> topos_coprod_obj x y.
  Proof.
    use make_comprehension_term.
    - exact ⟨ singleton_map x , empty_map x y ⟩.
    - abstract
        (unfold coprod_form, coprod_form_right ;
         simplify ;
         use disj_intro_right ;
         use conj_intro ; [ apply isEmpty_empty_map | ] ;
         apply isSingleton_singleton_map).
  Defined.

  Proposition topos_coprod_inl_incl
              (x y : ty EE)
    : ι [ topos_coprod_inl x y ]tm = ⟨ singleton_map x , empty_map x y ⟩.
  Proof.
    apply make_comprehension_term_eq.
  Qed.

  Definition topos_coprod_inr
             (x y : ty EE)
    : y --> topos_coprod_obj x y.
  Proof.
    use make_comprehension_term.
    - exact ⟨ empty_map y x , singleton_map y ⟩.
    - abstract
        (unfold coprod_form, coprod_form_left ;
         simplify ;
         use disj_intro_left ;
         use conj_intro ; [ apply isEmpty_empty_map | ] ;
         apply isSingleton_singleton_map).
  Defined.

  Proposition topos_coprod_inr_incl
              (x y : ty EE)
    : ι [ topos_coprod_inr x y ]tm = ⟨ empty_map y x , singleton_map y ⟩.
  Proof.
    apply make_comprehension_term_eq.
  Qed.


  Definition topos_copair_left
             {x y z : ty EE}
             (f : x --> z)
             (g : y --> z)
    : form (topos_coprod_obj x y ×h z)
    := (∀h (let a := π₂ (tm_var _) in
            let b := π₁ (ι [ (π₁ (π₁ (tm_var _))) ]tm) in
            let c := π₂ (π₁ (tm_var _)) in
            a ∈ b ⇒ f [ a ]tm ≡ c)).

  Proposition topos_copair_left_eq
              {Γ x y z : ty EE}
              {f : x --> z}
              {g : y --> z}
              {Δ : form Γ}
              {t₁ : tm Γ (topos_coprod_obj x y)}
              {t₂ : tm Γ z}
              (p : Δ ⊢ (topos_copair_left f g) [ ⟨ t₁ , t₂ ⟩ ])
              (s : tm Γ x)
              (q : Δ ⊢ s ∈ π₁ (ι [ t₁ ]tm))
    : Δ ⊢ f [ s ]tm ≡ t₂.
  Proof.
    refine (weaken_cut _ _).
    {
      refine (hyperdoctrine_cut p _).
      unfold topos_copair_left.
      simplify.
      exact (forall_elim (hyperdoctrine_hyp _) s).
    }
    simplify.
    refine (impl_elim _ _).
    - use weaken_left.
      exact q.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition topos_copair_right
             {x y z : ty EE}
             (f : x --> z)
             (g : y --> z)
    : form (topos_coprod_obj x y ×h z)
    := (∀h (let a := π₂ (tm_var _) in
            let b := π₂ (ι [ (π₁ (π₁ (tm_var _))) ]tm) in
            let c := π₂ (π₁ (tm_var _)) in
            a ∈ b ⇒ g [ a ]tm ≡ c)).

  Proposition topos_copair_right_eq
              {Γ x y z : ty EE}
              {f : x --> z}
              {g : y --> z}
              {Δ : form Γ}
              {t₁ : tm Γ (topos_coprod_obj x y)}
              {t₂ : tm Γ z}
              (p : Δ ⊢ (topos_copair_right f g) [ ⟨ t₁ , t₂ ⟩ ])
              (s : tm Γ y)
              (q : Δ ⊢ s ∈ π₂ (ι [ t₁ ]tm))
    : Δ ⊢ g [ s ]tm ≡ t₂.
  Proof.
    refine (weaken_cut _ _).
    {
      refine (hyperdoctrine_cut p _).
      unfold topos_copair_right.
      simplify.
      exact (forall_elim (hyperdoctrine_hyp _) s).
    }
    simplify.
    refine (impl_elim _ _).
    - use weaken_left.
      exact q.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition topos_copair_form
             {x y z : ty EE}
             (f : x --> z)
             (g : y --> z)
    : form (topos_coprod_obj x y ×h z)
    := topos_copair_left f g ∧ topos_copair_right f g.

  Proposition functional_relation_topos_copair
              {x y z : ty EE}
              (f : x --> z)
              (g : y --> z)
    : ⊤ ⊢ functional_relation (topos_copair_form f g).
  Proof.
    use conj_intro.
    - use forall_intro.
      pose (Γ := 𝟙 ×h topos_coprod_obj x y).
      pose (w := π₂ (tm_var Γ)).
      refine (hyperdoctrine_cut
                (topos_coprod_obj_prf _ w)
                _).
      refine (disj_elim _ _ _).
      + unfold coprod_form.
        simplify.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        unfold coprod_form_left, isSingleton_form.
        simplify.
        refine (exists_elim _ _).
        {
          apply inhabited_form_el.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        simplify.
        use exists_intro.
        {
          exact (g [ π₂ (tm_var _) ]tm).
        }
        unfold topos_copair_form.
        simplify.
        use conj_intro.
        * unfold topos_copair_left.
          rewrite forall_subst.
          use forall_intro.
          simplify.
          use impl_intro.
          use false_elim.
          refine (empty_form_false _ _ _ _).
          ** do 3 use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             unfold w.
             simplify.
             apply hyperdoctrine_hyp.
        * unfold topos_copair_right.
          rewrite forall_subst.
          use forall_intro.
          simplify.
          use impl_intro.
          use hyperdoctrine_subst_eq.
          refine (isSubSingleton_form_eq _ _ _).
          ** do 2 use weaken_left.
             use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             unfold w.
             simplify.
             apply hyperdoctrine_hyp.
          ** use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
      + use weaken_right.
        unfold coprod_form_right, isSingleton_form.
        simplify.
        refine (exists_elim _ _).
        {
          apply inhabited_form_el.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        simplify.
        use exists_intro.
        {
          exact (f [ π₂ (tm_var _) ]tm).
        }
        unfold topos_copair_form.
        simplify.
        use conj_intro.
        * unfold topos_copair_left.
          rewrite forall_subst.
          use forall_intro.
          simplify.
          use impl_intro.
          use hyperdoctrine_subst_eq.
          refine (isSubSingleton_form_eq _ _ _).
          ** do 2 use weaken_left.
             use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             unfold w.
             simplify.
             apply hyperdoctrine_hyp.
          ** use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
        * unfold topos_copair_right.
          rewrite forall_subst.
          use forall_intro.
          simplify.
          use impl_intro.
          use false_elim.
          refine (empty_form_false _ _ _ _).
          ** do 3 use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             unfold w.
             simplify.
             apply hyperdoctrine_hyp.
    - do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      unfold topos_copair_form.
      simplify.
      refine (disj_elim _ _ _).
      + refine (hyperdoctrine_cut (topos_coprod_obj_prf _ (π₂ (π₁ (π₁ (tm_var _))))) _).
        unfold coprod_form.
        simplify.
        apply hyperdoctrine_hyp.
      + refine (exists_elim _ _).
        {
          apply inhabited_form_el.
          use weaken_right.
          unfold coprod_form_left, isSingleton_form.
          simplify.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        simplify.
        pose ((((𝟙 ×h topos_coprod_obj x y) ×h z) ×h z) ×h y) as Γ.
        pose (a := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (b₁ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (b₂ := π₂ (π₁ (tm_var Γ))).
        pose (c := π₂ (tm_var Γ)).
        unfold Γ in * ; clear Γ.
        fold a b₁ b₂ c.
        refine (hyperdoctrine_eq_trans _ _).
        * use hyperdoctrine_eq_sym.
          refine (topos_copair_right_eq _ _ _).
          ** do 3 use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * refine (topos_copair_right_eq _ _ _).
          ** do 2 use weaken_left.
             do 2 use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
      + refine (exists_elim _ _).
        {
          apply inhabited_form_el.
          unfold coprod_form_right, isSingleton_form.
          simplify.
          do 3 use weaken_right.
          apply hyperdoctrine_hyp.
        }
        simplify.
        pose ((((𝟙 ×h topos_coprod_obj x y) ×h z) ×h z) ×h x) as Γ.
        pose (a := π₂ (π₁ (π₁ (π₁ (tm_var Γ))))).
        pose (b₁ := π₂ (π₁ (π₁ (tm_var Γ)))).
        pose (b₂ := π₂ (π₁ (tm_var Γ))).
        pose (c := π₂ (tm_var Γ)).
        unfold Γ in * ; clear Γ.
        fold a b₁ b₂ c.
        refine (hyperdoctrine_eq_trans _ _).
        * use hyperdoctrine_eq_sym.
          refine (topos_copair_left_eq _ _ _).
          ** do 4 use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * refine (topos_copair_left_eq _ _ _).
          ** do 2 use weaken_left.
             use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.

  Definition topos_copair
             {x y z : ty EE}
             (f : x --> z)
             (g : y --> z)
    : topos_coprod_obj x y --> z
    := functional_relation_to_mor
         (topos_logic_functional_completeness E)
         _
         (functional_relation_topos_copair f g).

  Proposition topos_copair_inl
              {x y z : ty EE}
              (f : x --> z)
              (g : y --> z)
    : topos_coprod_inl x y · topos_copair f g = f.
  Proof.
    assert ((topos_coprod_inl x y · topos_copair f g)
            =
            (topos_copair f g) [ topos_coprod_inl x y ]tm)
      as ->.
    {
      apply idpath.
    }
    use topos_logic_extensionality.
    use forall_intro.
    simple refine (hyperdoctrine_cut
                     (functional_relation_to_mor_agrees
                        (topos_logic_functional_completeness E)
                        _
                        (functional_relation_topos_copair f g)
                        _
                        _)
                     _).
    {
      exact ((topos_coprod_inl x y) [ π₂ (tm_var _) ]tm).
    }
    unfold topos_copair_form.
    simplify.
    use weaken_left.
    use hyperdoctrine_eq_sym.
    refine (topos_copair_left_eq _ _ _).
    {
      apply hyperdoctrine_hyp.
    }
    refine (hyperdoctrine_cut (truth_intro _) _).
    rewrite <- tm_subst_comp.
    rewrite topos_coprod_inl_incl.
    unfold singleton_map.
    simplify.
    rewrite (topos_tripos_compr_subst E).
    rewrite (topos_tripos_compr_in E).
    simplify.
    apply hyperdoctrine_refl.
  Qed.

  Proposition topos_copair_inr
              {x y z : ty EE}
              (f : x --> z)
              (g : y --> z)
    : topos_coprod_inr x y · topos_copair f g = g.
  Proof.
    assert ((topos_coprod_inr x y · topos_copair f g)
            =
            (topos_copair f g) [ topos_coprod_inr x y ]tm)
      as ->.
    {
      apply idpath.
    }
    use topos_logic_extensionality.
    use forall_intro.
    simple refine (hyperdoctrine_cut
                     (functional_relation_to_mor_agrees
                        (topos_logic_functional_completeness E)
                        _
                        (functional_relation_topos_copair f g)
                        _
                        _)
                     _).
    {
      exact ((topos_coprod_inr x y) [ π₂ (tm_var _) ]tm).
    }
    unfold topos_copair_form.
    simplify.
    use weaken_right.
    use hyperdoctrine_eq_sym.
    refine (topos_copair_right_eq _ _ _).
    {
      apply hyperdoctrine_hyp.
    }
    refine (hyperdoctrine_cut (truth_intro _) _).
    rewrite <- tm_subst_comp.
    rewrite topos_coprod_inr_incl.
    unfold singleton_map.
    simplify.
    rewrite (topos_tripos_compr_subst E).
    rewrite (topos_tripos_compr_in E).
    simplify.
    apply hyperdoctrine_refl.
  Qed.

  Proposition topos_copair_unique
              {x y z : ty EE}
              (f : x --> z)
              (g : y --> z)
              (h : topos_coprod_obj x y --> z)
              (p₁ : topos_coprod_inl x y · h = f)
              (p₂ : topos_coprod_inr x y · h = g)
    : h = topos_copair f g.
  Proof.
    assert (q₁ : h [ topos_coprod_inl x y ]tm = f).
    {
      exact p₁.
    }
    assert (q₂ : h [ topos_coprod_inr x y ]tm = g).
    {
      exact p₂.
    }
    clear p₁ p₂.
    use topos_logic_extensionality.
    use forall_intro.
    simplify.
    use (functional_relation_unique_im
           _
           (functional_relation_topos_copair f g)
           _
           (π₂ (tm_var _))).
    - unfold topos_copair_form.
      simplify.
      use conj_intro.
      + unfold topos_copair_left.
        simplify.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        rewrite <- q₁.
        simplify.
        use hyperdoctrine_subst_eq.
        use eq_comprehension_term_topos.
        assert (formula_inclusion
                  (topos_logic_comprehension_hd E)
                  (coprod_form x y)
                =
                ι)
          as ->.
        {
          apply idpath.
        }
        rewrite <- tm_subst_comp.
        refine (hyperdoctrine_eq_trans _ _).
        {
          use hyperdoctrine_refl_eq.
          apply maponpaths_2.
          apply (topos_coprod_inl_incl x y).
        }
        use hyperdoctrine_eq_prod_eq.
        * unfold singleton_map.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          use topos_tripos_compr_eq.
          use forall_intro.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          rewrite topos_tripos_compr_in.
          simplify.
          use conj_intro.
          ** use impl_intro.
             refine (hyperdoctrine_cut _ _).
             {
               use (hyperdoctrine_eq_elim
                      (π₂ (tm_var _) ∈ (π₁ (ι [ π₂ (π₁ (π₁ (π₁ (tm_var _)))) ]tm)))
                      (hyperdoctrine_eq_sym (weaken_right (hyperdoctrine_hyp _) _))).
               simplify.
               use weaken_left.
               apply hyperdoctrine_hyp.
             }
             simplify.
             apply hyperdoctrine_hyp.
          ** use impl_intro.
             refine (isSubSingleton_form_eq
                       _
                       (weaken_right (hyperdoctrine_hyp _) _)
                       (weaken_left (hyperdoctrine_hyp _) _)).
             apply topos_coprod_obj_subsingleton_left.
        * unfold empty_map.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          simplify.
          use topos_tripos_compr_eq.
          use forall_intro.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          rewrite topos_tripos_compr_in.
          simplify.
          use conj_intro.
          ** use impl_intro.
             apply false_elim.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use impl_intro.
             refine (topos_coprod_obj_both _ _ _).
             *** use weaken_left.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
      + unfold topos_copair_right.
        simplify.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        rewrite <- q₂.
        simplify.
        use hyperdoctrine_subst_eq.
        use eq_comprehension_term_topos.
        assert (formula_inclusion
                  (topos_logic_comprehension_hd E)
                  (coprod_form x y)
                =
                ι)
          as ->.
        {
          apply idpath.
        }
        rewrite <- tm_subst_comp.
        refine (hyperdoctrine_eq_trans _ _).
        {
          use hyperdoctrine_refl_eq.
          apply maponpaths_2.
          apply (topos_coprod_inr_incl x y).
        }
        use hyperdoctrine_eq_prod_eq.
        * unfold empty_map.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          simplify.
          use topos_tripos_compr_eq.
          use forall_intro.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          rewrite topos_tripos_compr_in.
          simplify.
          use conj_intro.
          ** use impl_intro.
             apply false_elim.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use impl_intro.
             refine (topos_coprod_obj_both _ _ _).
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 apply hyperdoctrine_hyp.
        * unfold singleton_map.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          use topos_tripos_compr_eq.
          use forall_intro.
          simplify.
          rewrite (topos_tripos_compr_subst E).
          rewrite topos_tripos_compr_in.
          simplify.
          use conj_intro.
          ** use impl_intro.
             refine (hyperdoctrine_cut _ _).
             {
               use (hyperdoctrine_eq_elim
                      (π₂ (tm_var _) ∈ (π₂ (ι [ π₂ (π₁ (π₁ (π₁ (tm_var _)))) ]tm)))
                      (hyperdoctrine_eq_sym (weaken_right (hyperdoctrine_hyp _) _))).
               simplify.
               use weaken_left.
               apply hyperdoctrine_hyp.
             }
             simplify.
             apply hyperdoctrine_hyp.
          ** use impl_intro.
             refine (isSubSingleton_form_eq
                       _
                       (weaken_right (hyperdoctrine_hyp _) _)
                       (weaken_left (hyperdoctrine_hyp _) _)).
             apply topos_coprod_obj_subsingleton_right.
    - exact (functional_relation_to_mor_agrees
               (topos_logic_functional_completeness E)
               _
               (functional_relation_topos_copair f g)
               _
               _).
  Qed.

  Definition topos_bincoproducts
    : BinCoproducts E.
  Proof.
    intros x y.
    use make_BinCoproduct.
    - exact (topos_coprod_obj x y).
    - exact (topos_coprod_inl x y).
    - exact (topos_coprod_inr x y).
    - intros z f g.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (topos_copair f g).
        * apply topos_copair_inl.
        * apply topos_copair_inr.
      + abstract
          (intros hpq ;
           induction hpq as [ h [ p₁ p₂ ]] ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           exact (topos_copair_unique f g h p₁ p₂)).
  Defined.

  Proposition isInjective_topos_coprod_inl
              (x y : ty EE)
    : ⊤ ⊢ isInjective_hyperdoctrine (topos_coprod_inl x y).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    pose (Γ := (𝟙 ×h x) ×h x).
    pose (a₁ := π₂ (π₁ (tm_var Γ))).
    pose (a₂ := π₂ (tm_var Γ)).
    unfold Γ in * ; clear Γ.
    fold a₁ a₂.
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_subst_eq (hyperdoctrine_hyp _) _).
      exact ι.
    }
    rewrite <- !tm_subst_comp.
    rewrite !topos_coprod_inl_incl.
    refine (hyperdoctrine_cut _ _).
    {
      exact (hyperdoctrine_eq_pr1 (hyperdoctrine_hyp _)).
    }
    simplify.
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_eq_elim
                (a₁ [ π₁ (tm_var _) ]tm ∈ π₂ (tm_var _))
                (hyperdoctrine_hyp _)
                _).
      refine (hyperdoctrine_cut (truth_intro _) _).
      unfold singleton_map.
      simplify.
      rewrite (topos_tripos_compr_subst E).
      rewrite (topos_tripos_compr_in E).
      simplify.
      apply hyperdoctrine_refl.
    }
    unfold singleton_map.
    simplify.
    rewrite (topos_tripos_compr_subst E).
    rewrite (topos_tripos_compr_in E).
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition isInjective_topos_coprod_inr
              (x y : ty EE)
    : ⊤ ⊢ isInjective_hyperdoctrine (topos_coprod_inr x y).
  Proof.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    pose (Γ := (𝟙 ×h y) ×h y).
    pose (a₁ := π₂ (π₁ (tm_var Γ))).
    pose (a₂ := π₂ (tm_var Γ)).
    unfold Γ in * ; clear Γ.
    fold a₁ a₂.
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_subst_eq (hyperdoctrine_hyp _) _).
      exact ι.
    }
    rewrite <- !tm_subst_comp.
    rewrite !topos_coprod_inr_incl.
    refine (hyperdoctrine_cut _ _).
    {
      exact (hyperdoctrine_eq_pr2 (hyperdoctrine_hyp _)).
    }
    simplify.
    refine (hyperdoctrine_cut _ _).
    {
      refine (hyperdoctrine_eq_elim
                (a₁ [ π₁ (tm_var _) ]tm ∈ π₂ (tm_var _))
                (hyperdoctrine_hyp _)
                _).
      refine (hyperdoctrine_cut (truth_intro _) _).
      unfold singleton_map.
      simplify.
      rewrite (topos_tripos_compr_subst E).
      rewrite (topos_tripos_compr_in E).
      simplify.
      apply hyperdoctrine_refl.
    }
    unfold singleton_map.
    simplify.
    rewrite (topos_tripos_compr_subst E).
    rewrite (topos_tripos_compr_in E).
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition topos_coprod_disjoint
              {w x y : ty EE}
              {f : w --> x}
              {g : w --> y}
              (p : f · topos_coprod_inl x y = g · topos_coprod_inr x y)
    : w --> topos_initial_obj.
  Proof.
    assert (⊤ ⊢ (topos_coprod_inl x y) [ f ]tm ≡ (topos_coprod_inr x y) [ g ]tm) as q.
    {
      use hyperdoctrine_refl_eq.
      exact p.
    }
    use (functional_relation_to_mor
           (topos_logic_functional_completeness E)).
    {
      exact ⊥.
    }
    use conj_intro.
    - use forall_intro.
      use false_elim.
      simplify.
      refine (hyperdoctrine_cut
                _
                (hyperdoctrine_cut
                   (hyperdoctrine_proof_subst (π₂ (tm_var _)) q)
                   _)).
      {
        simplify.
        apply truth_intro.
      }
      simplify.
      refine (hyperdoctrine_cut _ _).
      {
        refine (hyperdoctrine_subst_eq (hyperdoctrine_hyp _) _).
        exact ι.
      }
      rewrite <- !tm_subst_comp.
      rewrite topos_coprod_inl_incl, topos_coprod_inr_incl.
      refine (hyperdoctrine_cut _ _).
      {
        exact (hyperdoctrine_eq_pr1 (hyperdoctrine_hyp _)).
      }
      unfold singleton_map, empty_map.
      simplify.
      rewrite !(topos_tripos_compr_subst E).
      simplify.
      refine (hyperdoctrine_cut _ _).
      {
        refine (hyperdoctrine_eq_elim
                  (f [ π₂ (π₁ (tm_var _)) ]tm ∈ π₂ (tm_var _))
                  (hyperdoctrine_hyp _)
                  _).
        simplify.
        refine (hyperdoctrine_cut (truth_intro _) _).
        rewrite (topos_tripos_compr_in E).
        simplify.
        apply hyperdoctrine_refl.
      }
      simplify.
      rewrite (topos_tripos_compr_in E).
      simplify.
      apply hyperdoctrine_hyp.
    - use forall_intro.
      use false_elim.
      simplify.
      refine (hyperdoctrine_cut
                _
                (hyperdoctrine_cut
                   (hyperdoctrine_proof_subst (π₂ (tm_var _)) q)
                   _)).
      {
        simplify.
        apply truth_intro.
      }
      simplify.
      refine (hyperdoctrine_cut _ _).
      {
        refine (hyperdoctrine_subst_eq (hyperdoctrine_hyp _) _).
        exact ι.
      }
      rewrite <- !tm_subst_comp.
      rewrite topos_coprod_inl_incl, topos_coprod_inr_incl.
      refine (hyperdoctrine_cut _ _).
      {
        exact (hyperdoctrine_eq_pr1 (hyperdoctrine_hyp _)).
      }
      unfold singleton_map, empty_map.
      simplify.
      rewrite !(topos_tripos_compr_subst E).
      simplify.
      refine (hyperdoctrine_cut _ _).
      {
        refine (hyperdoctrine_eq_elim
                  (f [ π₂ (π₁ (tm_var _)) ]tm ∈ π₂ (tm_var _))
                  (hyperdoctrine_hyp _)
                  _).
        simplify.
        refine (hyperdoctrine_cut (truth_intro _) _).
        rewrite (topos_tripos_compr_in E).
        simplify.
        apply hyperdoctrine_refl.
      }
      simplify.
      rewrite (topos_tripos_compr_in E).
      simplify.
      apply hyperdoctrine_hyp.
  Qed.


End ToposInitial.
