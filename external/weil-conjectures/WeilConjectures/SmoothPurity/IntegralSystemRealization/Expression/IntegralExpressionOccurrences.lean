/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain

/-! # Independent leaf occurrences in an integral-system expression

Source: blueprint, adic transport in theorem-smooth-purity-all-admissible-coefficients, Step 2;
independent occurrence-slot convention of lem-pur-integral-realization-shift-coherence
(blueprint: def-pur-integral-expression-occurrences).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

/-- Each leaf contributes its own singleton, and a tensor contributes a disjoint
sum. In particular two occurrences of the same variable give different elements.
Source: blueprint, independent occurrence slots
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.Occurrences {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → Expression B I X W → Type u
  | _, .var _ => PUnit.{u + 1}
  | _, .pull _ e => e.Occurrences
  | _, .push _ _ e => e.Occurrences
  | _, .shriek _ _ _ e => e.Occurrences
  | _, .compactSupport _ _ e => e.Occurrences
  | _, .tensor e t => e.Occurrences ⊕ t.Occurrences

/-- Original input label at a leaf occurrence. This retains labels independently
of equality of the supplied objects.
Source: blueprint, each leaf occurrence is an independent slot
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.occurrenceLabel {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → (e : Expression B I X W) → e.Occurrences → I
  | _, .var i => fun _ ↦ i
  | _, .pull _ e => e.occurrenceLabel
  | _, .push _ _ e => e.occurrenceLabel
  | _, .shriek _ _ _ e => e.occurrenceLabel
  | _, .compactSupport _ _ e => e.occurrenceLabel
  | _, .tensor e t => Sum.elim e.occurrenceLabel t.occurrenceLabel

open Classical in
open Classical in
/-- Shift one factor of a product input category; all other factors retain their maps.
Source: blueprint Step 2 (blueprint: def-pur-integral-expression-occurrences). -/
def inputShift {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)]
    [∀ i, HasShift (C i) ℤ] (i : I) (r : ℤ) : (∀ j, C j) ⥤ ∀ j, C j :=
  Functor.pi' (fun j ↦ Pi.eval C j ⋙ if i = j then shiftFunctor (C j) r else 𝟭 (C j))

open Classical in
/-- The input endofunctor has exactly the dependent-update object family.
Source: blueprint Step 2 (blueprint: def-pur-integral-expression-occurrences).
Proof: apply dependent function extensionality at j and split on i = j. After
substitution the selected component is (K i)[r]; every other component is K j. -/
theorem inputShift_obj {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)]
    [∀ i, HasShift (C i) ℤ] (K : ∀ j, C j) (i : I) (r : ℤ) :
    (inputShift C i r).obj K = Function.update K i ((K i)⟦r⟧) := by
  funext j
  by_cases h : i = j
  · subst j
    simp [inputShift]
  · simp [inputShift, h, Function.update_of_ne (Ne.symm h)]

open Classical in
open Classical in
/-- A single designated input, with every other operand held at its actual value.
Unary vertices retain their original maps and witnesses, and tensor vertices retain
which of the two inputs contains the designated occurrence.
Source: blueprint, independent slotwise comparisons
(blueprint: def-pur-integral-expression-occurrences). -/
inductive Expression.SlotContext {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] (d : Interpretation C) (A : Over B) :
    Over B → Type (max (u + 1) v) where
  | input : SlotContext d A A
  | pull {U V : Over B} (f : U ⟶ V) (e : SlotContext d A V) : SlotContext d A U
  | push {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left)
      (e : SlotContext d A U) : SlotContext d A V
  | shriek {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hq : QuasiCompact j.left) (e : SlotContext d A U) : SlotContext d A V
  | compactSupport {U V : Over B} (f : U ⟶ V) (c : Compactification f.left)
      (e : SlotContext d A U) : SlotContext d A V
  | tensorLeft {W : Over B} (e : SlotContext d A W) (N : C W.left) : SlotContext d A W
  | tensorRight {W : Over B} (M : C W.left) (e : SlotContext d A W) : SlotContext d A W

/-- A context is the actual unary composite, using the appropriate curried tensor
functor at a tensor vertex. No functor or map is chosen by an existence theorem.
Source: blueprint, expression contexts and slotwise comparisons
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.SlotContext.evaluate {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] {d : Interpretation C} {A : Over B} :
    {W : Over B} → SlotContext d A W → (C A.left ⥤ C W.left)
  | _, .input => 𝟭 _
  | _, .pull f e => e.evaluate ⋙ d.pull f.left
  | _, .push f _ e => e.evaluate ⋙ d.push f.left
  | _, .shriek j hj _ e =>
    letI := hj
    e.evaluate ⋙ d.shriek j.left
  | _, .compactSupport f c e => e.evaluate ⋙ d.compactSupport f.left c
  | W, .tensorLeft e N => e.evaluate ⋙ (Functor.curry.obj (d.tensor W.left)).flip.obj N
  | W, .tensorRight M e => e.evaluate ⋙ (Functor.curry.obj (d.tensor W.left)).obj M

open Classical in
/-- Independently labelled finite expressions. This is only a presentation of
independent occurrences: independentInputs provides it for every existing expression.
Source: blueprint, independent input slots
(blueprint: def-pur-integral-expression-occurrences). -/
abbrev IndependentExpression (B : Scheme.{u}) (I : Type u) (X : I → Over B) (W : Over B) :=
  {e : Expression B I X W // Function.Bijective e.occurrenceLabel}

open Classical in
/-- Search the expression for a designated input label. At a tensor the actual
other subtree is held fixed. For independent labels there is exactly one hit.
Source: blueprint, individual occurrence slots
(blueprint: def-pur-integral-expression-occurrences). -/
def Expression.variableContext {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] (d : Interpretation C)
    (K : ∀ i, C (X i).left) (i : I) :
    {W : Over B} → Expression B I X W → Option (Expression.SlotContext d (X i) W)
  | _, .var j => if h : i = j then h ▸ some .input else none
  | _, .pull f e => (e.variableContext d K i).map (.pull f)
  | _, .push f hp e => (e.variableContext d K i).map (.push f hp)
  | _, .shriek j hj hq e => (e.variableContext d K i).map (.shriek j hj hq)
  | _, .compactSupport f c e => (e.variableContext d K i).map (.compactSupport f c)
  | _, .tensor e t => match e.variableContext d K i with
    | some c => some (.tensorLeft c ((t.evaluate d).obj K))
    | none => (t.variableContext d K i).map
      (fun c ↦ .tensorRight ((e.evaluate d).obj K) c)

private theorem variableContext_isSome_iff {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) (K : ∀ i, C (X i).left) (i : I)
    {W : Over B} (e : Expression B I X W) :
    (e.variableContext d K i).isSome ↔ ∃ j, e.occurrenceLabel j = i := by
  classical
  induction e with
  | var j =>
    by_cases h : i = j
    · subst j
      constructor
      · intro _; exact ⟨PUnit.unit, rfl⟩
      · intro _; simp [Expression.variableContext]
    · simp [Expression.variableContext, Expression.occurrenceLabel, h, Ne.symm h]
  | pull f e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | push f hp e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | shriek j hj hq e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | compactSupport f c e ih =>
    change (Option.map _ (e.variableContext d K i)).isSome ↔
      ∃ j : e.Occurrences, e.occurrenceLabel j = i
    rw [Option.isSome_map]
    exact ih
  | tensor e t ih jt =>
    cases he : e.variableContext d K i with
    | none =>
      have ha : ¬ ∃ j, e.occurrenceLabel j = i := by
        intro hex
        have bad := ih.mpr hex
        simp [he] at bad
      simp only [Expression.variableContext, he]
      rw [Option.isSome_map]
      constructor
      · intro ht
        obtain ⟨j, hj⟩ := jt.mp ht
        exact ⟨Sum.inr j, hj⟩
      · rintro ⟨j, hj⟩
        cases j with
        | inl j => exact (ha ⟨j, hj⟩).elim
        | inr j => exact jt.mpr ⟨j, hj⟩
    | some c =>
      have hex := ih.mp (by simp [he])
      constructor
      · intro _
        obtain ⟨j, hj⟩ := hex
        exact ⟨Sum.inl j, hj⟩
      · intro _
        simp [Expression.variableContext, he]

open Classical in
private theorem evaluate_update_absent {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) (K : ∀ i, C (X i).left) (i : I) (P : C (X i).left)
    {W : Over B} (e : Expression B I X W) (h : ∀ j, e.occurrenceLabel j ≠ i) :
    (e.evaluate d).obj (Function.update K i P) = (e.evaluate d).obj K := by
  induction e with
  | var j =>
    exact Function.update_of_ne (h PUnit.unit) P K
  | pull f e ih => exact congrArg (d.pull f.left).obj (ih h)
  | push f hp e ih => exact congrArg (d.push f.left).obj (ih h)
  | shriek j hj hq e ih =>
    let := hj
    exact congrArg (d.shriek j.left).obj (ih h)
  | compactSupport f c e ih => exact congrArg (d.compactSupport f.left c).obj (ih h)
  | tensor e t ih jt =>
    exact congrArg (d.tensor _).obj
      (Prod.ext (ih (fun j ↦ h (Sum.inl j))) (jt (fun j ↦ h (Sum.inr j))))

/-- Every independently labelled input has a context in the explicit search.
Source: blueprint, independent leaf indexing
(blueprint: def-pur-integral-expression-occurrences).

Proof: surjectivity of the label map gives a leaf with label i. Follow its path
through the tree. Unary vertices preserve successful searches. At a tensor the
leaf is in one of the two disjoint occurrence sets. Injectivity excludes an
occurrence of i in the other subtree, so the search reaches precisely that branch.
A variable labelled i returns the input context. Thus the resulting Option is some. -/
theorem IndependentExpression.variableContext_isSome {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C (X i).left) (i : I) : (e.val.variableContext d K i).isSome := by
  exact (variableContext_isSome_iff d K i e.val).mpr (e.property.surjective i)

/-- Extract the context from the successful explicit tree search. The proof only
certifies Option.get; it does not choose a context from an existence theorem.
Source: blueprint, independent input slots
(blueprint: def-pur-integral-expression-occurrences). -/
def IndependentExpression.variableContext {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C (X i).left) (i : I) : Expression.SlotContext d (X i) W :=
  (e.val.variableContext d K i).get (e.variableContext_isSome d K i)

open Classical in
private theorem variableContext_evaluate_of_some {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) (K : ∀ i, C (X i).left) (i : I) (P : C (X i).left)
    {W : Over B} (e : Expression B I X W) (h : Function.Injective e.occurrenceLabel)
    (c : Expression.SlotContext d (X i) W) (hc : e.variableContext d K i = some c) :
    c.evaluate.obj P = (e.evaluate d).obj (Function.update K i P) := by
  induction e with
  | var j =>
    by_cases hij : i = j
    · subst j
      simp [Expression.variableContext] at hc
      subst c
      simp [Expression.SlotContext.evaluate, Expression.evaluate]
    · simp [Expression.variableContext, hij] at hc
  | pull f e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact congrArg (d.pull f.left).obj (ih h c' hc')
  | push f hp e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact congrArg (d.push f.left).obj (ih h c' hc')
  | shriek j hj hq e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    let := hj
    exact congrArg (d.shriek j.left).obj (ih h c' hc')
  | compactSupport f c e ih =>
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
    exact congrArg (d.compactSupport f.left c).obj (ih h c' hc')
  | tensor e t ih jt =>
    have hl : Function.Injective e.occurrenceLabel :=
      fun a b hab ↦ Sum.inl.inj (h (a₁ := Sum.inl a) (a₂ := Sum.inl b) hab)
    have hr : Function.Injective t.occurrenceLabel :=
      fun a b hab ↦ Sum.inr.inj (h (a₁ := Sum.inr a) (a₂ := Sum.inr b) hab)
    cases he : e.variableContext d K i with
    | some c' =>
      have hex := (variableContext_isSome_iff d K i e).mp (by simp [he])
      obtain ⟨j, hj⟩ := hex
      have ha : ∀ k, t.occurrenceLabel k ≠ i := by
        intro k hk
        have bad := h (a₁ := Sum.inl j) (a₂ := Sum.inr k) (hj.trans hk.symm)
        cases bad
      simp only [Expression.variableContext, he, Option.some.injEq] at hc
      subst c
      change (d.tensor _).obj (_, _) = (d.tensor _).obj (_, _)
      exact congrArg (d.tensor _).obj
        (Prod.ext (ih hl c' he) (evaluate_update_absent d K i P t ha).symm)
    | none =>
      have ha : ∀ k, e.occurrenceLabel k ≠ i := by
        intro k hk
        have bad := (variableContext_isSome_iff d K i e).mpr ⟨k, hk⟩
        simp [he] at bad
      simp only [Expression.variableContext, he] at hc
      obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hc
      change (d.tensor _).obj (_, _) = (d.tensor _).obj (_, _)
      exact congrArg (d.tensor _).obj
        (Prod.ext (evaluate_update_absent d K i P e ha).symm (jt hr c' hc'))

open Classical in
/-- Replacing the sole occurrence of a label is evaluation of its actual context.
Source: blueprint, slotwise comparison
(blueprint: def-pur-integral-expression-occurrences).

Proof: induct along the successful search. At a variable, bijectivity identifies
its label with i and the context is identity. Unary functor evaluation preserves
the equality. At a tensor the nonselected subtree has no occurrence of i, by
injectivity of the global leaf-label map. Its evaluation therefore ignores the
update. The selected subtree satisfies the inductive identity, so the respective
curried tensor gives the stated equality. The same induction with P = K i gives
the second equality, since update at the current value is the original family. -/
theorem IndependentExpression.variableContext_evaluate {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    (d : Interpretation C) {W : Over B} (e : IndependentExpression B I X W)
    (K : ∀ i, C (X i).left) (i : I) (P : C (X i).left) :
    ((e.variableContext d K i).evaluate).obj P =
      (e.val.evaluate d).obj (Function.update K i P) ∧
    ((e.variableContext d K i).evaluate).obj (K i) = (e.val.evaluate d).obj K := by
  have hP := variableContext_evaluate_of_some d K i P e.val e.property.injective
    (e.variableContext d K i) (Option.some_get _).symm
  refine ⟨hP, ?_⟩
  have hK := variableContext_evaluate_of_some d K i (K i) e.val e.property.injective
    (e.variableContext d K i) (Option.some_get _).symm
  simpa only [Function.update_eq_self] using hK

end WeilConjectures.IntegralSystemRealization
