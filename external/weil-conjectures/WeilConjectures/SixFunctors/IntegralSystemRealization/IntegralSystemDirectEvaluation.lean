/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralDirectEvaluationMateInvertible
import WeilConjectures.SixFunctors.IntegralSystemRealization.Pull.IntegralPullEvaluationQuotientSquare
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Evaluation of a normalized derived system direct image

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section MateNaturality
universe a av b bv c cv e ev c' cv' e' ev'
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  {Fs : A ⥤ B} {Gs : B ⥤ A} (asys : Fs ⊣ Gs)
  {Fl : C ⥤ D} {Gl : D ⥤ C} (alevel : Fl ⊣ Gl)
  {EA EA' : A ⥤ C} {EB EB' : B ⥤ D}

private theorem mate_whiskerTop (τ : TwoSquare EA Fs Fl EB) (γ : EA' ⟶ EA) :
    mateEquiv asys alevel (τ.whiskerTop γ) =
      (mateEquiv asys alevel τ).whiskerRight γ := by
  ext M
  simp only [mateEquiv, TwoSquare.whiskerTop, TwoSquare.whiskerRight,
    Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, TwoSquare] at τ ⊢
  erw [Category.comp_id]
  have hu := alevel.unit_naturality (γ.app (Gs.obj M))
  simpa only [Category.assoc, Category.comp_id, Category.id_comp,
    Functor.comp_obj, Functor.id_obj] using congrArg (fun f ↦ f ≫
    Gl.map (τ.app (Gs.obj M)) ≫ Gl.map (EB.map (asys.counit.app M))) hu

private theorem mate_whiskerBottom (τ : TwoSquare EA Fs Fl EB) (γ : EB ⟶ EB') :
    mateEquiv asys alevel (τ.whiskerBottom γ) =
      (mateEquiv asys alevel τ).whiskerLeft γ := by
  ext M
  simp only [mateEquiv, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    Equiv.coe_fn_mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj, TwoSquare] at τ ⊢
  erw [Category.comp_id, Category.id_comp]
  have hn := γ.naturality (asys.counit.app M)
  have hh := congrArg (fun f ↦ alevel.unit.app (EA.obj (Gs.obj M)) ≫
    Gl.map (τ.app (Gs.obj M)) ≫ Gl.map f) hn
  simpa only [Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp,
    Functor.comp_obj, Functor.id_obj] using hh.symm

variable {C' : Type c'} [Category.{cv'} C'] {D' : Type e'} [Category.{ev'} D']
  {Fn : C' ⥤ D'} {Gn : D' ⥤ C'} (an : Fn ⊣ Gn)
  (RA : C' ⥤ C) (RB : D' ⥤ D)
  (EA₀ : A ⥤ C) (EA₁ : A ⥤ C') (EB₀ : B ⥤ D) (EB₁ : B ⥤ D')
  (α₀ : Fs ⋙ EB₀ ≅ EA₀ ⋙ Fl) (α₁ : Fs ⋙ EB₁ ≅ EA₁ ⋙ Fn)
  (δ : RA ⋙ Fl ⟶ Fn ⋙ RB)
  (tA : EA₀ ⟶ EA₁ ⋙ RA) (tB : EB₀ ⟶ EB₁ ⋙ RB)

private theorem transition_mates
    (ht : ∀ H, tB.app (Fs.obj H) ≫ RB.map (α₁.hom.app H) =
      α₀.hom.app H ≫ Fl.map (tA.app H) ≫ δ.app (EA₁.obj H)) (M : B) :
    tA.app (Gs.obj M) ≫
      RA.map ((mateEquiv asys an (TwoSquare.mk _ _ _ _ α₁.inv)).app M) ≫
      (mateEquiv an alevel (TwoSquare.mk _ _ _ _ δ)).app (EB₁.obj M) =
    (mateEquiv asys alevel (TwoSquare.mk _ _ _ _ α₀.inv)).app M ≫
      Gl.map (tB.app M) := by
  let τ₁ : TwoSquare EA₁ Fs Fn EB₁ := α₁.inv
  let τ₂ : TwoSquare RA Fn Fl RB := δ
  let τ₀ : TwoSquare EA₀ Fs Fl EB₀ := α₀.inv
  have hh : (τ₁.hComp τ₂).whiskerTop tA = τ₀.whiskerBottom tB := by
    ext H
    dsimp only [τ₀, τ₁, τ₂]
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    apply (cancel_epi (α₀.hom.app H)).1
    apply (cancel_mono (RB.map (α₁.hom.app H))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← RB.map_comp,
      Iso.inv_hom_id_app]
    erw [RB.map_id, Category.comp_id]
    exact (ht H).symm
  have hm := congrArg (mateEquiv asys alevel) hh
  rw [mate_whiskerTop asys alevel, mate_whiskerBottom asys alevel,
    mateEquiv_vcomp asys an alevel] at hm
  have hc := congr_app hm M
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using hc

end MateNaturality

private theorem restrictedDirect_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ r : normalizedDVRRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRRes l E Y (Nat.le_succ n),
      HEq r (sfDerivedImageRestriction f
        (Padic.coefficientExtensionTransition l E (n + 1))) := by
  have h (W : Scheme.{u}) :
      (proEtaleCoefficientRestrictScalars W
        (Padic.coefficientExtensionTransition l E (n + 1))).mapDerivedCategory =
          normalizedDVRRes l E W (Nat.le_succ n) := by
    unfold normalizedDVRRes
    congr 1
    exact originRestrictionEquality l E W n
  rw [← h X, ← h Y]
  exact ⟨sfDerivedImageRestriction f
    (Padic.coefficientExtensionTransition l E (n + 1)), HEq.rfl⟩

/-- Evaluation of the universal right derived sequence-site direct image, including
its adjunction and adjacent quotient normalizations.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941, 07A7
(blueprint: lem-sf-integral-system-direct-evaluation).

Proof: evaluation at n has a left derived finite left extension. On flat-term
K-flat representatives the ordinary extension is zero above n and, at q at most n,
is extension of scalars to the q-th quotient. Exact geometric inverse image
commutes with this extension: its quotient pure-tensor map preserves balancing,
transition maps and the zero components. Deriving gives the same interchange,
without assuming quotient-ring flatness. Transpose through both finite-extension
adjunctions and the geometric adjunctions. Yoneda gives the displayed direct-image
evaluation isomorphism. The n-th component of the extension comparison is the
identity, so the transposed counit is the finite counit; the triangle identities
give the unit equation. The universal right-derived certificate and the factors
field identify these adjunctions with d.adj, fixing its normalization.
For adjacent quotients, take the published scalar-restriction comparison
sfDerivedImageRestriction itself. The finite-extension interchange commutes
with the canonical quotient maps: below n both maps send a pure tensor to its
quotient, and above n the source is zero. Transposing this equality gives exactly
the transition equation with coefficientSequenceDerivedTransition. These are
identities of system morphisms before localization, so evaluation faithfulness
on derived morphisms is unnecessary. Zero complexes and n = 0 obey the same
formulas; no boundedness, normalization of the input, or invertibility of l on
the schemes is required. -/
theorem integralSystemDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : Direct l E f) : Nonempty (DirectEvaluation l E d) := by
  let β (n : ℕ) := (mateEquiv d.adj (finiteAdj l E f n)
    (TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f n).inv))
  have hβ (n : ℕ) : IsIso (β n) := integralDirectEvaluationMate_invertible l E f d n
  let e (n : ℕ) := asIso (β n)
  let r (n : ℕ) := (restrictedDirect_exists l E f n).choose
  have hr (n : ℕ) := (restrictedDirect_exists l E f n).choose_spec
  refine ⟨{
    evaluation := e
    unit := ?_
    counit := ?_
    restrictedDirect := r
    restrictedDirectCanonical := hr
    transition := ?_ }⟩
  · intro n M
    have hu := unit_mateEquiv d.adj (finiteAdj l E f n)
      (TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f n).inv) M
    change _ ≫ (β n).app _ ≫ _ = _
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp]
    erw [Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  · intro n M
    change _ ≫ (finiteDerivedPullback l E n f).map ((β n).app M) ≫ _ = _
    rw [mateEquiv_counit, Iso.hom_inv_id_app_assoc]
  · intro n M
    let δ := ((mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))).symm
      (TwoSquare.mk _ _ _ _ (r n).inv))
    have ht := transition_mates d.adj (finiteAdj l E f (n + 1)) (finiteAdj l E f n)
      (normalizedDVRRes l E Y (Nat.le_succ n))
      (normalizedDVRRes l E X (Nat.le_succ n))
      (coefficientSequenceDerivedEvaluation l E Y (n + 1))
      (coefficientSequenceDerivedEvaluation l E Y n)
      (coefficientSequenceDerivedEvaluation l E X (n + 1))
      (coefficientSequenceDerivedEvaluation l E X n)
      (pullbackTensorDerivedEvaluation l E f (n + 1))
      (pullbackTensorDerivedEvaluation l E f n) δ
      (coefficientSequenceDerivedTransition l E Y (Nat.le_succ n))
      (coefficientSequenceDerivedTransition l E X (Nat.le_succ n))
      (integralPullEvaluation_quotientSquare l E f n (r n) (hr n)) M
    have hδ : mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))
        (TwoSquare.mk _ _ _ _ δ) = TwoSquare.mk _ _ _ _ (r n).inv :=
      (mateEquiv (finiteAdj l E f n) (finiteAdj l E f (n + 1))).apply_symm_apply _
    rw [hδ] at ht
    have hh := congrArg (fun z ↦ z ≫ (r n).hom.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj M)) ht
    simp only [Category.assoc, Iso.inv_hom_id_app] at hh
    erw [Category.comp_id] at hh
    exact hh

end WeilConjectures.IntegralSystemRealization
