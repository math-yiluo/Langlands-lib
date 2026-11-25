/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Germ
public import WeilConjectures.SixFunctors.ProEtale.OpenClosed.ClosedLiftSections
public import WeilConjectures.TraceFormula.Specialization.Trait
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftConnectedComponents
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftStrictlyHenselian
public import WeilConjectures.RingTheory.ProEtale.SpanIdempotents

/-!

# Geometric generic fibres of henselian lifts over the trait

Let `k'` be a separably closed field, `A = k'⟦t⟧` and `C̄` a w-contractible ind-étale
`A ⧸ (t)`-algebra. Its henselian lift `H = H_A(C̄)` is a filtered colimit of finite products
of copies of `A` (an étale `A`-algebra over the strictly henselian `A` is a product of copies of
`A` and of an algebra on which `t` is invertible, and the latter maps to zero in `C̄`). Hence
the geometric generic fibre `H ⊗_A Ω` is a filtered colimit of finite products of copies of the
algebraically closed field `Ω`, with the same extremally disconnected space of connected
components as `C̄`: it is w-contractible
(`AlgebraicGeometry.ProEtale.isWContractibleRing_closedLift_tensorProduct_traitGenericField`), and
the base change of `W = Spec H` to the geometric
generic point `Spec Ω ⟶ S` is weakly contractible
(`AlgebraicGeometry.ProEtale.isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec`).

-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {k' : Type u} [Field k'] [IsSepClosed k']

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The geometric generic fibre `H ⊗_{k'⟦t⟧} Ω` of the henselian lift `H = H_{k'⟦t⟧}(C̄)` of a
w-contractible ind-étale `k'⟦t⟧ ⧸ (t)`-algebra `C̄` is w-contractible: it is spanned over `Ω` by
idempotents coming from `H`, and its space of connected components is that of `Spec H`, hence
that of `Spec C̄`. -/
theorem isWContractibleRing_closedLift_tensorProduct_traitGenericField (C : Type u) [CommRing C]
    [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    [Algebra (PowerSeries k') C]
    [IsScalarTower (PowerSeries k')
      (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    (hC : IsWContractibleRing C) :
    IsWContractibleRing (CommRingCat.of
      (Algebra.ClosedLift (PowerSeries k') C ⊗[PowerSeries k'] traitGenericField k')) := by
  let H := Algebra.ClosedLift (PowerSeries k') C
  let Ω := traitGenericField k'
  let φ : H →ₐ[PowerSeries k'] H ⊗[PowerSeries k'] Ω := Algebra.TensorProduct.includeLeft
  let E : Set (H ⊗[PowerSeries k'] Ω) := φ '' {e | IsIdempotentElem e}
  have hE : ∀ x ∈ E, IsIdempotentElem x := by
    rintro _ ⟨e, he, rfl⟩
    exact he.map φ
  have hC0 (a : PowerSeries k') (ha : a ∈ IsLocalRing.maximalIdeal (PowerSeries k')) :
      algebraMap (PowerSeries k') C a = 0 := by
    rw [PowerSeries.maximalIdeal_eq_span_X] at ha
    rw [IsScalarTower.algebraMap_apply (PowerSeries k')
      (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hR (x : H ⊗[PowerSeries k'] Ω) : x ∈ Submodule.span Ω E := by
    have htmul (h : H) (hh : h ∈ Submodule.span (PowerSeries k') {e : H | IsIdempotentElem e})
        (ω : Ω) : h ⊗ₜ[PowerSeries k'] ω ∈ Submodule.span Ω E := by
      induction hh using Submodule.span_induction generalizing ω with
      | mem e he =>
        have : e ⊗ₜ[PowerSeries k'] ω = ω • φ e := by
          simp [φ, Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, he, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa [TensorProduct.add_tmul] using add_mem (hx ω) (hy ω)
      | smul a x _ hx => simpa [TensorProduct.smul_tmul] using hx (a • ω)
    induction x using TensorProduct.inductionOn with
    | tmul h ω => exact htmul h (Algebra.ClosedLift.mem_span_isIdempotentElem hC0 h) ω
    | add x y hx hy => exact add_mem hx hy
  have hφ : Function.Injective φ := Algebra.ClosedLift.injective_includeLeft
    ((algebraMap (FractionRing (PowerSeries k')) Ω).injective.comp
      (IsFractionRing.injective (PowerSeries k') (FractionRing (PowerSeries k'))))
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum H)) := by
    have := hC.extremallyDisconnected_connectedComponents
    refine extremallyDisconnected_of_homeo (PrimeSpectrum.isHomeomorph_connectedComponentsMap_comap
      (Algebra.ClosedLift.toAlgHom (PowerSeries k') C).toRingHom (fun p₁ p₂ h ↦ ?_)
      fun e he h0 ↦ Algebra.ClosedLift.eq_zero_of_isIdempotentElem he h0).homeomorph
    obtain ⟨c, hc, h₁, h₂⟩ := PrimeSpectrum.exists_isIdempotentElem_of_connectedComponents_mk_ne h
    obtain ⟨e, he, rfl⟩ := Algebra.ClosedLift.exists_isIdempotentElem_toAlgHom_eq
      (Ideal.span {(PowerSeries.X : PowerSeries k')}) hc
    exact ⟨e, he, h₁, h₂⟩
  have : ExtremallyDisconnected
      (ConnectedComponents (PrimeSpectrum (H ⊗[PowerSeries k'] Ω))) := by
    refine extremallyDisconnected_of_homeo (PrimeSpectrum.isHomeomorph_connectedComponentsMap_comap
      φ.toRingHom (fun p₁ p₂ h ↦ ?_) fun e _ h0 ↦ hφ (by simpa using h0)).homeomorph.symm
    by_contra hcon
    push Not at hcon
    refine h (congrArg ConnectedComponents.mk (PrimeSpectrum.ext
      (Ideal.eq_of_forall_mem_span_isIdempotentElem hE hR ?_)))
    rintro _ ⟨e, he, rfl⟩
    have hmul : φ e * φ (1 - e) = 0 := by
      rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, map_zero]
    have hadd : φ e + φ (1 - e) = 1 := by
      rw [← map_add, add_sub_cancel, map_one]
    refine ⟨fun h₁ ↦ ?_, fun h₂ ↦ by_contra fun h₁ ↦ hcon e he h₁ h₂⟩
    have h₁' : φ (1 - e) ∉ p₁.asIdeal := fun h ↦
      p₁.isPrime.one_notMem (hadd ▸ add_mem h₁ h)
    exact ((p₂.isPrime.mem_or_mem (hmul ▸ p₂.asIdeal.zero_mem)).resolve_right
      (hcon _ he.one_sub h₁'))
  exact IsWContractibleRing.of_forall_mem_span_isIdempotentElem hE hR

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The henselian lift `W = Spec H_{k'⟦t⟧}(C̄)` of a w-contractible ind-étale
`k'⟦t⟧ ⧸ (t)`-algebra `C̄` has a weakly contractible geometric generic fibre
`W ×_S Spec Ω`. -/
theorem isWeaklyContractible_pullback_traitGenericPoint_closedLiftSpec (C : Type u) [CommRing C]
    [Algebra (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    [Algebra (PowerSeries k') C]
    [IsScalarTower (PowerSeries k')
      (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    [Algebra.IndEtale (PowerSeries k' ⧸ Ideal.span {(PowerSeries.X : PowerSeries k')}) C]
    (hC : IsWContractibleRing C) :
    (ProEt.topology (Spec (.of (traitGenericField k')))).IsWeaklyContractible.{u + 1}
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (traitGenericPoint k')).obj
        (closedLiftSpec (.of (PowerSeries k')) C)) :=
  have := isWContractibleRing_closedLift_tensorProduct_traitGenericField (k' := k') C hC
  Scheme.ProEt.isWeaklyContractible_of_iso
    (pullbackSpecIso (PowerSeries k') (Algebra.ClosedLift (PowerSeries k') C)
      (traitGenericField k'))

end AlgebraicGeometry.ProEtale
