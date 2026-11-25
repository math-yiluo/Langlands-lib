/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PrimitiveElement
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisMinpoly

/-!

# `K((t)) ⊗_{k'((t))} k'((t))^sep` is a field

Let `F ⊆ L` be fields such that `F` is separably closed in `L`. Then `L` is linearly disjoint
from every separable algebraic extension of `F`: for a simple extension `F(β)` this is the
equality of minimal polynomials `minpoly.map_algebraMap_of_isSeparable` (the powers
`1, β, …, β^{n-1}` stay `L`-linearly independent), and the general case follows since linear
disjointness is checked on finite subextensions, which are simple by the primitive element
theorem. Consequently `M ⊗_F L` is a field for every separable algebraic `M / F`
(`Algebra.TensorProduct.isField_of_isSeparable_of_forall_mem_range`).

For the slice of SGA 4½, [Th. finitude], Lemme 3.3 (`F = k'((t))`, `F_K = K((t))`, `Ω = F^alg`):

* `AlgebraicGeometry.isField_separableClosure_tensorProduct_traitLaurentField`:
  `F^sep ⊗_F F_K` is a field;
* `AlgebraicGeometry.isHomeomorph_comap_traitGenericField_tensorProduct`:
  `Spec(Ω ⊗_F F_K) ⟶ Spec(F^sep ⊗_F F_K)` is a homeomorphism (`Ω / F^sep` is purely
  inseparable);
* `AlgebraicGeometry.subsingleton_primeSpectrum_traitGenericField_tensorProduct`:
  hence `Spec(Ω ⊗_F F_K)` is a single point.

-/

@[expose] public section

open Polynomial IntermediateField

open scoped TensorProduct IntermediateField

section General

variable {F L E : Type*} [Field F] [Field L] [Field E] [Algebra F L] [Algebra L E] [Algebra F E]
  [IsScalarTower F L E]

/-- If `F` is separably closed in `L` and `β ∈ E ⊇ L` is separable over `F`, then `F(β)` and
`L` are linearly disjoint over `F`: the power basis of `F(β)` stays `L`-linearly independent,
since the minimal polynomial of `β` over `L` is that over `F`. -/
theorem IntermediateField.linearDisjoint_adjoin_simple_of_isSeparable
    (hL : ∀ c : L, IsSeparable F c → c ∈ (algebraMap F L).range) {β : E}
    (hβ : IsSeparable F β) : F⟮β⟯.LinearDisjoint L := by
  have hβi : IsIntegral F β := hβ.isIntegral
  let pb := IntermediateField.adjoin.powerBasis hβi
  refine IntermediateField.LinearDisjoint.of_basis_left pb.basis ?_
  have hdeg : (minpoly L β).natDegree = pb.dim := by
    rw [← minpoly.map_algebraMap_of_isSeparable hL hβ, natDegree_map, adjoin.powerBasis_dim]
  convert (linearIndependent_pow (K := L) β).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
    using 1
  ext i
  simp [pb, adjoin.powerBasis_gen]

/-- If `F` is separably closed in `L`, then every intermediate field `A` of `E ⊇ L` separable over
`F` is linearly disjoint from `L` over `F`: it suffices to check finite subextensions, which are
simple. -/
theorem IntermediateField.linearDisjoint_of_isSeparable
    (hL : ∀ c : L, IsSeparable F c → c ∈ (algebraMap F L).range) (A : IntermediateField F E)
    [Algebra.IsSeparable F A] : A.LinearDisjoint L := by
  rw [IntermediateField.linearDisjoint_iff]
  have : Algebra.IsIntegral F A.toSubalgebra := inferInstanceAs (Algebra.IsIntegral F A)
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ ↦ ?_
  have hBi : ∀ x ∈ B, IsIntegral F x := fun x hx ↦
    (Algebra.IsIntegral.isIntegral (R := F) (⟨x, hx⟩ : B)).map B.val
  let I : IntermediateField F E :=
    B.toIntermediateField fun x hx ↦ B.inv_mem_of_algebraic (x := ⟨x, hx⟩) (hBi x hx).isAlgebraic
  have : FiniteDimensional F I := inferInstanceAs (Module.Finite F B)
  have hsep : ∀ x ∈ B, IsSeparable F x := fun x hx ↦
    (isSeparable_map_iff A.val Subtype.val_injective).mpr
      (Algebra.IsSeparable.isSeparable F (⟨x, hB hx⟩ : A))
  have : Algebra.IsSeparable F I := ⟨fun y ↦ IsSeparable.of_algHom F I.val (hsep y y.2)⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F I
  have hI : F⟮(α : E)⟯ = I := by rw [← lift_adjoin_simple, hα, lift_top]
  have h := IntermediateField.linearDisjoint_adjoin_simple_of_isSeparable hL (hsep α α.2)
  rw [hI] at h
  exact h

/-- If `F` is separably closed in `L` and `M / F` is separable algebraic, then `M ⊗_F L` is a
field. -/
theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_mem_range
    (hL : ∀ c : L, IsSeparable F c → c ∈ (algebraMap F L).range) (M : Type*) [Field M]
    [Algebra F M] [Algebra.IsSeparable F M] : IsField (M ⊗[F] L) := by
  let fb : M →ₐ[F] AlgebraicClosure L := IsAlgClosed.lift
  let e : M ≃ₐ[F] fb.fieldRange := AlgEquiv.ofInjectiveField fb
  have : Algebra.IsSeparable F fb.fieldRange := AlgEquiv.Algebra.isSeparable e
  have H := (IntermediateField.linearDisjoint_of_isSeparable hL
    fb.fieldRange).isField_of_isAlgebraic (Or.inl inferInstance)
  exact (Algebra.TensorProduct.congr e AlgEquiv.refl).toMulEquiv.isField H

end General

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] [IsSepClosed k'] {K : Type u} [Field K] [Algebra k' K]
  [IsAlgClosed K]

/-- **`F^sep ⊗_F F_K` is a field** for `F = k'((t))`, `F_K = K((t))`, `k'` separably closed and
`K` algebraically closed of transcendence degree `≤ 1` over `k'`; `F^sep` is the separable
closure of `F` in `Ω = F^alg` (`AlgebraicGeometry.traitGenericField`). -/
theorem isField_separableClosure_tensorProduct_traitLaurentField
    (htr : Algebra.trdeg k' K ≤ 1) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    IsField (separableClosure (FractionRing (PowerSeries k')) (traitGenericField k') ⊗[
      FractionRing (PowerSeries k')] FractionRing (PowerSeries K)) := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  exact Algebra.TensorProduct.isField_of_isSeparable_of_forall_mem_range
    (fun c hc ↦ mem_range_traitLaurentFieldMap_of_isSeparable htr c hc) _


omit [IsSepClosed k'] [IsAlgClosed K] in
/-- `Spec(Ω ⊗_F F_K) ⟶ Spec(F^sep ⊗_F F_K)` is a homeomorphism, `Ω / F^sep` being purely
inseparable. -/
theorem isHomeomorph_comap_traitGenericField_tensorProduct :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    IsHomeomorph (PrimeSpectrum.comap (Algebra.TensorProduct.map
      (Algebra.ofId (separableClosure (FractionRing (PowerSeries k')) (traitGenericField k'))
        (traitGenericField k'))
      (AlgHom.id (FractionRing (PowerSeries k')) (FractionRing (PowerSeries K)))).toRingHom) := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  exact PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable _ _ _ _

/-- **`Spec(Ω ⊗_F F_K)` has at most one point** (exactly one, the ring being nonzero): it is
homeomorphic to the spectrum of the field `F^sep ⊗_F F_K`. -/
theorem subsingleton_primeSpectrum_traitGenericField_tensorProduct
    (htr : Algebra.trdeg k' K ≤ 1) :
    letI := (traitLaurentFieldMap k' K).toAlgebra
    Subsingleton (PrimeSpectrum (traitGenericField k' ⊗[FractionRing (PowerSeries k')]
      FractionRing (PowerSeries K))) := by
  let := (traitLaurentFieldMap k' K).toAlgebra
  have hF := isField_separableClosure_tensorProduct_traitLaurentField (K := K) htr
  have hbot : ∀ p : PrimeSpectrum (separableClosure (FractionRing (PowerSeries k'))
      (traitGenericField k') ⊗[FractionRing (PowerSeries k')] FractionRing (PowerSeries K)),
      p.asIdeal = ⊥ := fun p ↦ by
    refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ by_contra fun hx0 ↦ p.2.ne_top ?_
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hx0
    exact (Ideal.eq_top_iff_one _).mpr (hy ▸ p.asIdeal.mul_mem_right y hx)
  refine ⟨fun p q ↦ (isHomeomorph_comap_traitGenericField_tensorProduct (K := K)).injective ?_⟩
  ext1
  rw [hbot, hbot]

end AlgebraicGeometry
