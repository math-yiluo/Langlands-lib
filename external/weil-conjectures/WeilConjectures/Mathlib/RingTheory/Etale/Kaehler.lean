/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# An étaleness criterion via Kähler differentials

## Main results

- `Algebra.FormallyEtale.of_bijective_mapBaseChange`: for `R → S → T` with `H¹(L_{T/R}) = 0`
  (e.g. `T` formally smooth over `R`), if `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then `T` is
  formally étale over `S`.
- `MvPolynomial.etale_aeval_of_basis_kaehlerDifferential`: if `T` is smooth over `R` and
  `Ω[T⁄R]` has a basis `d uᵢ` for a finite family `uᵢ : T`, then `R[Xᵢ] → T`, `Xᵢ ↦ uᵢ`, is
  étale.
-/

@[expose] public section

open KaehlerDifferential TensorProduct

namespace Algebra

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

/-- Let `R → S → T` with `H¹(L_{T/R}) = 0`. If `T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` is bijective, then
`T` is formally étale over `S`: `Ω[T⁄S]` is its cokernel, and the Jacobi–Zariski sequence
`H¹(L_{T/R}) → H¹(L_{T/S}) → T ⊗[S] Ω[S⁄R] → Ω[T⁄R]` shows `H¹(L_{T/S}) = 0`. -/
theorem FormallyEtale.of_bijective_mapBaseChange [Subsingleton (H1Cotangent R T)]
    (h : Function.Bijective (mapBaseChange R S T)) : FormallyEtale S T := by
  refine ⟨⟨fun x y ↦ ?_⟩, ⟨fun x y ↦ ?_⟩⟩
  · have hz : ∀ z : Ω[T⁄S], z = 0 := fun z ↦ by
      obtain ⟨w, rfl⟩ := KaehlerDifferential.map_surjective R S T z
      obtain ⟨v, rfl⟩ := h.2 w
      exact (exact_mapBaseChange_map R S T _).mpr ⟨v, rfl⟩
    rw [hz x, hz y]
  · have hz : ∀ z : H1Cotangent S T, z = 0 := fun z ↦ by
      have hδ : H1Cotangent.δ R S T z = 0 := by
        apply h.1
        rw [map_zero]
        exact (H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := (H1Cotangent.exact_map_δ R S T z).mp hδ
      rw [Subsingleton.elim w 0, map_zero]
    rw [hz x, hz y]

end Algebra

namespace MvPolynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]

/-- If `T` is smooth over `R` and `Ω[T⁄R]` has a basis `d uᵢ` for a finite family `uᵢ : T`,
then `R[Xᵢ] → T`, `Xᵢ ↦ uᵢ`, is étale. -/
theorem etale_aeval_of_basis_kaehlerDifferential [Algebra.FormallySmooth R T]
    [Algebra.FinitePresentation R T] {ι : Type*} [Finite ι] (u : ι → T)
    (b : Module.Basis ι T Ω[T⁄R]) (hb : ∀ i, b i = D R T (u i)) :
    (aeval u : MvPolynomial ι R →ₐ[R] T).toRingHom.Etale := by
  let := (aeval u : MvPolynomial ι R →ₐ[R] T).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) T :=
    .of_algebraMap_eq fun r ↦ ((aeval u).commutes r).symm
  change (algebraMap (MvPolynomial ι R) T).Etale
  rw [RingHom.etale_algebraMap]
  have hX : ∀ i, mvPolynomialBasis R ι i = D R (MvPolynomial ι R) (X i) := fun i ↦
    (mvPolynomialBasis R ι).repr.injective (by simp)
  let b' := (mvPolynomialBasis R ι).baseChange T
  have hmap : mapBaseChange R (MvPolynomial ι R) T = (b'.equiv b (Equiv.refl ι)).toLinearMap := by
    refine b'.ext fun i ↦ ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, hb]
    simp only [b', Module.Basis.baseChange_apply, hX, mapBaseChange_tmul, map_D, one_smul]
    change D R T (aeval u (X i)) = _
    rw [aeval_X]
  have : Algebra.FormallyEtale (MvPolynomial ι R) T := .of_bijective_mapBaseChange R _ T
    (by rw [hmap]; exact LinearEquiv.bijective _)
  have : Algebra.FinitePresentation (MvPolynomial ι R) T :=
    .of_restrict_scalars_finitePresentation R _ T
  exact {}

end MvPolynomial
