/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRootsNaturality
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.WeilSheaf.SmoothPurityCyclotomicField

/-!
# The geometric Frobenius on the trivialized sheaves of roots of unity

Let `k` be a finite field with `q` elements, `k̄` its algebraic closure, `σ = Spec γ` the
automorphism of `Spec k̄` given by the geometric Frobenius `γ = (x ↦ x ^ q)⁻¹`
(`AlgebraicGeometry.specGeometricFrobenius`), and `U` a scheme over `k̄` through `f`.
For `ζ ∈ k̄` with `ζ ^ N = 1`, the sheaf `μ_N` on `U_proét` is trivialized by the map
`ℤ ⟶ μ_N`, `a ↦ ζ ^ a` (`AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf f hζ`). This map
depends on the `k̄`-structure `f`: along the semilinear structure `f ≫ σ` it becomes `a ↦ γ(ζ) ^ a`
(`AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf_comp_Spec_map`, from
`WeilConjectures.WeilSheaf.SmoothPurityRootsNaturality`), and since `γ(ζ) = ζ ^ c`
for the value `c ∈ ℤ/N` of the modular cyclotomic character of `γ`, it is `c` times the
trivialization along `f`
(`AlgebraicGeometry.ProEtale.unitToRootsOfUnitySheaf_comp_specGeometricFrobenius`).

Applied to the geometric fibre `X̄ = X₀ ×_k k̄` of a `k`-scheme `X₀` with its geometric Galois
Frobenius `g = 𝟙 × σ` (`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`), which satisfies
`g ≫ a = a ≫ σ` for the structure morphism `a : X̄ ⟶ Spec k̄`, this computes the pullback of
roots of unity along `g` on the trivialized sheaf `μ_{ℓⁿ} ≅ ℤ/ℓⁿ`: it is multiplication by
`c = χ_ℓ(γ) mod ℓⁿ`, the reduction of the `ℓ`-adic cyclotomic character of the geometric
Frobenius, which is `q⁻¹`
(`AlgebraicGeometry.WeilSheaf.purity_modularCyclotomicCharacter_geometricFrobenius_mul`); this is
`AlgebraicGeometry.ProEtale.upperStar_map_unitToRootsOfUnitySheaf_geometricGaloisFrobenius`.
This is the finite-level input of the identification of the Tate twist `ℚ̄_ℓ(1)` of roots of
unity, pulled back to the geometric fibre with its canonical Weil structure, with the constant
Weil twist by `χ_ℓ(γ)` (`AlgebraicGeometry.WeilSheaf.tateTwistSheaf_one`), blueprint
`prose-10-21`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme

section Field

variable {K : Type u} [Field K] {U : Scheme.{u}}

/-- `a ↦ (z ^ m) ^ a` is `m` times `a ↦ z ^ a`. -/
lemma unitToRootsOfUnity_pow {N : ℕ} (z : rootsOfUnity N K) (m : ℕ) :
    unitToRootsOfUnity (z ^ m) = (m : ℤ) • unitToRootsOfUnity z := by
  ext a
  apply ULift.ext
  simp only [unitToRootsOfUnity_apply, AddCommGrpCat.hom_zsmul, AddMonoidHom.zsmul_apply,
    ofMul_pow]
  rw [← natCast_zsmul]
  exact smul_comm _ _ _

/-- `a ↦ ζ ^ a` only depends on `ζ`. -/
lemma unitToRootsOfUnitySheaf_congr (f : U ⟶ Spec (.of K)) {N : ℕ} {ζ ζ' : K} (h : ζ = ζ')
    (hζ : ζ ^ N = 1) (hζ' : ζ' ^ N = 1) :
    unitToRootsOfUnitySheaf f hζ = unitToRootsOfUnitySheaf f hζ' := by
  subst h
  rfl

/-- On presheaves, `a ↦ (z ^ m) ^ a` is `m` times `a ↦ z ^ a`. -/
lemma unitToRootsOfUnityPresheaf_pow (f : U ⟶ Spec (.of K)) {N : ℕ} (z : rootsOfUnity N K)
    (m : ℕ) :
    unitToRootsOfUnityPresheaf f (z ^ m) = (m : ℤ) • unitToRootsOfUnityPresheaf f z := by
  ext V : 2
  rw [NatTrans.app_zsmul]
  dsimp only [unitToRootsOfUnityPresheaf]
  rw [unitToRootsOfUnity_pow, Preadditive.zsmul_comp]

/-- `a ↦ (ζ ^ m) ^ a` is `m` times `a ↦ ζ ^ a`. -/
lemma unitToRootsOfUnitySheaf_pow (f : U ⟶ Spec (.of K)) {N : ℕ} {ζ : K} (hζ : ζ ^ N = 1)
    (m : ℕ) (hζ' : (ζ ^ m) ^ N = 1) :
    unitToRootsOfUnitySheaf f hζ' = (m : ℤ) • unitToRootsOfUnitySheaf f hζ := by
  by_cases hN : N = 0
  · subst hN
    rw [unitToRootsOfUnitySheaf_of_eq_zero, unitToRootsOfUnitySheaf_of_eq_zero, smul_zero]
  · have : NeZero N := ⟨hN⟩
    rw [unitToRootsOfUnitySheaf_eq, unitToRootsOfUnitySheaf_eq, ← Functor.map_zsmul,
      ← unitToRootsOfUnityPresheaf_pow]
    congr 2
    ext
    simp

end Field

/-! ### The geometric Frobenius -/

section FiniteField

variable (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- The value `c ∈ (ℤ/ℓⁿ)ˣ` of the modular cyclotomic character of the geometric Frobenius
`γ = (x ↦ x ^ q)⁻¹` of `k̄`: `γ(ζ) = ζ ^ c` for every `ℓⁿ`-th root of unity `ζ` of `k̄`. It
satisfies `c q = 1`
(`AlgebraicGeometry.WeilSheaf.purity_modularCyclotomicCharacter_geometricFrobenius_mul`). -/
noncomputable def geometricFrobeniusModularCharacter (n : ℕ) : (ZMod (ℓ ^ n))ˣ :=
  haveI := WeilSheaf.purity_neZero_natCast_algebraicClosure k ℓ
  letI := Fintype.ofFinite k
  modularCyclotomicCharacter (AlgebraicClosure k)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure k) (ℓ ^ n))
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)).toRingEquiv

/-- `c q = 1` in `ℤ/ℓⁿ`. -/
lemma geometricFrobeniusModularCharacter_mul_natCard (n : ℕ) :
    ((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)) *
      (Nat.card k : ZMod (ℓ ^ n)) = 1 := by
  let := Fintype.ofFinite k
  exact WeilSheaf.purity_modularCyclotomicCharacter_geometricFrobenius_mul k ℓ n

/-- The geometric Frobenius raises an `ℓⁿ`-th root of unity `ζ` of `k̄` to the power `c`. -/
lemma geometricFrobeniusAlgEquivOfAlgebraic_apply_of_pow_eq_one (n : ℕ)
    {ζ : AlgebraicClosure k} (hζ : ζ ^ (ℓ ^ n) = 1) :
    letI := Fintype.ofFinite k
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ζ =
      ζ ^ ((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val := by
  have := WeilSheaf.purity_neZero_natCast_algebraicClosure k ℓ
  let := Fintype.ofFinite k
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure k)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure k) (ℓ ^ n))
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)).toRingEquiv
    (rootsOfUnity.mkOfPowEq ζ hζ).2
  unfold geometricFrobeniusModularCharacter
  simpa using h

variable {k ℓ} {U : Scheme.{u}}

/-- **The geometric Frobenius on the trivialized `μ_{ℓⁿ}`**: for `U` over `k̄` through `f` and
`ζ ∈ k̄` with `ζ ^ ℓⁿ = 1`, the map `ℤ ⟶ μ_{ℓⁿ}`, `a ↦ ζ ^ a`, read along the semilinear
structure `f ≫ σ`, is `c` times the one along `f`, for the value `c ∈ ℤ/ℓⁿ` of the modular
cyclotomic character of the geometric Frobenius. -/
theorem unitToRootsOfUnitySheaf_comp_specGeometricFrobenius
    (f : U ⟶ Spec (.of (AlgebraicClosure k))) (n : ℕ) {ζ : AlgebraicClosure k}
    (hζ : ζ ^ (ℓ ^ n) = 1) :
    unitToRootsOfUnitySheaf (f ≫ (specGeometricFrobenius k).asIso.hom) hζ =
      (((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val : ℤ) •
        unitToRootsOfUnitySheaf f hζ := by
  let := Fintype.ofFinite k
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  rw [specGeometricFrobenius_hom]
  have hζ' : (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k
      (AlgebraicClosure k)).toRingEquiv.toRingHom ζ ^ (ℓ ^ n) = 1 := by
    rw [← map_pow, hζ, map_one]
  have h : (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k
      (AlgebraicClosure k)).toRingEquiv.toRingHom ζ =
      ζ ^ ((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val :=
    geometricFrobeniusAlgEquivOfAlgebraic_apply_of_pow_eq_one k ℓ n hζ
  rw [unitToRootsOfUnitySheaf_comp_Spec_map _ f hζ hζ',
    unitToRootsOfUnitySheaf_congr f h hζ' (by rw [← h]; exact hζ'),
    unitToRootsOfUnitySheaf_pow f hζ]

variable {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k))

/-- **The pullback of roots of unity along the geometric Galois Frobenius, on the trivialized
`μ_{ℓⁿ}`**: on the geometric fibre `X̄` with structure morphism `a_X : X̄ ⟶ Spec k̄` and geometric
Galois Frobenius `g = 𝟙 × σ`, for `ζ ∈ k̄` with `ζ ^ ℓⁿ = 1`, the comparison `g^* μ_{ℓⁿ} ⟶ μ_{ℓⁿ}`
carries `g^*(a ↦ ζ ^ a)` to `c · (a ↦ ζ ^ a)`, through the identification `g^* ℤ ≅ ℤ` of the
units, where `c ∈ ℤ/ℓⁿ` is the value of the modular cyclotomic character of the geometric
Frobenius (`c q = 1`). -/
theorem upperStar_map_unitToRootsOfUnitySheaf_geometricGaloisFrobenius
    (n : ℕ) {ζ : AlgebraicClosure k} (hζ : ζ ^ (ℓ ^ n) = 1) :
    (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map
        (unitToRootsOfUnitySheaf a.geometricFiberToAlgebraicClosure hζ ≫
          (rootsOfUnitySheafIso a.geometricFiber (ℓ ^ n)).hom) ≫
        upperStarRootsOfUnityComparison a.geometricGaloisFrobenius.asIso.hom (ℓ ^ n) =
      η (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}] ≫
        ((((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val : ℤ) •
          unitToRootsOfUnitySheaf a.geometricFiberToAlgebraicClosure hζ) ≫
        (rootsOfUnitySheafIso a.geometricFiber (ℓ ^ n)).hom := by
  rw [upperStar_map_unitToRootsOfUnitySheaf_comp_upperStarRootsOfUnityComparison
    a.geometricGaloisFrobenius.asIso.hom a.geometricFiberToAlgebraicClosure
    (a.geometricFiberToAlgebraicClosure ≫ (specGeometricFrobenius k).asIso.hom)
    (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure a) hζ,
    unitToRootsOfUnitySheaf_comp_specGeometricFrobenius]

end FiniteField

end AlgebraicGeometry.ProEtale
