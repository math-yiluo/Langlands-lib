/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusPullbackNaturality
public import WeilConjectures.WeilSheaf.CondensedModelDescent

/-! # Frobenius on the underlying root trivialization -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The factorization isomorphism and `upperStarComp'` -/

section Factor

variable {U X : Scheme.{u}} (g₁ : U ⟶ U) (g : U ⟶ X) (h : g₁ ≫ g = g)

/-- The factorization isomorphism `g₁^* g^* ≅ g^*` along `g₁ ≫ g = g` is the inverse of the
composition isomorphism `ProEtale.upperStarComp'`. -/
lemma upperStarComp'_symm_inv_app_eq (Y : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    (ProEtale.upperStarComp' Ab.{u + 1} g₁ g g h.symm).symm.inv.app Y =
      (upperStarFactorIso g₁ g h).inv.app Y := by
  simp [ProEtale.upperStarComp', upperStarFactorIso, upperStarCongr]

end Factor

/-! ### The semilinear structure of the trivialization -/

section Frobenius

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k)) {ζ : ℕ → AlgebraicClosure k}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

instance weaklyEtale_geometricGaloisFrobenius_hom :
    WeaklyEtale a.geometricGaloisFrobenius.asIso.hom :=
  MorphismProperty.of_isIso _ _

/-- **The trivialization of the Tate module under the geometric Galois Frobenius**, on
underlying sheaves: `Fr^*` of the trivialization `p^* ℤ_ℓ(1) ≅ p^* ℤ_ℓ,X₀` followed by the
factorization `Fr^* p^* ℤ_ℓ,X₀ ≅ p^* ℤ_ℓ,X₀` is `q` times the factorization
`Fr^* p^* ℤ_ℓ(1) ≅ p^* ℤ_ℓ(1)` followed by the trivialization. -/
theorem upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom_frobenius :
    (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure ℓ hζ hζ').hom.hom ≫
      (upperStarFactorIso a.geometricGaloisFrobenius.asIso.hom a.geometricFiberProj
        a.geometricGaloisFrobenius_hom_comp_geometricFiberProj).hom.app
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X₀) =
    (Nat.card k : ℤ) •
      ((upperStarFactorIso a.geometricGaloisFrobenius.asIso.hom a.geometricFiberProj
          a.geometricGaloisFrobenius_hom_comp_geometricFiberProj).hom.app (tateModule X₀ ℓ).X ≫
        (upperStarMapModTateModuleIsoUnit a.geometricFiberProj
          a.geometricFiberToAlgebraicClosure ℓ hζ hζ').hom.hom) := by
  rw [upperStar_map_upperStarMapModTateModuleIsoUnit_hom_hom a.geometricGaloisFrobenius.asIso.hom
    a.geometricFiberProj a.geometricGaloisFrobenius_hom_comp_geometricFiberProj
    a.geometricFiberToAlgebraicClosure
    a.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure ℓ hζ hζ',
    upperStarMapModTateModuleIsoUnit_comp_specGeometricFrobenius_hom, Mod.zsmul_hom,
    Preadditive.comp_zsmul]

end Frobenius

end AlgebraicGeometry.ProEtale

