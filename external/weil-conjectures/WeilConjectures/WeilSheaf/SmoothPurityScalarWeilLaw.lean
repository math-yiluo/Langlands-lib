/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarComparison
public import WeilConjectures.WeilSheaf.SmoothPurityScalarFactorSquare
import WeilConjectures.Tactic.ExactModProofs

/-! # Transport of a scalar Frobenius law with abstract coefficients -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X U : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)

variable (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (e : ((p)^*[Ab.{u + 1}].mapMod _).obj M ≅
    ((p)^*[Ab.{u + 1}].mapMod _).obj N)
  (c : ℤ)

/-- A scalar Frobenius relation descends from underlying sheaves to coefficient modules. -/
theorem purityExtendPullbackIso_factor
    (he : (s)^*[Ab.{u + 1}].map e.hom.hom ≫
        (purityAbelianFactorIso p s hs).hom.app N.X =
      c • ((purityAbelianFactorIso p s hs).hom.app M.X ≫ e.hom.hom)) :
    c • ((purityModuleFactorIso Λ p s hs).hom.app M ≫
        (purityExtendPullbackIso Λ p M N e).hom) =
      (s)^*⟦Λ⟧.map
          (purityExtendPullbackIso Λ p M N e).hom ≫
        (purityModuleFactorIso Λ p s hs).hom.app N := by
  apply purity_scalarFunctorFactorSquare (p)^*⟦Λ⟧
    (Mod.forget (condensedRingObj Λ X) ⋙ (p)^*[Ab.{u + 1}])
    (Mod.forget (condensedRingObj Λ U))
    (s)^*⟦Λ⟧ (s)^*[Ab.{u + 1}] (CondensedRing.upperStarForgetIso Λ s)
    (CondensedRing.upperStarForgetIso Λ p) (purityModuleFactorIso Λ p s hs) M N
    ((purityAbelianFactorIso p s hs).hom.app M.X)
    ((purityAbelianFactorIso p s hs).hom.app N.X)
    e.hom.hom (purityExtendPullbackIso Λ p M N e).hom c
  · exact purity_upperStarForgetIso_factor_normalized Λ p s hs M
  · exact purity_upperStarForgetIso_factor_normalized Λ p s hs N
  · exact purityExtendPullbackIso_forget Λ p M N e
  · exact he



section FiniteBase

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k))

/-- The abelian factorization attached to the geometric Frobenius. -/
noncomputable def purityAbelianFrobeniusFactorIso :
    (a.geometricFiberProj)^*[Ab.{u + 1}] ⋙
        (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}] ≅
      (a.geometricFiberProj)^*[Ab.{u + 1}] :=
  purityAbelianFactorIso a.geometricFiberProj a.geometricGaloisFrobenius.asIso.hom
    a.geometricGaloisFrobenius_hom_comp_geometricFiberProj

variable (M₀ N₀ : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀))
  (e₀ : ((a.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M₀ ≅
    ((a.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj N₀) (c₀ : ℤ)

/-- A scalar Frobenius relation descends from underlying sheaves to coefficient modules. -/
theorem purityExtendPullbackIso_weil
    (he : (a.geometricGaloisFrobenius.asIso.hom)^*[Ab.{u + 1}].map e₀.hom.hom ≫
        (purityAbelianFrobeniusFactorIso a).hom.app N₀.X =
      c₀ • ((purityAbelianFrobeniusFactorIso a).hom.app M₀.X ≫ e₀.hom.hom)) :
    c₀ • ((CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app M₀ ≫
        (purityExtendPullbackIso Λ a.geometricFiberProj M₀ N₀ e₀).hom) =
      (a.geometricGaloisFrobenius.asIso.hom)^*⟦Λ⟧.map
          (purityExtendPullbackIso Λ a.geometricFiberProj M₀ N₀ e₀).hom ≫
        (CondensedRing.geometricFiberProjUpperStarFrobeniusIso Λ a).hom.app N₀ := by
  have h := purityExtendPullbackIso_factor Λ a.geometricFiberProj
    a.geometricGaloisFrobenius.asIso.hom a.geometricGaloisFrobenius_hom_comp_geometricFiberProj
    M₀ N₀ e₀ c₀ he
  simp only [CondensedRing.geometricFiberProjUpperStarFrobeniusIso,
    purityModuleFactorIso] at h ⊢
  exact_mod_proofs h

end FiniteBase

end AlgebraicGeometry.ProEtale
