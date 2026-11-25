/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux

/-!
# Lisse `𝒪_E`-sheaves are locally constant

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and uniformizer
`ϖ`. On a scheme `Z` with noetherian underlying space, a pro-étale locally finitely presented
module object `M` over `𝒪_{E,Z}` (a lisse `𝒪_E`-sheaf) is pro-étale locally isomorphic to a
constant finitely generated module `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r`
(`ProEtale.exists_cover_iso_integralConstant`; Bhatt–Scholze, *The pro-étale topology for
schemes*, Section 6.8).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The constant module object `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` over `𝒪_{E,V}`. -/
noncomputable def integralConstantModule (V : Scheme.{u}) (ϖ : PadicAlgCl.integers ℓ E) (k r : ℕ)
    (e : Fin k → ℕ) :
    Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) V) :=
  (⨁ fun j ↦ cokernel (padicIntegersRegularEndOfAlgebra V ℓ E (ϖ ^ e j))) ⊞ Mod.finiteFree _ r

/-- **Lisse `𝒪_E`-sheaves are locally constant**: on a scheme with noetherian underlying space, a
pro-étale locally finitely presented module object over `𝒪_{E,Z}` is, on the members of some
pro-étale cover, isomorphic to a constant module `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r`. -/
theorem exists_cover_iso_integralConstantModule (Z : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Z]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Z) M)
    (ϖ : PadicAlgCl.integers ℓ E)
    (hϖ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E) = Ideal.span {ϖ}) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z, ∀ i, ∃ (k r : ℕ) (e : Fin k → ℕ),
      Nonempty ((𝒰.f i)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj M ≅
        integralConstantModule ℓ E (𝒰.X i) ϖ k r e) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have hϖ0 : ϖ ≠ 0 := fun h ↦ PadicAlgCl.maximalIdeal_integers_ne_bot ℓ E (by
    rw [hϖ, h, Ideal.span_singleton_eq_bot])
  -- Transport the result for the integral coefficient ring `integralCoeff ℓ E`, which agrees
  -- with `𝒪̲_E` for the normed field structure restricted from `ℚ̄_ℓ`.
  exact LfpLocallyConstModule.of_eq (Λ₂ := Profinite.padicIntegersRingObj ℓ E)
    (σ₂ := fun n ↦ (Profinite.continuousMapConstRingHom.{u} (PadicAlgCl.integers ℓ E)
      (ϖ ^ n)).hom) rfl HEq.rfl HEq.rfl
    (lfpLocallyConstModule_integralCoeff ℓ E ϖ
      (PadicAlgCl.exists_norm_eq_pow_of_maximalIdeal_eq_span ℓ E ϖ hϖ)
      fun h ↦ hϖ0 (Subtype.ext h)) Z M hM

omit [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] in
/-- The pullback of a constant module `⊕ⱼ 𝒪_E/ϖ^{eⱼ} ⊕ 𝒪_E^r` is the constant module. -/
theorem nonempty_upperStar_integralConstantModule_iso {W V : Scheme.{u}} (g : W ⟶ V)
    (ϖ : PadicAlgCl.integers ℓ E) (k r : ℕ) (e : Fin k → ℕ) :
    Nonempty ((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧.obj (integralConstantModule ℓ E V ϖ k r e) ≅
      integralConstantModule ℓ E W ϖ k r e) :=
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  ⟨upperStarConstModuleIso (Profinite.padicIntegersRingObj ℓ E) g
    (fun j ↦ (Profinite.continuousMapConstRingHom.{u} (PadicAlgCl.integers ℓ E) (ϖ ^ e j)).hom) r⟩

end AlgebraicGeometry.ProEtale
