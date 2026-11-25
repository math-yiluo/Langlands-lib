/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.IndHeart
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!
# The ind-constructible heart

Blueprint `proposition-ind-constructible-sheaves` (2): if the constructible sheaves of `R`-modules
on `X_proét` are closed under kernels, cokernels and extensions, and morphisms out of a
constructible sheaf `C` into `B[n]`, `B = colim Bᵢ` a filtered colimit of sheaves, factor through
some `Bᵢ[n]` (`AlgebraicGeometry.ProEtale.HasConstructibleExtContinuity`), then the
ind-constructible sheaves are closed under kernels, cokernels, extensions and direct sums
(`AlgebraicGeometry.ProEtale.isIndConstructibleHeart_of_hasConstructibleExtContinuity`). This is
the abstract statement
`CategoryTheory.ObjectProperty.isClosedUnder_ind_of_homFactorsThroughFilteredColimits`.

We also record that, on a topologically noetherian scheme, the constructible sheaves are closed
under kernels, cokernels and extensions for the coefficient rings `E`, `𝒪_E` and `ℚ̄_ℓ`
(`AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_serre_continuousMapRingObj`,
`AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_serre_padicIntegersRingObj`,
`AlgebraicGeometry.ProEtale.CondensedRing.isConstructibleModuleObject_serre_padicAlgClRingObj`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]

/-- Blueprint `proposition-ind-constructible-sheaves` (2): if the constructible sheaves of
`R`-modules are closed under kernels, cokernels and extensions, and morphisms out of constructible
sheaves commute with filtered colimits (`HasConstructibleExtContinuity`), the ind-constructible
sheaves are closed under kernels, cokernels, extensions and direct sums. -/
theorem isIndConstructibleHeart_of_hasConstructibleExtContinuity
    (hK : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R))
    (hC : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R))
    (hE : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R))
    (h : HasConstructibleExtContinuity R) : IsIndConstructibleHeart R := by
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, isConstructibleModuleObject_of_isZero R (isZero_zero _)⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    ObjectProperty.isClosedUnder_ind_of_homFactorsThroughFilteredColimits.{u + 1} h
  exact ⟨h₁, h₂, h₃, h₄⟩

end

namespace CondensedRing

/-- Closure of the constructible module objects under (chosen) kernels, cokernels and
extensions, as `ObjectProperty` closure properties. -/
lemma isConstructibleModuleObject_serre_of_forall {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (hk : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (f : M ⟶ N), IsConstructibleModuleObject R M →
      IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧
      IsConstructibleModuleObject R (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) ∧
      ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) ∧
      ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := by
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨he _⟩⟩
  · rintro _ ⟨f, s, hs, hf⟩
    exact _root_.constructible_of_iso (R := R) (limit.isoLimitCone ⟨s, hs⟩)
      (hk _ _ f hf.1 hf.2).1
  · rintro _ ⟨f, s, hs, hf⟩
    exact _root_.constructible_of_iso (R := R) (colimit.isoColimitCocone ⟨s, hs⟩)
      (hk _ _ f hf.1 hf.2).2

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

-- The prime `ℓ` of `E̲` occurs only in the instance `NormedAlgebra ℚ_[ℓ] E`; it is found from the
-- local instance `Fact ℓ.Prime`, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
/-- For a finite extension `E` of `ℚ_ℓ` and a topologically noetherian scheme `X`, the
constructible `E`-sheaves are closed under kernels, cokernels and extensions. -/
lemma isConstructibleModuleObject_serre_continuousMapRingObj (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)) :=
  have h := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.continuousMapRingObj E) (continuous_lf ℓ E) X
  isConstructibleModuleObject_serre_of_forall _ h.1 h.2

/-- For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a topologically noetherian scheme `X`, the
constructible `𝒪_E`-sheaves are closed under kernels, cokernels and extensions. -/
lemma isConstructibleModuleObject_serre_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact integralConstructible_serre ℓ E X

/-- For a topologically noetherian scheme `X`, the constructible `ℚ̄_ℓ`-sheaves are closed under
kernels, cokernels and extensions. -/
lemma isConstructibleModuleObject_serre_padicAlgClRingObj :
    ObjectProperty.IsClosedUnderKernels
        (IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X)) :=
  have h := isConstructibleModuleObject_serre_padicAlgCl X ℓ
  isConstructibleModuleObject_serre_of_forall _ h.1 h.2

end CondensedRing

end AlgebraicGeometry.ProEtale
