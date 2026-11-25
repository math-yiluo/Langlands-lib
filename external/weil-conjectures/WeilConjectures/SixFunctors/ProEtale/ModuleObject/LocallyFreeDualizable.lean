/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom
public import WeilConjectures.CategoryTheory.Monoidal.DualizableDetection
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!

# Locally free module objects on the pro-étale site are dualizable

Let `X` be a scheme and `R` a commutative ring object of `Sheaf (Scheme.ProEt.topology X) Ab`.
A locally free `R`-module object `M` (`ProEtale.IsLocallyFree`) is dualizable in `Mod_R` for the
relative tensor product (`ProEtale.IsLocallyFree.isDualizable`). For the coefficient rings
`R = Λ_X` of a commutative condensed ring `Λ`, it is moreover constructible
(`ProEtale.IsLocallyFree.isConstructibleModuleObject`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeConstructible`), with respect to the
trivial stratification.

## The argument

Let `{gᵢ : Uᵢ ⟶ X}` be a pro-étale cover with `M|_{Uᵢ}` free of finite rank. The restrictions
`Φᵢ = (gᵢ^*).mapMod R : Mod_R ⥤ Mod_{gᵢ^* R}`

* are strong monoidal for the relative tensor products, `gᵢ^*` being braided and right exact
  (`Functor.monoidal_mapMod`);
* commute with internal homs (`Mod.isIso_ihomComparison_mapMod`), since `gᵢ^*` does
  (`ProEtale.isIso_ihomComparison_upperStar`, `gᵢ` being weakly étale) and is exact;
* are jointly conservative, as the restrictions of sheaves along a pro-étale cover are
  (`ProEtale.isIso_of_isIso_localizationRestriction`).

Since every `Φᵢ M ≅ (gᵢ^* R)^{nᵢ}` is dualizable (`isDualizable_biproduct_unit`), `M` is
dualizable (`isDualizable_of_isDualizable_map`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
  [IsCommMonObj R]

/-- **A locally free module object is dualizable**: if `M|_{Uᵢ}` is free of finite rank for a
pro-étale cover `{Uᵢ ⟶ X}`, then `M` is dualizable in `Mod_R`, for the relative tensor product
over `R`. Dualizability is detected by the restrictions to the `Uᵢ`, which are jointly
conservative, monoidal and commute with internal homs. -/
theorem IsLocallyFree.isDualizable {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hM : IsLocallyFree R M) : IsDualizable M := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  have (i : 𝒰.I₀) : WeaklyEtale (𝒰.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ (.mk i)
  have := fun i ↦ isIso_ihomComparison_upperStar Ab.{u + 1} (𝒰.f i)
  refine isDualizable_of_isDualizable_map (fun i ↦ (𝒰.f i)^*[Ab.{u + 1}].mapMod R) ?_
    fun i ↦ ?_
  · intro Y Z f hf
    suffices IsIso ((Mod.forget R).map f) from isIso_of_reflects_iso f (Mod.forget R)
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom 𝒰.f 𝒰.mem₀ fun i ↦ ?_
    have : IsIso ((𝒰.f i)^*[Ab.{u + 1}].map f.hom) :=
      inferInstanceAs (IsIso ((Mod.forget _).map (((𝒰.f i)^*[Ab.{u + 1}].mapMod R).map f)))
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (𝒰.f i) inferInstance) _).1 this
  · obtain ⟨n, ⟨e⟩⟩ := h𝒰 i
    exact IsDualizable.of_iso e.symm (isDualizable_biproduct_unit (C := Mod _ _) n)

end AlgebraicGeometry.ProEtale
