/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ExchangeRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.StrictLocalizationBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.SingleReduction
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus

/-!

# Exceptional pullback along a closed immersion on the strict localization

Let `M` be a strictly local model of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`) and
`ι ≫ graph = d ≫ diagonal` a cartesian square with fixed scheme `F`, so that `d : F ⟶ X` is a
closed immersion and `Y = F ×_X B` (`AlgebraicGeometry.Etale.CurveLocalModel.isPullback_τY`),
where `B ⟶ X` is the strict localization of `X` at the fixed point `y`. This file proves that
the base change map `Lτ_Y^* Rd^! N ⟶ Ry_B^! Lτ_B^* N` of the exceptional pullback
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) becomes an isomorphism after
derived global sections over `Y`, for bounded below `N`: the stalk of `Rd^! N` at `y` is the
local cohomology `RΓ_Y(B, N|_B)` on the strict localization.

In fact the base change map itself is an isomorphism
(`AlgebraicGeometry.Etale.CurveLocalModel.isIso_rightDerivedUpperShriekBaseChangeMap_app_τY`):
by the localization triangle of `d` and its open complement `j : U ⟶ X`, it suffices that the
derived base change map `τ_B^* Rj_* ⟶ Rj'_* τ_U^*` is an isomorphism on bounded below complexes
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso`). Since
`B = X ×_{X ×_k X} T` is the base change of the strict localization `T`, the map `B ⟶ X` is a
cofiltered limit of étale `X`-schemes, along which base change holds for arbitrary coefficients
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_isPullback_strictLocalization`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (M : CurveLocalModel k) {F : Scheme.{u}} {ι d : F ⟶ M.X} [IsClosedImmersion d]
  (hsq : IsPullback ι d M.graph (pullback.diagonal M.f))

instance : CompactSpace M.X :=
  QuasiCompact.compactSpace_of_compactSpace M.f

instance : QuasiSeparatedSpace M.X :=
  quasiSeparatedSpace_of_quasiSeparated M.f

instance : QuasiSeparatedSpace (pullback M.f M.f : Scheme.{u}) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst M.f M.f ≫ M.f)

omit [Finite Λ] in
/-- **Derived base change along `τ_B : B ⟶ X`.** The diagonal `B = X ×_{X ×_k X} T` of the
strictly local model is the base change of the strict localization `T` of `X ×_k X`, so for a
quasi-compact quasi-separated `g : V ⟶ X` the derived base change map
`τ_B^* R⁺g_* ⟶ R⁺g'_* τ_V^*` on bounded below complexes is an isomorphism. -/
lemma isIso_derivedBaseChangeMapPlus_τB {V : Scheme.{u}} (g : V ⟶ M.X) [QuasiCompact g]
    [QuasiSeparated g] :
    IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback g M.τB).toCommSq) :=
  isIso_derivedBaseChangeMapPlus_of_isPullback_strictLocalization Λ M.diagPoint
    (pullback.diagonal M.f) M.τB M.b M.isPullback_τB g (IsPullback.of_hasPullback g M.τB)

/-- **The exceptional pullback along `d` commutes with the pullback to the strict
localization.** For bounded below `N`, the base change map `Lτ_Y^* Rd^! N ⟶ Ry_B^! Lτ_B^* N` is
an isomorphism: with `j : U ⟶ X` the open complement of `d`, the derived base change map
`τ_B^* Rj_* ⟶ Rj'_* τ_U^*` is an isomorphism on bounded below complexes
(`AlgebraicGeometry.Etale.CurveLocalModel.isIso_derivedBaseChangeMapPlus_τB`), so
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso` applies. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_τY
    (N : DerivedCategory.Plus (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ (M.isPullback_τY hsq)).app N.obj) := by
  have : Smooth M.f := SmoothOfRelativeDimension.smooth 1 M.f
  have : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.f
  have : IsNoetherian M.X := {}
  let j := d.openComplement.ι
  have sqU := IsPullback.of_hasPullback j M.τB
  have hij : Set.range d.base = (Set.range j.base)ᶜ := d.range_eq_compl_range_openComplement_ι
  have hij' : Disjoint (Set.range M.yB.base) (Set.range (pullback.snd j M.τB).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, rfl⟩ ⟨w, hw⟩
    have h₁ : M.τB.base (M.yB.base y) ∈ Set.range d.base :=
      ⟨M.τY hsq y, by rw [← Scheme.Hom.comp_apply, M.τY_d hsq, Scheme.Hom.comp_apply]⟩
    have h₂ : M.τB.base (M.yB.base y) ∈ Set.range j.base :=
      ⟨pullback.fst j M.τB w, by rw [← hw, ← Scheme.Hom.comp_apply, pullback.condition,
        Scheme.Hom.comp_apply]⟩
    rw [hij] at h₁
    exact h₁ h₂
  obtain ⟨n, hn⟩ := N.2
  have : N.obj.IsGE n := hn
  let K : DerivedCategory.Plus (Sheaf (d.openComplement : M.X.Opens).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) :=
    ⟨(L((j)^*[ModuleCat.{u + 1} Λ])).obj N.obj, n, isGE_leftDerivedUpperStar_obj _ j N.obj n⟩
  have := M.isIso_derivedBaseChangeMapPlus_τB Λ j
  exact isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso Λ (M.isPullback_τY hsq) sqU hij
    hij' N.obj ((isIso_derivedBaseChangeMap_app_ι_obj_iff _ sqU.toCommSq K).2 inferInstance)

/-- **Stalks of the exceptional pullback on the strict localization**: for bounded below `N`, the
base change map `Lτ_Y^* Rd^! N ⟶ Ry_B^! Lτ_B^* N` induces an isomorphism on derived global
sections over `Y = F ×_X B`. -/
theorem isIso_rightDerivedGlobalSections_map_rightDerivedUpperShriekBaseChangeMap
    (N : DerivedCategory.Plus (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y).map
      ((rightDerivedUpperShriekBaseChangeMap Λ (M.isPullback_τY hsq)).app N.obj)) := by
  have := M.isIso_rightDerivedUpperShriekBaseChangeMap_app_τY Λ hsq N
  infer_instance

end AlgebraicGeometry.Etale.CurveLocalModel
