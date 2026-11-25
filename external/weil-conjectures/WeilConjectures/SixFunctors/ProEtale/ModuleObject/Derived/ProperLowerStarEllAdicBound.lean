/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!
# A uniform bound for the proper direct image of constructible `ℓ`-adic sheaves

Let `p : Z ⟶ Y` be a proper morphism to a `k`-scheme of finite type, `ℓ` invertible in `k`, and
`d` a bound for the dimensions of the geometric fibres of `p`. For the `ℓ`-adic coefficient rings
`Λ = 𝒪_E, E, ℚ̄_ℓ` (`E ⊆ ℚ̄_ℓ` a finite subextension), `Rp_*` sends every constructible
`Λ_Z`-module, placed in degree `0`, into degrees `≤ 2d`, with `d` independent of `E` (blueprints
`lemma-uniform-bound-proper-direct-image--1`):

* `exists_isLE_rightDerivedLowerStar_singleFunctor_padicIntegers`: for `𝒪_E`, from
  `isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper` (reduction modulo a
  uniformizer and the torsion bound `2d`);
* `exists_isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj`: for `E`, a constructible
  `E`-module `N` being `E ⊗ᴸ K₀` for a bounded constructible `𝒪_E`-complex `K₀`
  (`isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars`);
* `exists_isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj`: for `ℚ̄_ℓ`, in the same way
  from a finite subextension `E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  (p : Z ⟶ Y) [IsProper p]

/-! ### The uniform bound on constructible sheaves -/

include aY in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1`, integral form: there is `d` such that
for every finite subextension `E ⊆ ℚ̄_ℓ`, `Rp_*` sends the constructible `𝒪_E`-modules into degrees
`≤ 2d`. -/
lemma exists_isLE_rightDerivedLowerStar_singleFunctor_padicIntegers :
    ∃ d : ℕ, ∀ (E : FiniteIntermediateField ℓ)
      (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)),
      IsConstructibleModuleObject _ N →
        ((R((p)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * d : ℕ) := by
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_pullback_le aY p
  refine ⟨d, fun E N hN ↦ ?_⟩
  have := isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper ℓ E p d
    (fun Ω _ _ s ↦ hd Ω s) (residueFieldFiniteness_of_isNoetherian ℓ p aY E) N hN
  exact_mod_cast this

include aY in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1` for the finite subextensions `E ⊆ ℚ̄_ℓ`:
there is `d` such that `Rp_*` sends the constructible `E`-modules into degrees `≤ d`, for every
`E`. -/
lemma exists_isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj :
    ∃ d : ℤ, ∀ (E : FiniteIntermediateField ℓ)
      (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.1) Z)),
      IsConstructibleModuleObject _ N →
        ((R((p)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (p ≫ aY)
  obtain ⟨d, hd⟩ := exists_isLE_rightDerivedLowerStar_singleFunctor_padicIntegers ℓ aY p
  refine ⟨(2 * d : ℕ), fun E N hN ↦ ?_⟩
  obtain ⟨K₀, ⟨e⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso Z ℓ E
    ⟨_, boundedConstructible_singleFunctor_obj _ Z 0 N hN⟩
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)) :=
    preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield ℓ E X
  exact isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars
    (padicIntegersRingObjToContinuousMapRingObj ℓ E) p _
    (fun K n _ ↦ isIso_derivedPushHom_app_padicIntegers_of_isGE ℓ E p K n) (hd E) K₀.obj
    K₀.property ((boundedConstructible _).ι.mapIso e)

include aY in
/-- Blueprint `lemma-uniform-bound-proper-direct-image--1` for `ℚ̄_ℓ`: there is `d` such that `Rp_*`
sends the constructible `ℚ̄_ℓ`-modules into degrees `≤ d`. -/
lemma exists_isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj :
    ∃ d : ℤ, ∀ (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      IsConstructibleModuleObject _ N →
        ((R((p)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType (p ≫ aY)
  obtain ⟨d, hd⟩ := exists_isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj ℓ aY p
  refine ⟨d, fun N hN ↦ ?_⟩
  obtain ⟨E, K_E, ⟨e⟩⟩ := constructibleCocone_essSurjObj Z ℓ
    ⟨_, boundedConstructible_singleFunctor_obj _ Z 0 N hN⟩
  have (X : Scheme.{u}) : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)) :=
    preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ X E
  exact isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars
    (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) p _
    (fun K n _ ↦ isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E p K n)
    (hd E) K_E.obj K_E.property ((boundedConstructible _).ι.mapIso e)

end AlgebraicGeometry.ProEtale.CondensedRing
