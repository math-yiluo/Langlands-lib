/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ProjectiveTensorUnitCover
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComapQuotient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionRestrictConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar

/-!
# Restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` preserves constructibility

Let `E ⊆ ℚ̄_ℓ` with ring of integers `𝒪_E`, `n : ℕ` and `X` a scheme. This file proves that the
restriction of scalars along the reduction `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` sends constructible
`𝒪_E ⧸ ℓⁿ`-modules to constructible `𝒪_E`-modules
(`ProEtale.CondensedRing.isConstructibleModuleObject_comap_integersModPowReduction`), hence
bounded constructible complexes to bounded constructible complexes
(`ProEtale.CondensedRing.restrictScalarsIntegersModPowBoundedConstructible`).

* Every scheme has a pro-étale cover by spectra of w-contractible rings, indexed by a type in the
  universe of the scheme (`AlgebraicGeometry.Scheme.exists_cover_projective_tensorUnit`), over
  which the unit of abelian sheaves is projective
  (`AlgebraicGeometry.ProEtale.projective_tensorUnit_of_isWContractibleRing`).
* Over such a member, a finitely presented `𝒪_E ⧸ ℓⁿ`-module is a finitely presented
  `𝒪_E`-module (`CategoryTheory.Mod.IsFinitelyPresented.comap_of_shortExact`), the reduction
  `0 ⟶ 𝒪_E --ℓⁿ--> 𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ ⟶ 0` being short exact
  (`ProEtale.shortExact_integersModPowReduction`); restriction of scalars commutes with the
  pullbacks (`ProEtale.CondensedRing.comapUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ)

/-- Restriction of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` preserves pro-étale locally finitely
presented module objects: refine the cover by spectra of w-contractible rings, over which the
unit is projective, so that finitely presented `𝒪_E ⧸ ℓⁿ`-modules are finitely presented
`𝒪_E`-modules. -/
lemma isLocallyFinitelyPresented_comap_integersModPowReduction {X : Scheme.{u}}
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)}
    (hN : IsLocallyFinitelyPresented (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)
      N) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((Mod.comap (integersModPowReduction X ℓ E n)).obj N) := by
  obtain ⟨𝒰, h𝒰⟩ := hN
  choose 𝒱 h𝒱 using fun i ↦ exists_cover_projective_tensorUnit (𝒰.X i)
  refine ⟨𝒰.bind 𝒱, fun i ↦ ?_⟩
  have := h𝒱 i.1 i.2
  refine (isFinitelyPresented_mapMod_iff _ ((𝒱 i.1).f i.2 ≫ 𝒰.f i.1) _).2 ?_
  have h₁ := IsFinitelyPresented.upperStar _ ((𝒱 i.1).f i.2)
    ((isFinitelyPresented_mapMod_iff _ _ _).1 (h𝒰 i.1))
  have h₂ := h₁.of_iso ((upperStarComp _ ((𝒱 i.1).f i.2) (𝒰.f i.1)).app N).symm
  have h₃ := Mod.IsFinitelyPresented.comap_of_shortExact _ _
    (shortExact_integersModPowReduction ((𝒱 i.1).X i.2) ℓ E n) h₂
  exact h₃.of_iso ((comapUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
    ((𝒱 i.1).f i.2 ≫ 𝒰.f i.1)).app N)

/-- Restriction of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X` preserves constructible module
objects: it commutes with the pullbacks to the strata of a stratification. -/
lemma isConstructibleModuleObject_comap_integersModPowReduction {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)}
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) M) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
      ((Mod.comap (integersModPowReduction X ℓ E n)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ (isLocallyFinitelyPresented_mapMod_iff _ _ _).2 ?_⟩
  exact IsLocallyFinitelyPresented.of_iso
    ((comapUpperStarIso (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n)
      (S.immersion a)).app M)
    (isLocallyFinitelyPresented_comap_integersModPowReduction ℓ E n
      ((isLocallyFinitelyPresented_mapMod_iff _ _ _).1 (hS a)))

variable (X : Scheme.{u})

/-- **Restriction of scalars along `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` preserves bounded constructible
complexes** on every scheme `X`: it is exact, hence preserves boundedness and commutes with the
cohomology sheaves, and it preserves constructible module objects. -/
theorem restrictScalarsIntegersModPowBoundedConstructible :
    RestrictScalarsIntegersModPowBoundedConstructible ℓ E n X := fun M hM ↦
  ⟨Functor.bounded_mapDerivedCategory_obj _ hM.1, fun i ↦
    IsConstructibleModuleObject.of_iso
      (((Mod.comap (integersModPowReduction X ℓ E n)).mapDerivedCategoryHomologyFunctorIso
        i).app M)
      (isConstructibleModuleObject_comap_integersModPowReduction ℓ E n (hM.2 i))⟩

end ProEtale.CondensedRing

end AlgebraicGeometry
