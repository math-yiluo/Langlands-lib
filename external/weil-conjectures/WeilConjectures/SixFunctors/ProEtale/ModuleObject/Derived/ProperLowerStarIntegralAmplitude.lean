/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructureTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegral

/-!
# Uniform amplitude of the proper direct image of constructible `𝒪_E`-sheaves

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`, and `p : Z ⟶ Y` a proper morphism of noetherian schemes whose geometric fibres have
dimension `≤ d`. This file proves that for every constructible `𝒪_{E,Z}`-module object `N`, the
pro-étale direct image `Rp_* N` lies in degrees `≤ 2d`
(`ProEtale.CondensedRing.isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper`,
blueprint `proposition-compactness-proper-direct-image--2` (1),
`lemma-uniform-bound-proper-direct-image--1`), given that `Rp_*` preserves `Dᵇc(-, 𝔽_E)`.

The proof reduces to the residue field: `Rp_* N` is bounded constructible, so it suffices that its
first derived reduction lies in degrees `≤ 2d`
(`ProEtale.CondensedRing.isLE_of_isLE_derivedReduction`). This reduction is `Rp_*(N ⊗ᴸ 𝔽_E)`,
where `N ⊗ᴸ 𝔽_E` is a bounded constructible complex in degrees `≤ 0`
(`ProEtale.CondensedRing.isLE_derivedReduction_singleFunctor_obj`) of étale origin. With finite
coefficients the pro-étale direct image of such a complex is `ν^*` of the étale one
(`ProEtale.isLE_rightDerivedLowerStar_of_isProper_of_boundedConstructible`), and the étale bound
follows by dévissage from the vanishing of `Rᵠp_* F` for `q > 2d` on single sheaves
(`Etale.isLE_rightDerivedLowerStar_of_isProper`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry

open Scheme

/-- For a proper morphism `f : X ⟶ S` whose geometric fibres have dimension `≤ d` and a finite
coefficient ring `Λ`, the étale direct image `Rf_*` sends bounded complexes in degrees `≤ 0` into
degrees `≤ 2d`: by dévissage from single sheaves, for which `Rᵠf_* F = 0` when `q > 2d`. -/
lemma Etale.isLE_rightDerivedLowerStar_of_isProper {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.TStructure.t.bounded L) [L.IsLE 0] :
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj L).IsLE (2 * d) := by
  have h := DerivedCategory.isLE_obj_of_isLE_of_homologyProperty
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor (2 * d) ⊤
    (fun F _ ↦ (DerivedCategory.isLE_iff _ _).2 fun q hq ↦
      Etale.isZero_homology_rightDerivedLowerStar_of_isProper f d hd F q hq)
    L hL (fun _ ↦ trivial) 0
  rwa [zero_add] at h

/-- For a proper morphism `f : X ⟶ S` whose geometric fibres have dimension `≤ d` and a finite
coefficient ring `Λ`, the pro-étale direct image `Rf_*` sends bounded constructible complexes (of
étale origin) in degrees `≤ 0` into degrees `≤ 2d`: on `ν^* L'` it is `ν^*` of the étale direct
image of `L'`. -/
lemma ProEtale.isLE_rightDerivedLowerStar_of_isProper_of_boundedConstructible
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (d : ℕ) (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hL : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L)
    (h₀ : L.IsLE 0) :
    ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj L).IsLE (2 * d) := by
  obtain ⟨L', hL', ⟨e⟩⟩ := (ProEtale.DerivedCategory.boundedConstructible_iff _ _ _).1 hL
  have : L'.IsLE 0 := ProEtale.isLE_of_isLE_mapDerivedCategory_comparisonUpperStar
    (DerivedCategory.TStructure.t.isLE_of_iso e.symm 0)
  have := Etale.isLE_rightDerivedLowerStar_of_isProper f d hd L' hL'.1
  have := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) S).isLE_mapDerivedCategory_obj
    ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj L') (2 * d)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso e.symm ≪≫
      ProEtale.rightDerivedLowerStarMapDerivedCategoryObjIso _ f L' hL'.1.1).symm _

namespace ProEtale.CondensedRing

open PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- The first derived reduction `N ⊗ᴸ 𝔽_E` of a module object `N` placed in degree `0` lies in
degrees `≤ 0`: it is the cone of the action of a uniformizer on `N`. -/
lemma isLE_derivedReduction_singleFunctor_obj {X : Scheme.{u}}
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) :
    ((derivedReduction X ℓ E).obj ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE 0 := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  have hS := shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ
  obtain ⟨g, δ, hT⟩ := Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _ hS
    ((DerivedCategory.singleFunctor _ 0).obj N)
  have h₀ : ((DerivedCategory.singleFunctor _ 0).obj N).IsLE 0 := inferInstance
  have hC := DerivedCategory.isLE_obj₃_of_isLE _ hT 0 h₀ h₀
  have hM : ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE 0 :=
    (DerivedCategory.isLE_iff _ 0).2 fun i hi ↦ Mod.isZero_of_isZero_comap _
      ((((DerivedCategory.isLE_iff _ 0).1 hC i hi)).of_iso
        (((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategoryHomologyFunctorIso
          i).app _))
  exact (residueFieldModuleSheaf X ℓ E).isLE_mapDerivedCategory_obj _ 0

variable (ℓ E) in
/-- Blueprint `proposition-compactness-proper-direct-image--2` (1),
`lemma-uniform-bound-proper-direct-image--1`: for a proper morphism `p : Z ⟶ Y` of noetherian
schemes whose geometric fibres have dimension `≤ d`, if `Rp_*` preserves `Dᵇc(-, 𝔽_E)`, then
`Rp_* N` lies in degrees `≤ 2d` for every constructible `𝒪_{E,Z}`-module object `N`. -/
theorem isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (p : Z ⟶ Y) [IsProper p] (d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback p s : Scheme.{u}) ≤ (d : WithBot ℕ∞))
    (hp : ∀ L, ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Z L →
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Y
        ((R((p)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).obj L))
    (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))
    (hN : IsConstructibleModuleObject _ N) :
    ((R((p)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE (2 * d) := by
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (integersResidueField ℓ E.1)))
  have hN₀ := boundedConstructible_singleFunctor_obj (Profinite.padicIntegersRingObj ℓ E.1) Z 0
    N hN
  refine isLE_of_isLE_derivedReduction
    (boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueField ℓ E p hp _ hN₀) _ ?_
  have e := (nonempty_derivedReduction_rightDerivedLowerStar_iso ℓ E p
    ((DerivedCategory.singleFunctor _ 0).obj N) 0).some
  have := ProEtale.isLE_rightDerivedLowerStar_of_isProper_of_boundedConstructible p d hd _
    (boundedConstructible_derivedReduction_obj Z ℓ E _ hN₀)
    (isLE_derivedReduction_singleFunctor_obj N)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm _

end ProEtale.CondensedRing

end AlgebraicGeometry
