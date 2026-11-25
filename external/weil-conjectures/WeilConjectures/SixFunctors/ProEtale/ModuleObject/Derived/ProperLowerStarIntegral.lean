/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama

/-!
# Finiteness of `Rf_*` with integral coefficients from the residue field case

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E` and residue field
`𝔽_E`. This file reduces statements about the derived pushforward `Rf_*` with coefficients `𝒪_E`
to the residue field `𝔽_E`, as in the proof of blueprint
`proposition-proper-direct-image-constructible-complexes` (1).

## Main results

* `ProEtale.CondensedRing.nonempty_derivedReduction_rightDerivedLowerStar_iso`: the first derived
  reduction commutes with `Rf_*` on bounded below complexes. It is the composite of the
  comparison (Push) `𝔽_E ⊗ᴸ Rf_* K ⟶ Rf_*(𝔽_E ⊗ᴸ K)`
  (`isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`) and of the transport along
  residue field module sheaves (`ProEtale.isIso_residueFieldDerivedPushHom`).
* `ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueField`:
  between noetherian schemes, if `Rp_*` preserves `Dᵇc(-, 𝔽_E)`, it preserves `Dᵇc(-, 𝒪_E)`. The
  pushforward of a bounded constructible complex is derived complete with bounded constructible
  first derived reduction, hence bounded constructible by the integral criterion
  (`ProEtale.boundedConstructible_of_derivedCompleteIntegers`).
* `ProEtale.CondensedRing.isLE_of_isLE_derivedReduction`: a bounded constructible
  `𝒪_E`-complex whose first derived reduction lies in degrees `≤ c` lies in degrees `≤ c`. For
  `q > c`, the reduction triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` shows that `ϖ` acts surjectively
  on the constructible sheaf `Hᵠ(K)`, which therefore vanishes by Nakayama's lemma
  (`ProEtale.isZero_of_isConstructibleModuleObject_of_isZero_extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace CategoryTheory

/-- A functor which preserves zero morphisms and reflects isomorphisms reflects zero objects. -/
lemma Functor.isZero_of_isZero_map {C D : Type*} [Category* C]
    [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
    (G : C ⥤ D) [G.PreservesZeroMorphisms] [G.ReflectsIsomorphisms] {A : C}
    (h : IsZero (G.obj A)) : IsZero A := by
  have : IsIso (G.map (0 : A ⟶ 0)) :=
    isIso_of_source_target_iso_zero _ h.isoZero (G.map_isZero (isZero_zero _)).isoZero
  have := isIso_of_reflects_iso (0 : A ⟶ 0) G
  exact (isZero_zero _).of_iso (asIso (0 : A ⟶ 0))

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- **The first derived reduction commutes with the derived pushforward** on bounded below
complexes (blueprint `proposition-proper-direct-image-constructible-complexes` (1)): for every
morphism of schemes `f : X ⟶ Y` and every bounded below `K ∈ D(𝒪_{E,X})`,
`(Rf_* K) ⊗ᴸ 𝔽_E ≅ Rf_*(K ⊗ᴸ 𝔽_E)`. -/
theorem nonempty_derivedReduction_rightDerivedLowerStar_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (n : ℤ) [K.IsGE n] :
    Nonempty ((derivedReduction Y ℓ E).obj
        ((R((f)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) ≅
      (R((f)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).obj
        ((derivedReduction X ℓ E).obj K)) := by
  have h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom
      (Profinite.padicIntegersRingObjToResidueField ℓ E.1) f).app K) :=
    isIso_derivedUpperStarExtendScalarsPushHom_residueField_app ℓ E f K n
  exact ⟨(residueFieldModuleSheaf Y ℓ E).mapDerivedCategory.mapIso (asIso
      ((derivedUpperStarExtendScalarsPushHom
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) f).app K)) ≪≫
    asIso ((residueFieldDerivedPushHom ℓ E f).app
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))⟩

/-- Blueprint `proposition-proper-direct-image-constructible-complexes` (1), given the finite
coefficient case: for a morphism `p : Z ⟶ Y` of noetherian schemes, if `Rp_*` preserves
`Dᵇc(-, 𝔽_E)`, it preserves `Dᵇc(-, 𝒪_E)`. Indeed `Rp_* K` is derived complete, and its first
derived reduction is `Rp_*(K ⊗ᴸ 𝔽_E)`, which is bounded constructible. -/
theorem boundedConstructible_rightDerivedLowerStar_padicIntegers_of_residueField
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (p : Z ⟶ Y)
    (hp : ∀ L, ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Z L →
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) Y
        ((R((p)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).obj L))
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)
      ((R((p)_*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K) := by
  have : K.IsGE hK.1.1.choose := hK.1.1.choose_spec
  have e := (nonempty_derivedReduction_rightDerivedLowerStar_iso ℓ E p K hK.1.1.choose).some
  refine ProEtale.boundedConstructible_of_derivedCompleteIntegers
    (derivedCompleteIntegers_rightDerivedLowerStar_obj p
      (derivedCompleteIntegers_of_boundedConstructible hK)) ?_
  exact ObjectProperty.prop_of_iso _ e.symm
    (hp _ (boundedConstructible_derivedReduction_obj Z ℓ E K hK))

variable {ℓ E}

/-- **Amplitude from the reduction**: on a noetherian scheme, a bounded constructible
`𝒪_E`-complex `K` whose first derived reduction lies in degrees `≤ c` lies in degrees `≤ c`. For
`q > c` the reduction triangle `K --ϖ--> K ⟶ K ⊗ᴸ 𝔽_E ⟶ K[1]` shows that `ϖ` is surjective on
the constructible sheaf `Hᵠ(K)`, so that its reduction vanishes, and `Hᵠ(K) = 0` by Nakayama's
lemma. -/
theorem isLE_of_isLE_derivedReduction {X : Scheme.{u}} [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K)
    (c : ℤ) (h : ((derivedReduction X ℓ E).obj K).IsLE c) : K.IsLE c := by
  obtain ⟨ϖ, hϖ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.1
  rw [Ideal.submodule_span_eq] at hϖ
  have hS := shortExact_padicIntegersRegularEnd X ℓ E ϖ hϖ
  obtain ⟨g, δ, hT⟩ := Mod.exists_distinguished_regularEndCenter_derivedExtendScalars _ hS K
  rw [DerivedCategory.isLE_iff]
  intro q hq
  have hred : IsZero ((residueFieldModuleSheaf X ℓ E).obj ((DerivedCategory.homologyFunctor _ q).obj
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))) :=
    (((DerivedCategory.isLE_iff _ c).1 h q hq).of_iso
      (((residueFieldModuleSheaf X ℓ E).mapDerivedCategoryHomologyFunctorIso q).app _))
  have h₁ : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategory.obj
        ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).leftDerivedFunctor.obj K))) :=
    ((Mod.comap (padicIntegersToResidueField X ℓ E)).map_isZero
      ((residueFieldModuleSheaf X ℓ E).isZero_of_isZero_map hred)).of_iso
      (((Mod.comap (padicIntegersToResidueField X ℓ E)).mapDerivedCategoryHomologyFunctorIso
        q).app _).symm
  have hex := (DerivedCategory.homologyFunctor _ q).map_distinguished_exact _ hT
  have hepi : Epi ((DerivedCategory.homologyFunctor _ q).map
      ((padicIntegersCenter X ℓ E ϖ).derivedCategory.app K)) :=
    hex.epi_f (h₁.eq_of_tgt _ _)
  rw [CatCenter.homologyFunctor_map_derivedCategory_app, Mod.regularEndCenter_app] at hepi
  obtain ⟨-, hu⟩ := Mod.exact_regularEndSMul_extendUnit _ hS
    ((DerivedCategory.homologyFunctor _ q).obj K)
  have h₀ : Mod.extendUnit (padicIntegersToResidueField X ℓ E)
      ((DerivedCategory.homologyFunctor _ q).obj K) = 0 := by
    rw [← cancel_epi (Mod.regularEndSMul (padicIntegersRegularEndOfAlgebra X ℓ E.1 ϖ)
      ((DerivedCategory.homologyFunctor _ q).obj K)), comp_zero]
    exact Mod.regularEndSMul_comp_extendUnit (padicIntegersRegularEnd_hom_comp_residueField X ℓ E ϖ
      (hϖ ▸ Ideal.mem_span_singleton_self ϖ)) _
  rw [h₀] at hu
  have hz : IsZero ((Mod.comap (padicIntegersToResidueField X ℓ E)).obj
      ((Mod.extendScalars (padicIntegersToResidueField X ℓ E)).obj
        ((DerivedCategory.homologyFunctor _ q).obj K))) :=
    IsZero.of_epi_zero ((DerivedCategory.homologyFunctor _ q).obj K) _
  exact isZero_of_isConstructibleModuleObject_of_isZero_extendScalars ℓ E _
    (((mem_boundedConstructible_iff _ _).1 hK).2 q) (Mod.isZero_of_isZero_comap _ hz)

end AlgebraicGeometry.ProEtale.CondensedRing
