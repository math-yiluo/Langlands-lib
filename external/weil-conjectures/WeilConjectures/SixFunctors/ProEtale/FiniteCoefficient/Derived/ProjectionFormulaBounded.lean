/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-!
# The projection formula for a bounded second argument

Let `Λ` be a finite ring, `g : Z ⟶ Y` a proper morphism and `j : U ⟶ Z` an open immersion. For
`K` in `Dᵇctf(U_proét, Λ)` and `L` a bounded complex of étale origin on `Y` (not necessarily of
finite Tor amplitude), the projection map `Rg_*(j_! K) ⊗ᴸ L ⟶ Rg_*(j_! K ⊗ᴸ Lg^* L)` is an
isomorphism. As in `AlgebraicGeometry.ProEtale.hasProjectionFormulaOfCompactification_of_comparison`
this is the étale projection formula transported along `ν^*`; the boundedness of
`j_! K ⊗ᴸ Lg^* L` now comes from the finite Tor amplitude of `K` rather than of `L`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Coefficients

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Extension by zero along an open immersion `j : U ⟶ X` preserves Tor amplitude in `[a, b]`
on the pro-étale site: `j_!K ⊗ᴸ F ≅ j_!(K ⊗ᴸ j^*F)` by the projection formula, and `j_!` and
`j^*` are exact. -/
lemma torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek
    [ProEtale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) A)}
    (hK : DerivedCategory.torAmplitudeIn A U a b K) :
    DerivedCategory.torAmplitudeIn A X a b (D((j)_!open[A]).obj K) := fun G ↦ by
  let F := (j)_!open[A]
  -- `j_!K ⊗ᴸ G ≅ j_!(K ⊗ᴸ j^*G)`
  have e := (((derivedOpenImmersionLowerShriekProjectionIso A j).app K).app
    ((_root_.DerivedCategory.singleFunctor _ 0).obj G)).symm ≪≫
    F.mapDerivedCategory.mapIso (((-⊗ᴸ-(U)[A]).obj K).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso A j).app G))
  obtain ⟨h₁, h₂⟩ := F.homologyConcentratedIn_mapDerivedCategory_obj (hK ((j)^*[A].obj G))
  have : _root_.DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
      (((-⊗ᴸ-(U)[A]).obj K).obj (((j)^*[A] ⋙
        _root_.DerivedCategory.singleFunctor _ 0).obj G))) a := h₁
  have : _root_.DerivedCategory.TStructure.t.IsLE (F.mapDerivedCategory.obj
      (((-⊗ᴸ-(U)[A]).obj K).obj (((j)^*[A] ⋙
        _root_.DerivedCategory.singleFunctor _ 0).obj G))) b := h₂
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- Let `g : Z ⟶ Y`, let `M₀` and `L₀` be complexes of étale sheaves on `Z` and `Y` whose
pro-étale realizations `N ≅ ν^* M₀` and `L ≅ ν^* L₀` are respectively of finite Tor amplitude
and bounded. Then `M₀ ⊗ᴸ Lg^* L₀` is bounded below: its pro-étale realization is
`N ⊗ᴸ Lg^* L`, which is bounded since `N` has finite Tor amplitude and `Lg^* L` is bounded.
This is the variant of
`AlgebraicGeometry.ProEtale.plus_derivedTensor_leftDerivedUpperStar_of_comparison` with the
roles of the boundedness and of the Tor amplitude exchanged. -/
lemma plus_derivedTensor_leftDerivedUpperStar_of_comparison_of_torAmplitudeIn
    [Etale.UpperStarPreservesFlat A] [∀ X : Scheme.{u}, (ν^*(X)[A]).PreservesFlat]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    {M₀ : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)}
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)}
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (eM : N ≅ L(ν^*(Z)[A]).obj M₀) (eL : L ≅ L(ν^*(Y)[A]).obj L₀) {a b : ℤ}
    (hN : DerivedCategory.torAmplitudeIn A Z a b N)
    (hL : _root_.DerivedCategory.TStructure.t.bounded L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀)) := by
  let P := (L(ProEtale.upperStar A g)).obj L
  have hP : _root_.DerivedCategory.TStructure.t.bounded P :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory A g).app L).symm
      ((ProEtale.upperStar A g).bounded_mapDerivedCategory_obj hL)
  obtain ⟨p, q, hPpq⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded P).2 hP
  have hNP := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hN hPpq
  let e : D(ν^*(Z)[A]).obj
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀)) ≅ N ⊗ P :=
    ((ν^*(Z)[A]).leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
      asIso (((ν^*(Z)[A]).leftDerivedTensorComparison.app M₀).app _) ≪≫
      tensorIso eM.symm (((leftDerivedComparisonUpperStarCompUpperStarIso A g).app L₀).symm ≪≫
        (L(ProEtale.upperStar A g)).mapIso eL.symm)
  have hb : _root_.DerivedCategory.TStructure.t.bounded (D(ν^*(Z)[A]).obj
      (((Etale.derivedTensor A Z).obj M₀).obj ((L(Etale.upperStar A g)).obj L₀))) :=
    _root_.DerivedCategory.TStructure.t.bounded.prop_of_iso e.symm
      ((_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1 ⟨_, _, hNP⟩)
  exact ((ν^*(Z)[A]).bounded_of_bounded_mapDerivedCategory_obj hb).1

end Coefficients

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The projection formula for a bounded second argument.** For a finite ring `Λ`, a proper
`g : Z ⟶ Y`, an open immersion `j : U ⟶ Z`, `K` in `Dᵇctf(U_proét, Λ)` and `L₀` a bounded complex
of étale sheaves on `Y`, the projection map `Rg_*(j_! K) ⊗ᴸ ν^* L₀ ⟶ Rg_*(j_! K ⊗ᴸ Lg^* ν^* L₀)` is
an isomorphism. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_bounded {Y Z U : Scheme.{u}}
    (g : Z ⟶ Y) [IsProper g] (j : U ⟶ Z) [IsOpenImmersion j]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) U K)
    {L₀ : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL₀ : _root_.DerivedCategory.TStructure.t.bounded L₀) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g).app
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K)).app (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj L₀)) := by
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK.1
  obtain ⟨a, b, hKt⟩ := hK.2
  let M₀ := D(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj K₀
  have hM₀ : _root_.DerivedCategory.TStructure.t.plus M₀ :=
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).bounded_mapDerivedCategory_obj
      hK₀.1).1
  -- `j_! K ≅ ν^* M₀` and `ν^* L₀ ≅ Lν^* L₀`
  let eM : D((j)_!open[ModuleCat.{u + 1} Λ]).obj K ≅ L(ν^*(Z)[ModuleCat.{u + 1} Λ]).obj M₀ :=
    D((j)_!open[ModuleCat.{u + 1} Λ]).mapIso eK.symm ≪≫
      (Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).symm ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).app K₀ ≪≫
      ((ν^*(Z)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.app M₀).symm
  let eL := ((ν^*(Y)[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory.app L₀).symm
  -- `j_! K₀ ⊗ᴸ Lg^* L₀` is bounded below, since its pro-étale realization `j_! K ⊗ᴸ Lg^* L` is
  have hML := plus_derivedTensor_leftDerivedUpperStar_of_comparison_of_torAmplitudeIn g eM eL
    (torAmplitudeIn_mapDerivedCategory_openImmersionLowerShriek j hKt)
    ((ν^*(Y)[ModuleCat.{u + 1} Λ]).bounded_mapDerivedCategory_obj hL₀)
  -- the étale projection formula for the proper `g`
  have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite Λ g
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_leftDerived (ModuleCat.{u + 1} Λ) g
    M₀ L₀ hM₀ hML
  exact NatTrans.isIso_app_app_of_iso
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) g) eM.symm eL.symm

end AlgebraicGeometry.ProEtale
