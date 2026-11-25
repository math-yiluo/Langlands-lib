/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportCube

/-!
# The base-change morphism and residue field module sheaves

Under the compatibility `ProEtale.ResidueFieldDerivedUpperStarIsoCompCoherenceAt` of
`ProEtale.residueFieldDerivedUpperStarIso` with the composition of derived pullbacks, `D(G_{Y'})`
of the base-change morphism of module objects over `𝔽_E` and the base-change morphism of
pro-étale sheaves of `𝔽_E`-modules (the exchange morphism of
`ProEtale.leftDerivedUpperStarSquareIso`, which is `ProEtale.derivedBaseChangeMap` by
`ProEtale.exchangeRight_leftDerivedUpperStarSquareIso`) are isomorphic arrows
(`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The base-change morphism and residue field module sheaves.** Assume that
`residueFieldDerivedUpperStarIso` is compatible with the composition of derived pullbacks along
`f' ≫ g` and `g' ≫ f`. Then `D(G_{Y'})` of the base-change morphism
`Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over `𝔽_E` and the base-change morphism of
pro-étale sheaves of `𝔽_E`-modules at `D(G_X) M` (which is `derivedBaseChangeMap` by
`exchangeRight_leftDerivedUpperStarSquareIso`) are isomorphic arrows. -/
theorem nonempty_arrowIso_map_exchangeRight_residueField (sq : CommSq g' f' f g)
    (H₁ : ResidueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E f' g)
    (H₂ : ResidueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E g' f)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (residueFieldRingObj X ℓ E))) :
    Nonempty (Arrow.mk ((residueFieldModuleSheaf Y' ℓ E).mapDerivedCategory.map
        ((Adjunction.exchangeRight
          (CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
          (CondensedRing.derivedUpperStarLowerStarAdjunction
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f')
          (pullbackSquareComparison
            (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) sq)).app M)) ≅
      Arrow.mk ((Adjunction.exchangeRight
        (ProEtale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)
        (ProEtale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f')
        (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) sq)).app
        ((residueFieldModuleSheaf X ℓ E).mapDerivedCategory.obj M))) := by
  have key := Adjunction.nonempty_arrowIso_map_exchangeRight_app
    (CondensedRing.derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f')
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) f')
    (pullbackSquareComparison (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) sq)
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) sq)
    (residueFieldDerivedUpperStarIso ℓ E f) (residueFieldDerivedUpperStarIso ℓ E f')
    (residueFieldDerivedUpperStarIso ℓ E g) (residueFieldDerivedUpperStarIso ℓ E g')
    ?_
    (residueFieldDerivedPushHom ℓ E f) rfl (residueFieldDerivedPushHom ℓ E f') rfl M
    inferInstance inferInstance
  -- The types differ from the goal only in instance arguments; at default transparency the
  -- unifier unfolds the morphisms of the derived categories instead (minutes).
  · with_reducible_and_instances exact key
  · with_reducible_and_instances exact residueFieldDerivedUpperStarIso_cube sq H₁ H₂

end AlgebraicGeometry.ProEtale
