/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportBaseChangeIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportCoherence

/-!
# The exchange morphism and residue field module sheaves, unconditionally

`D(G_{Y'})` of the base-change morphism of module objects over `𝔽_E` and the exchange morphism
of `ProEtale.leftDerivedUpperStarSquareIso` for pro-étale sheaves of `𝔽_E`-modules at `D(G_X) M`
are isomorphic arrows
(`ProEtale.nonempty_arrowIso_map_exchangeRight_residueField_of_commSq`):
this is `ProEtale.nonempty_arrowIso_map_exchangeRight_residueField`, whose coherence hypotheses
hold by `ProEtale.residueFieldDerivedUpperStarIsoCompCoherenceAt`.
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

/-- **The base-change morphism and residue field module sheaves.** `D(G_{Y'})` of the
base-change morphism `Lg^* Rf_* M ⟶ Rf'_* Lg'^* M` of module objects over `𝔽_E` and the
exchange morphism of `leftDerivedUpperStarSquareIso` for pro-étale sheaves of `𝔽_E`-modules at
`D(G_X) M` are isomorphic arrows. -/
theorem nonempty_arrowIso_map_exchangeRight_residueField_of_commSq (sq : CommSq g' f' f g)
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
        ((residueFieldModuleSheaf X ℓ E).mapDerivedCategory.obj M))) :=
  nonempty_arrowIso_map_exchangeRight_residueField sq
    (residueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E f' g)
    (residueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E g' f) M

end AlgebraicGeometry.ProEtale
