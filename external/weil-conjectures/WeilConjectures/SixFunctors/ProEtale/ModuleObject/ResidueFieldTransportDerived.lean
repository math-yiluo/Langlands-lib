/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportSection

/-!
# Derived pullback and pushforward of residue field module sheaves

Write `G_X = residueFieldModuleSheaf X ℓ E` for the equivalence between module objects over
`𝔽_{E,X}` and pro-étale sheaves of `𝔽_E`-modules, and `D(G_X)` for the induced equivalence of
derived categories. For a morphism `f : X ⟶ Y` of schemes:

- `ProEtale.residueFieldDerivedUpperStarIso`: `Lf^* ⋙ D(G_X) ≅ D(G_Y) ⋙ Lf^*`, induced by
  `ProEtale.residueFieldModuleSheafUpperStarIso`;
- `ProEtale.residueFieldDerivedPushHom`: its mate `Rf_* ⋙ D(G_Y) ⟶ D(G_X) ⋙ Rf_*` along the
  derived adjunctions, which is an isomorphism since `D(G_X)` and `D(G_Y)` are equivalences
  (`ProEtale.isIso_residueFieldDerivedPushHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullbacks commute with the equivalences `D(G)` between derived categories of
module objects over `𝔽_E` and of pro-étale sheaves of `𝔽_E`-modules:
`Lf^* ⋙ D(G_X) ≅ D(G_Y) ⋙ Lf^*`, induced by `residueFieldModuleSheafUpperStarIso`. -/
noncomputable def residueFieldDerivedUpperStarIso :
    L((f)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧) ⋙
        (residueFieldModuleSheaf X ℓ E).mapDerivedCategory ≅
      (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory ⋙
        L((f)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]) :=
  Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f) _ ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ f).symm

/-- The comparison `Rf_* ⋙ D(G_Y) ⟶ D(G_X) ⋙ Rf_*` between the derived pushforwards: the mate
of the inverse of `residueFieldDerivedUpperStarIso` along the derived adjunctions
`Lf^* ⊣ Rf_*`. -/
noncomputable def residueFieldDerivedPushHom :
    R((f)_*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)⟧) ⋙
        (residueFieldModuleSheaf Y ℓ E).mapDerivedCategory ⟶
      (residueFieldModuleSheaf X ℓ E).mapDerivedCategory ⋙
        R((f)_*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)]) :=
  (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction
    (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E)) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction _ f)
    (residueFieldDerivedUpperStarIso ℓ E f).inv)

/-- **The derived pushforwards commute with the equivalences `D(G)`**: the comparison
`residueFieldDerivedPushHom` is an isomorphism, being the mate of an isomorphism along
equivalences. -/
instance isIso_residueFieldDerivedPushHom : IsIso (residueFieldDerivedPushHom ℓ E f) :=
  isIso_mateEquiv_of_isEquivalence _ _ _

end AlgebraicGeometry.ProEtale
