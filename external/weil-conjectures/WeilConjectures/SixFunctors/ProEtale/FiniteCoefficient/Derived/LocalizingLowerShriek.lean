/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekTriangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts

/-!
# Compact support along one compactification on `Loc(Dctf)`

Let `Λ` be a finite ring whose exponent is invertible on a finite-type `k`-scheme `Y`, and let
`c = (X ⟶[j] X̄ ⟶[p] Y)` be a compactification of `f : X ⟶ Y`. Blueprint
`proposition-construction-independence-rf-shriek`: the compact-support functor
`Rf_!(c) = Rp_* ∘ j_!`

* preserves coproducts of objects of `Loc(Dctf(X, Λ))`
  (`preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification`):
  `j_!` is a left adjoint and preserves complexes with cohomology sheaves of étale origin, and
  `Rp_*` commutes with coproducts of such complexes
  (`AlgebraicGeometry.ProEtale.isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology`);
* hence maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(Y, Λ))`
  (`AlgebraicGeometry.ProEtale.localizingClosure_rightDerivedLowerShriekOfCompactification_obj`),
  since it maps `Dctf(X, Λ)` into `Dctf(Y, Λ)`
  (`AlgebraicGeometry.ProEtale.constructibleFiniteTor_rightDerivedLowerShriekOfCompactification`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  {f : X ⟶ Y} (c : Compactification f)

include aY in
/-- Blueprint `proposition-construction-independence-rf-shriek`: the compact-support functor
`Rf_!(c)` preserves coproducts of objects of `Loc(Dctf(X, Λ))`. -/
theorem preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification
    (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure.ι ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) := by
  let L := (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure
  let Φ := L.ι ⋙ (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategory
  have (M : J → L.FullSubcategory) : PreservesColimit (Discrete.functor M)
      (L.ι ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c) := by
    have hM (j : J) : DerivedCategory.etaleOriginHomology Λ c.Z (Φ.obj (M j)) :=
      DerivedCategory.etaleOriginHomology_openImmersionLowerShriek Λ c.Z c.i
        (DerivedCategory.localizingClosure_constructibleFiniteTor_le Λ X _ (M j).property)
    have := isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology Λ c.g
      (c.g ≫ aY) aY rfl (fun j ↦ Φ.obj (M j)) hM
    have : PreservesColimit (Discrete.functor fun j ↦ Φ.obj (M j))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor :=
      PreservesCoproduct.of_iso_comparison _ _
    have : PreservesColimit (Discrete.functor ((Discrete.functor M ⋙ Φ).obj ∘ Discrete.mk))
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor := this
    have : PreservesColimit (Discrete.functor M ⋙ Φ)
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor :=
      preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := Discrete.functor M ⋙ Φ)).symm
    exact inferInstanceAs (PreservesColimit (Discrete.functor M)
      (Φ ⋙ (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) c.g).rightDerivedFunctor))
  exact preservesColimitsOfShape_of_discrete _

include aY in
/-- Blueprint `proposition-construction-independence-rf-shriek`: the compact-support functor
`Rf_!(c)` maps `Loc(Dctf(X, Λ))` into `Loc(Dctf(Y, Λ))`. -/
theorem localizingClosure_rightDerivedLowerShriekOfCompactification_obj [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hK : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure K) :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).localizingClosure
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K) :=
  have := preservesColimitsOfShape_localizingClosure_rightDerivedLowerShriekOfCompactification
    Λ aY c
  ObjectProperty.localizingClosure_obj_of_le _ _ _
    (fun _ hK ↦ ObjectProperty.le_localizingClosure _ _
      (constructibleFiniteTor_rightDerivedLowerShriekOfCompactification Λ aY c hK)) K hK

end AlgebraicGeometry.ProEtale
