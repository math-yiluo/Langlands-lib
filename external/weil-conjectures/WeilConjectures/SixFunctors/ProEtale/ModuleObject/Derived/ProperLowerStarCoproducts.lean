/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange
public import WeilConjectures.AlgebraicGeometry.Curve.FunctionFieldCohomology
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GeometricFiber
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.Grothendieck
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.FiniteOverField
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# The direct image commutes with direct sums on `Loc(Dᵇc)`, from the heart

Let `Λ` be a commutative condensed ring and `p : Z ⟶ Y` a morphism of schemes. Blueprint
`proposition-compactness-proper-direct-image--2` (2), (3): the derived direct image `Rp_*` on module
objects over `Λ` commutes with direct sums of objects of `Loc(Dᵇc(Z)⟦Λ⟧)` as soon as it does so
on the "ind-constructible heart" and has finite amplitude there.

The heart is replaced here by the smallest class of module objects containing the constructible
ones and closed under isomorphisms, kernels, cokernels, extensions and direct sums
(`AlgebraicGeometry.ProEtale.CondensedRing.constructibleCoproductClosure`). It is contained in
the class `IndCons(Z, Λ)` of the blueprint (blueprint `proposition-ind-constructible-sheaves`), so
the hypotheses below are implied by blueprint `proposition-compactness-proper-direct-image--2` (1).
The complexes with cohomology in this class form a localizing subcategory containing `Dᵇc(Z)⟦Λ⟧`,
hence `Loc(Dᵇc(Z)⟦Λ⟧)`.

The reduction is `DerivedCategory.isIso_sigmaComparison_of_homologyProperty`; its exactness
hypotheses hold since the pro-étale topos is replete
(`AlgebraicGeometry.ProEtale.CondensedRing.countableAB4Star_mod`), so that the derived category of
module objects is left complete (`DerivedCategory.isHomotopyLimit_truncGECone`).

## Main results

* `AlgebraicGeometry.ProEtale.CondensedRing.homologyProperty_of_localizingClosure`: the objects
  of `Loc(Dᵇc(Z)⟦Λ⟧)` have cohomology in `constructibleCoproductClosure`.
* `preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar` (in the same namespace):
  if `Rp_*` sends the objects of `constructibleCoproductClosure` into degrees `≤ d` and commutes
  with direct sums of them, then its restriction to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Repleteness for module objects**: module objects over `Λ_X` on the pro-étale site satisfy
countable AB4\*, i.e. countable products are exact. -/
instance countableAB4Star_mod (X : Scheme.{u}) :
    CountableAB4Star (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi ProEt.epi_π_app_zero_of_epi_addCommGrpCat)

/-- The smallest class of module objects over `Λ_X` containing the constructible ones and closed
under isomorphisms, kernels, cokernels, extensions and direct sums. It is contained in the
ind-constructible sheaves `IndCons(X, Λ)` of the blueprint
(`proposition-ind-constructible-sheaves`). -/
abbrev constructibleCoproductClosure (X : Scheme.{u}) :
    ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstructibleModuleObject (condensedRingObj Λ X))

/-- The complexes of module objects with cohomology in `constructibleCoproductClosure` form a
localizing subcategory. -/
instance isLocalizing_homologyProperty_constructibleCoproductClosure (X : Scheme.{u}) :
    (DerivedCategory.homologyProperty (constructibleCoproductClosure Λ X)).IsLocalizing where
  isClosedUnderColimitsOfShape_discrete _ := ⟨fun _ ⟨h⟩ n ↦
    (constructibleCoproductClosure Λ X).prop_of_isColimit
      (isColimitOfPreserves (DerivedCategory.homologyFunctor _ n) h.isColimit)
      fun j ↦ h.prop_diag_obj j n⟩

omit [IsCommMonObj Λ] in
/-- The objects of `Loc(Dᵇc(X)⟦Λ⟧)` have cohomology in `constructibleCoproductClosure`. -/
lemma homologyProperty_of_localizingClosure (X : Scheme.{u}) :
    (boundedConstructible (condensedRingObj Λ X)).localizingClosure ≤
      DerivedCategory.homologyProperty (constructibleCoproductClosure Λ X) :=
  ObjectProperty.localizingClosure_le fun _ hK n ↦
    ObjectProperty.le_weakSerreCoproductClosure _ _ (hK.2 n)

/-- Blueprint `proposition-compactness-proper-direct-image--2` (2), (3), reduced to the heart: if
the derived direct image `Rp_*` sends the module objects of `constructibleCoproductClosure`, placed
in degree `0`, into degrees `≤ d`, and commutes with direct sums of them, then its restriction to
`Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums. -/
theorem preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar {Z Y : Scheme.{u}}
    (p : Z ⟶ Y) (d : ℤ)
    (hp₁ : ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d)
    (hp₂ : ∀ (J : Type (u + 1)) (N : J → Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj Λ Z)), (∀ j, constructibleCoproductClosure Λ Z (N j)) →
      IsIso (sigmaComparison R((p)_*⟦Λ⟧) fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j)))
    (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((boundedConstructible (condensedRingObj Λ Z)).localizingClosure.ι ⋙ R((p)_*⟦Λ⟧)) := by
  let L := (boundedConstructible (condensedRingObj Λ Z)).localizingClosure
  have (M : J → L.FullSubcategory) : PreservesColimit (Discrete.functor M) (L.ι ⋙ R((p)_*⟦Λ⟧)) := by
    have := DerivedCategory.isIso_sigmaComparison_of_homologyProperty R((p)_*⟦Λ⟧)
      (constructibleCoproductClosure Λ Z) d hp₁
      (fun X a _ ↦ Functor.isGE_rightDerivedFunctor_obj _ X a) (hp₂ J) (fun j ↦ (M j).obj)
      fun j ↦ homologyProperty_of_localizingClosure Λ Z _ (M j).property
    have : PreservesColimit (Discrete.functor fun j ↦ (M j).obj) R((p)_*⟦Λ⟧) :=
      PreservesCoproduct.of_iso_comparison _ _
    have : PreservesColimit (Discrete.functor M ⋙ L.ι) R((p)_*⟦Λ⟧) :=
      preservesColimit_of_iso_diagram _ (Discrete.natIso (F := Discrete.functor fun j ↦ (M j).obj)
        (G := Discrete.functor M ⋙ L.ι) fun _ ↦ Iso.refl _)
    exact inferInstanceAs (PreservesColimit (Discrete.functor M) (L.ι ⋙ R((p)_*⟦Λ⟧)))
  exact preservesColimitsOfShape_of_discrete _

/-- The properties of the derived direct image `Rp_*` on the heart used for its commutation with
direct sums (blueprints `lemma-uniform-bound-proper-direct-image` and
`proposition-compactness-proper-direct-image--2` (1)): there is a `d` such that `Rp_*` sends the
module objects of `constructibleCoproductClosure`, placed in degree `0`, into degrees `≤ d`, and
`Rp_*` commutes with direct sums of such module objects. -/
def ProperLowerStarHeartHypotheses {Z Y : Scheme.{u}} (p : Z ⟶ Y) : Prop :=
  (∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
    (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d) ∧
  ∀ (J : Type (u + 1)) (N : J → Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)), (∀ j, constructibleCoproductClosure Λ Z (N j)) →
    IsIso (sigmaComparison R((p)_*⟦Λ⟧) fun j ↦ (DerivedCategory.singleFunctor _ 0).obj (N j))

variable {Λ} in
/-- Blueprint `proposition-compactness-proper-direct-image--2` (3) and
`lemma-proper-direct-image-unbounded-complexes`: under `ProperLowerStarHeartHypotheses`, the
restriction of `Rp_*` to `Loc(Dᵇc(Z)⟦Λ⟧)` preserves direct sums. -/
theorem ProperLowerStarHeartHypotheses.preservesColimitsOfShape {Z Y : Scheme.{u}}
    {p : Z ⟶ Y} (hp : ProperLowerStarHeartHypotheses Λ p) (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J)
      ((boundedConstructible (condensedRingObj Λ Z)).localizingClosure.ι ⋙ R((p)_*⟦Λ⟧)) :=
  preservesColimitsOfShape_localizingClosure_rightDerivedLowerStar Λ p hp.1.choose
    hp.1.choose_spec hp.2 J

end AlgebraicGeometry.ProEtale.CondensedRing
