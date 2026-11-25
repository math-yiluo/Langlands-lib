/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!
# Complexes whose pullback is K-flat

- `AlgebraicGeometry.Etale.kFlatUpperStar g`: the complexes on `Y_ét` whose pullback by `g`
  is K-flat, and `AlgebraicGeometry.Etale.isLeftDerivabilityStructure_kFlatUpperStar`:
  they form a left derivability structure.

See `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal` for an overview.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
/-- The complexes of étale sheaves on `Y` whose pullback by `g : Z ⟶ Y` is K-flat: the
inverse image of the K-flat complexes of `K(Z_ét)` under `g^* : K(Y_ét) ⥤ K(Z_ét)`. -/
abbrev kFlatUpperStar :
    ObjectProperty (HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :=
  (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat.inverseImage
    ((g)^*[A].mapHomotopyCategory (.up ℤ))

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The pullbacks of the functorial flat resolutions of complexes of étale sheaves on `Y` are
K-flat. -/
lemma kFlatUpperStar_quotient_obj_resolutionFunctor_obj [(g)^*[A].PreservesFlat]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A))
    [Λ.F.PreservesZeroMorphisms]
    (K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :
    kFlatUpperStar A g ((HomotopyCategory.quotient _ _).obj (Λ.resolutionFunctor.obj K)) :=
  -- Transported along `mapHomotopyCategoryFactors`: checking the statement against
  -- `kFlat_quotient_obj_iff` up to defeq makes the kernel unfold `mapHomotopyCategory`
  -- (about a minute).
  ObjectProperty.prop_of_iso
    (HomotopyCategory.quasiIso (Sheaf Z.smallEtaleTopology A) (.up ℤ)).kFlat
    (((g)^*[A].mapHomotopyCategoryFactors (.up ℤ)).app (Λ.resolutionFunctor.obj K)).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (kFlat_upperStar_mapHomologicalComplex_obj g
        (Λ.colimitOfShapeFlatResolutionFunctorObj
          ObjectProperty.flat.essImage_ι_le K).colimitsOfShape))

omit [Abelian.HasFunctorialFlatResolution A] in
/-- Given a functorial flat resolution `Λ` of étale sheaves on `Y`, the complexes whose
pullback by `g` is K-flat form a left derivability structure on `K(Y_ét)` for the
quasi-isomorphisms. -/
lemma isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution
    [(g)^*[A].PreservesFlat]
    (Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ Sheaf Y.smallEtaleTopology A)) :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance)
    (kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ.reduced)

/-- The complexes whose pullback by `g` is K-flat form a left derivability structure on
`K(Y_ét)` for the quasi-isomorphisms. The functorial flat resolution of étale sheaves on `Y`
is given by the instance `Etale.hasFunctorialFlatResolution_sheaf`. -/
instance isLeftDerivabilityStructure_kFlatUpperStar [(g)^*[A].PreservesFlat] :
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar A g)).IsLeftDerivabilityStructure :=
  isLeftDerivabilityStructure_kFlatUpperStar_of_leftResolution A g
    (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some

end Etale

end AlgebraicGeometry
