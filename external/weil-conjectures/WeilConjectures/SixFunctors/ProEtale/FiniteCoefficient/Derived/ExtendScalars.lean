/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-!
# Derived extension of scalars on the pro-étale site

Let `S` be an algebra over a commutative ring `R`, not necessarily flat. Derived scalar extension
`K ↦ K ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` is the total left derived functor
`L(sheafExtendScalars (algebraMap R S) X)` of the extension of scalars of pro-étale sheaves,
computed on K-flat complexes: restricted back to `R`, the extension of scalars is the tensor
product with the constant sheaf `S_X`, so it sends quasi-isomorphisms between K-flat complexes
to quasi-isomorphisms. It is left adjoint to the restriction of scalars
`D(X_proét, S) ⥤ D(X_proét, R)`.

Derived scalar extension commutes with the derived pullbacks: for `g : Z ⟶ Y` both composites
`L(S ⊗_R -) ⋙ Lg^*` and `Lg^* ⋙ L(S ⊗_R -)` are total left derived functors of the composite
`g^* (S ⊗_R -) ≅ S ⊗_R g^* -` of sheaf functors, the second one being computed on the complexes
whose pullback by `g` is K-flat (`AlgebraicGeometry.ProEtale.kFlatUpperStar`).

## Main definitions

- `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsAdjunction`: the adjunction between
  derived scalar extension `- ⊗ᴸ_R S` (blueprint `prose-03-02`) and restriction of
  scalars.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`: the isomorphism
  `(Lg^* K) ⊗ᴸ_R S ≅ Lg^*(K ⊗ᴸ_R S)` (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S]

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

/- Mathlib's instance is stated for `extendScalars.{u₁, u₂, max u₂ w}`, and unifying
`u + 1 =?= max (u + 1) ?w` gets stuck. -/
instance (φ : R →+* S) : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint

section

variable (R S) (X : Scheme.{u})

instance : (sheafCompose (ProEt.topology X)
    (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).PreservesHomology where

/-- Derived scalar extension is computed on K-flat complexes: restricted back to `R`, the
extension of scalars of a morphism `f` of complexes is `f ⊗ S_X`, a quasi-isomorphism when `f`
is a quasi-isomorphism between K-flat complexes. -/
instance preservesKFlatQuasiIso_sheafExtendScalars :
    (sheafExtendScalars (algebraMap R S) X).PreservesKFlatQuasiIso where
  quasiIso_map {K L} hK hL f _ := by
    let J := ProEt.topology X
    let c := (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R S)
    have : MorphismProperty.localizerMorphismKFlat
        (quasiIso (Sheaf J (ModuleCat.{u + 1} R)) (.up ℤ)) |>.HasLeftResolutions := fun Y ↦ by
      obtain ⟨P, π, hπ, -, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := π, hw := (mem_quasiIso_iff _).2 hπ }⟩
    -- restricted back to `R`, the extension of scalars of `f` is `f ⊗ S_X`, a
    -- quasi-isomorphism since `K` and `L` are K-flat
    have h₁ : quasiIso _ (.up ℤ) (f ▷ (single _ (.up ℤ) 0).obj c) :=
      (quasiIso _ (.up ℤ)).whiskerRight_of_kFlat f ((mem_quasiIso_iff _).2 inferInstance) hK hL _
    have h₂ : QuasiIso (((tensorRight c).mapHomologicalComplex (.up ℤ)).map f) :=
      (mem_quasiIso_iff _).1 (((quasiIso _ (.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
          (curriedTensor _) c) f)).1 h₁)
    have h₃ : QuasiIso (((sheafExtendScalars (algebraMap R S) X ⋙
        sheafCompose J (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapHomologicalComplex
          (.up ℤ)).map f) :=
      (mem_quasiIso_iff _).1 (((quasiIso _ (.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex
          (Sheaf.extendScalarsCompRestrictScalarsIso J R S) (.up ℤ)) f)).2
        ((mem_quasiIso_iff _).2 h₂))
    rw [← quasiIso_map_iff_of_preservesHomology _
      (sheafCompose J (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)))]
    exact h₃

/-- Derived scalar extension `- ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` (blueprint
`prose-03-02`) is left adjoint to restriction of scalars. -/
noncomputable def leftDerivedSheafExtendScalarsAdjunction :
    L(sheafExtendScalars (algebraMap R S) X) ⊣
      D(sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))) :=
  (sheafExtendScalarsAdjunction (algebraMap R S) X).derivedAdjunction.ofNatIsoRight
    (sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).rightDerivedFunctorIsoMapDerivedCategory

end

section Pullback

variable (R S) [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The isomorphism `g^*(S ⊗_R -) ≅ S ⊗_R g^* -` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`, on homotopy categories. -/
noncomputable def mapHomotopyCategorySheafExtendScalarsCompUpperStarIso :
    (sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ) ≅
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) _ ≪≫
    { hom := NatTrans.mapHomotopyCategory
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory
        (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv (.up ℤ)
      hom_inv_id := by simp [← NatTrans.mapHomotopyCategory_comp]
      inv_hom_id := by simp [← NatTrans.mapHomotopyCategory_comp] } ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm

/-- The counit exhibiting `L(S ⊗_R -) ⋙ Lg^*` as a total left derived functor of
`S ⊗_R - ⋙ g^*`: the counit of `L(S ⊗_R -)` followed by the counit of `Lg^*`. -/
noncomputable def leftDerivedSheafExtendScalarsUpperStarCounit :
    DerivedCategory.Qh ⋙ L(sheafExtendScalars (algebraMap R S) Y) ⋙
        L((g)^*[ModuleCat.{u + 1} S]) ⟶
      (sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit
      L((g)^*[ModuleCat.{u + 1} S]) ≫
    Functor.whiskerLeft ((sheafExtendScalars (algebraMap R S) Y).mapHomotopyCategory (.up ℤ))
      (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit

instance isLeftDerivedFunctor_leftDerivedSheafExtendScalarsUpperStar :
    (L(sheafExtendScalars (algebraMap R S) Y) ⋙ L((g)^*[ModuleCat.{u + 1} S])).IsLeftDerivedFunctor
      (leftDerivedSheafExtendScalarsUpperStarCounit R S g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun K ↦ ?_)
  have : IsIso ((sheafExtendScalars (algebraMap R S) Y).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.obj K)) :=
    (sheafExtendScalars (algebraMap R S) Y).isIso_leftDerivedFunctorCounit_app_of_kFlat
      K.obj.as ((HomotopyCategory.kFlat_quotient_obj_iff _).1 K.property)
  simp only [leftDerivedSheafExtendScalarsUpperStarCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance

/-- The counit exhibiting `Lg^* ⋙ L(S ⊗_R -)` as a total left derived functor of
`g^* ⋙ S ⊗_R -`: the counit of `Lg^*` followed by the counit of `L(S ⊗_R -)`. -/
noncomputable def leftDerivedUpperStarSheafExtendScalarsCounit :
    DerivedCategory.Qh ⋙ L((g)^*[ModuleCat.{u + 1} R]) ⋙
        L(sheafExtendScalars (algebraMap R S) Z) ⟶
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh :=
  Functor.whiskerRight (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit
      L(sheafExtendScalars (algebraMap R S) Z) ≫
    Functor.whiskerLeft ((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ))
      (sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit

omit [IsNoetherianRing R] in
/-- On a complex whose pullback by `g` is K-flat, the counit of `L(S ⊗_R -)` at the pullback is an
isomorphism. -/
lemma isIso_leftDerivedFunctorCounit_app_mapHomotopyCategory_obj
    (K : CochainComplex (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) ℤ)
    (hK : kFlatUpperStar (ModuleCat.{u + 1} R) g ((HomotopyCategory.quotient _ _).obj K)) :
    IsIso ((sheafExtendScalars (algebraMap R S) Z).leftDerivedFunctorCounit.app
      (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj K))) := by
  have hK₀ := kFlat_mapHomologicalComplex_obj_of_kFlatUpperStar _ g hK
  have := (sheafExtendScalars (algebraMap R S) Z).isIso_leftDerivedFunctorCounit_app_of_kFlat _ hK₀
  exact (NatTrans.isIso_app_iff_of_iso _
    (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategoryFactors (.up ℤ)).app K)).2 this

instance isLeftDerivedFunctor_leftDerivedUpperStarSheafExtendScalars :
    (L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Z)).IsLeftDerivedFunctor
      (leftDerivedUpperStarSheafExtendScalarsCounit R S g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar (ModuleCat.{u + 1} R) g)) _
    (fun K ↦ ?_)
  have := isIso_leftDerivedFunctorCounit_app_mapHomotopyCategory_obj R S g K.obj.as K.property
  simp only [leftDerivedUpperStarSheafExtendScalarsCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' inferInstance this

/-- **Derived scalar extension commutes with the derived pullback.** For `g : Z ⟶ Y`, the
isomorphism `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S` of functors `D(Y_proét, R) ⥤ D(Z_proét, S)`
induced by the isomorphism `g^*(S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`: both composites are total left
derived functors of the two sides (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`). -/
noncomputable def leftDerivedUpperStarExtendScalarsIso :
    L(sheafExtendScalars (algebraMap R S) Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ≅
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Z) :=
  Functor.leftDerivedNatIso _ _ (leftDerivedSheafExtendScalarsUpperStarCounit R S g)
    (leftDerivedUpperStarSheafExtendScalarsCounit R S g) (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g)
      DerivedCategory.Qh)

/-- The isomorphism `leftDerivedUpperStarExtendScalarsIso` is compatible with the counits: it is
induced by `g^*(S ⊗_R F) ≅ S ⊗_R g^* F`. -/
@[reassoc]
lemma leftDerivedUpperStarExtendScalarsIso_hom_app_comp_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedUpperStarExtendScalarsIso R S g).hom.app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedUpperStarSheafExtendScalarsCounit R S g).app K =
      (leftDerivedSheafExtendScalarsUpperStarCounit R S g).app K ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso _ (.up ℤ)) _ K

end Pullback

end AlgebraicGeometry.ProEtale
