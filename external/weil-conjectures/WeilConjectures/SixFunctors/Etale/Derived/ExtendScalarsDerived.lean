/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.KFlat
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Derived extension of scalars of étale sheaves

Let `φ : R →+* S` be a morphism of commutative rings, not necessarily flat. Derived extension of
scalars `Ψ = - ⊗ᴸ_R S : D(X_ét, R) ⥤ D(X_ét, S)` is the total left derived functor of the
extension of scalars of étale sheaves (`AlgebraicGeometry.Etale.sheafExtendScalars`),
computed on K-flat complexes: restricted back to `R`, extension of scalars is the tensor product
with the constant sheaf `S_X`, so it sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. It is left adjoint to the derived restriction of scalars, and its unit
exhibits derived base changes (`CategoryTheory.Sheaf.IsDerivedBaseChange`).

Derived extension of scalars commutes with the derived pullbacks: for `g : Z ⟶ Y` both
composites `Ψ ⋙ Lg^*` and `Lg^* ⋙ Ψ` are total left derived functors of the composite
`g^* (S ⊗_R -) ≅ S ⊗_R g^* -` of sheaf functors
(`AlgebraicGeometry.Etale.leftDerivedUpperStarEtaleSheafExtendScalarsIso`).

This is the étale counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section KFlatAux

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- A complex whose image in the homotopy category is in `kFlatUpperStar A g` has a K-flat
pullback by `g`. -/
lemma kFlat_mapHomologicalComplex_obj_of_kFlatUpperStar
    {K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ}
    (hK : kFlatUpperStar A g ((HomotopyCategory.quotient _ _).obj K)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj K) :=
  (HomotopyCategory.kFlat_quotient_obj_iff _).1 (ObjectProperty.prop_of_iso
    (HomotopyCategory.quasiIso (Sheaf Z.smallEtaleTopology A) (.up ℤ)).kFlat
    (((g)^*[A].mapHomotopyCategoryFactors (.up ℤ)).app K) hK)

end KFlatAux

end AlgebraicGeometry.Etale

-- The braiding of `ModuleCat` found by instance search (`instBraidedCategory`) is not syntactically
-- the one underlying the derived tensor product of étale sheaves, and the kernel cannot compare
-- the two monoidal structures in reasonable time; with these instances, instance search produces
-- exactly the monoidal structure used by `AlgebraicGeometry.Etale.derivedTensor`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)

section

variable (X : Scheme.{u})

instance : (sheafCompose X.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} φ)).PreservesHomology where

/-- Derived extension of scalars is computed on K-flat complexes: restricted back to `R`, the
extension of scalars of a morphism `f` of complexes is `f ⊗ S_X`, a quasi-isomorphism when `f`
is a quasi-isomorphism between K-flat complexes. -/
instance preservesKFlatQuasiIso_sheafExtendScalars :
    (sheafExtendScalars φ X).PreservesKFlatQuasiIso where
  quasiIso_map {K L} hK hL f _ := by
    let := φ.toAlgebra
    let J := X.smallEtaleTopology
    have : MorphismProperty.localizerMorphismKFlat
        (quasiIso (Sheaf J (ModuleCat.{u + 1} R)) (.up ℤ)) |>.HasLeftResolutions := fun Y ↦ by
      obtain ⟨P, π, hπ, -, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := π, hw := (mem_quasiIso_iff _).2 hπ }⟩
    let c := (constantSheaf J (ModuleCat.{u + 1} R)).obj (ModuleCat.of R S)
    have h₁ : quasiIso _ (.up ℤ) (f ▷ (single _ (.up ℤ) 0).obj c) :=
      (quasiIso _ (.up ℤ)).whiskerRight_of_kFlat f ((mem_quasiIso_iff _).2 inferInstance) hK hL _
    have h₂ : QuasiIso (((tensorRight c).mapHomologicalComplex (.up ℤ)).map f) :=
      (mem_quasiIso_iff _).1 (((quasiIso _ (.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (CochainComplex.map₂HomologicalComplexFlipObjSingleIso
          (curriedTensor _) c) f)).1 h₁)
    have h₃ : QuasiIso (((sheafExtendScalars φ X ⋙
        sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).mapHomologicalComplex
          (.up ℤ)).map f) :=
      (mem_quasiIso_iff _).1 (((quasiIso _ (.up ℤ)).arrow_mk_iso_iff
        (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex
          (Sheaf.extendScalarsCompRestrictScalarsIso J R S) (.up ℤ)) f)).2
        ((mem_quasiIso_iff _).2 h₂))
    rw [← quasiIso_map_iff_of_preservesHomology _
      (sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ))]
    exact h₃

/-- Derived extension of scalars `- ⊗ᴸ_R S : D(X_ét, R) ⥤ D(X_ét, S)` is left adjoint to the
derived restriction of scalars. -/
noncomputable def leftDerivedEtaleSheafExtendScalarsAdjunction :
    L(sheafExtendScalars φ X) ⊣ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ :=
  (sheafExtendScalarsAdjunction φ X).derivedAdjunction.ofNatIsoRight
    (sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{u + 1} φ)).rightDerivedFunctorIsoMapDerivedCategory

/-- The unit `K ⟶ Res (K ⊗ᴸ_R S)` of derived extension of scalars exhibits `K ⊗ᴸ_R S` as the
derived base change of `K`. -/
lemma isDerivedBaseChange_leftDerivedEtaleSheafExtendScalarsAdjunction_unit
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    Sheaf.IsDerivedBaseChange ((leftDerivedEtaleSheafExtendScalarsAdjunction φ X).unit.app K) :=
  fun N ↦ by
    convert ((leftDerivedEtaleSheafExtendScalarsAdjunction φ X).homEquiv K N).bijective using 1
    ext g
    exact ((leftDerivedEtaleSheafExtendScalarsAdjunction φ X).homEquiv_unit K N g).symm

end

section Pullback

variable [IsNoetherianRing R] {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The isomorphism `g^*(S ⊗_R -) ≅ S ⊗_R g^* -` of
`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso`, on homotopy categories. -/
noncomputable def mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso :
    (sheafExtendScalars φ Y).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ) ≅
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (sheafExtendScalars φ Z).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) _ ≪≫
    { hom := NatTrans.mapHomotopyCategory
        (sheafExtendScalarsCompUpperStarIso φ g).hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory
        (sheafExtendScalarsCompUpperStarIso φ g).inv (.up ℤ)
      hom_inv_id := by simp [← NatTrans.mapHomotopyCategory_comp]
      inv_hom_id := by simp [← NatTrans.mapHomotopyCategory_comp] } ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm

/-- The counit exhibiting `L(S ⊗_R -) ⋙ Lg^*` as a total left derived functor of
`S ⊗_R - ⋙ g^*`: the counit of `L(S ⊗_R -)` followed by the counit of `Lg^*`. -/
noncomputable def leftDerivedEtaleSheafExtendScalarsUpperStarCounit :
    DerivedCategory.Qh ⋙ L(sheafExtendScalars φ Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ⟶
      (sheafExtendScalars φ Y).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (sheafExtendScalars φ Y).leftDerivedFunctorCounit
      L((g)^*[ModuleCat.{u + 1} S]) ≫
    Functor.whiskerLeft ((sheafExtendScalars φ Y).mapHomotopyCategory (.up ℤ))
      (g)^*[ModuleCat.{u + 1} S].leftDerivedFunctorCounit

instance isLeftDerivedFunctor_leftDerivedEtaleSheafExtendScalarsUpperStar :
    (L(sheafExtendScalars φ Y) ⋙ L((g)^*[ModuleCat.{u + 1} S])).IsLeftDerivedFunctor
      (leftDerivedEtaleSheafExtendScalarsUpperStarCounit φ g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun K ↦ ?_)
  have : IsIso ((sheafExtendScalars φ Y).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.obj K)) :=
    (sheafExtendScalars φ Y).isIso_leftDerivedFunctorCounit_app_of_kFlat
      K.obj.as ((HomotopyCategory.kFlat_quotient_obj_iff _).1 K.property)
  simp only [leftDerivedEtaleSheafExtendScalarsUpperStarCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) inferInstance

/-- The counit exhibiting `Lg^* ⋙ L(S ⊗_R -)` as a total left derived functor of
`g^* ⋙ S ⊗_R -`: the counit of `Lg^*` followed by the counit of `L(S ⊗_R -)`. -/
noncomputable def leftDerivedUpperStarEtaleSheafExtendScalarsCounit :
    DerivedCategory.Qh ⋙ L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars φ Z) ⟶
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (sheafExtendScalars φ Z).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit
      L(sheafExtendScalars φ Z) ≫
    Functor.whiskerLeft ((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ))
      (sheafExtendScalars φ Z).leftDerivedFunctorCounit

omit [IsNoetherianRing R] in
/-- On a complex whose pullback by `g` is K-flat, the counit of `L(S ⊗_R -)` at the pullback is an
isomorphism. -/
lemma isIso_leftDerivedFunctorCounit_app_upperStar_mapHomotopyCategory_obj
    (K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    (hK : kFlatUpperStar (ModuleCat.{u + 1} R) g ((HomotopyCategory.quotient _ _).obj K)) :
    IsIso ((sheafExtendScalars φ Z).leftDerivedFunctorCounit.app
      (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj K))) := by
  have hK₀ := kFlat_mapHomologicalComplex_obj_of_kFlatUpperStar (ModuleCat.{u + 1} R) g hK
  have := (sheafExtendScalars φ Z).isIso_leftDerivedFunctorCounit_app_of_kFlat _ hK₀
  exact (NatTrans.isIso_app_iff_of_iso _
    (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategoryFactors (.up ℤ)).app K)).2 this

instance isLeftDerivedFunctor_leftDerivedUpperStarEtaleSheafExtendScalars :
    (L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars φ Z)).IsLeftDerivedFunctor
      (leftDerivedUpperStarEtaleSheafExtendScalarsCounit φ g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar (ModuleCat.{u + 1} R) g)) _
    (fun K ↦ ?_)
  have := isIso_leftDerivedFunctorCounit_app_upperStar_mapHomotopyCategory_obj φ g K.obj.as
    K.property
  simp only [leftDerivedUpperStarEtaleSheafExtendScalarsCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' inferInstance this

/-- **Derived extension of scalars commutes with the derived pullback.** For `g : Z ⟶ Y`, the
isomorphism `Lg^*(K ⊗ᴸ_R S) ≅ (Lg^* K) ⊗ᴸ_R S` of functors `D(Y_ét, R) ⥤ D(Z_ét, S)` induced by
the isomorphism `g^*(S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.Etale.sheafExtendScalarsCompUpperStarIso`: both composites are total
left derived functors of the two sides. -/
noncomputable def leftDerivedUpperStarEtaleSheafExtendScalarsIso :
    L(sheafExtendScalars φ Y) ⋙ L((g)^*[ModuleCat.{u + 1} S]) ≅
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars φ Z) :=
  Functor.leftDerivedNatIso _ _ (leftDerivedEtaleSheafExtendScalarsUpperStarCounit φ g)
    (leftDerivedUpperStarEtaleSheafExtendScalarsCounit φ g)
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso φ g)
      DerivedCategory.Qh)

omit [IsNoetherianRing R] in
/-- The isomorphism `leftDerivedUpperStarEtaleSheafExtendScalarsIso` is compatible with the
counits: it is induced by `g^*(S ⊗_R F) ≅ S ⊗_R g^* F`. -/
@[reassoc]
lemma leftDerivedUpperStarEtaleSheafExtendScalarsIso_hom_app_comp_counit
    (K : HomotopyCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedUpperStarEtaleSheafExtendScalarsIso φ g).hom.app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedUpperStarEtaleSheafExtendScalarsCounit φ g).app K =
      (leftDerivedEtaleSheafExtendScalarsUpperStarCounit φ g).app K ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso φ g).hom.app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso _ (.up ℤ)) _ K

end Pullback

end AlgebraicGeometry.Etale
