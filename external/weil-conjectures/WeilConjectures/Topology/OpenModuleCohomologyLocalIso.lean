/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
import WeilConjectures.Topology.RestrictInjectiveResolution
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Open cohomology inverts morphisms that are isomorphisms on the open

Source: Stacks Project, Cohomology, Tag 01E1.
(blueprint: lem-sc-open-module-cohomology-local-iso)
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.RingedSpace

/-- Open cohomology depends only on the restriction of a module morphism.
Source: Stacks Project, Cohomology, Tag 01E1, restriction of injective resolutions.
Proof: Choose injective resolutions of M and N and a comparison map lifting f.
Restrict both resolutions to U. By restrict_injectiveResolution these are injective
resolutions on the over-site of U. Their restricted comparison map lifts the
isomorphism R(f), hence is a homotopy equivalence by comparison of injective
resolutions. Sections on U of the original resolutions are precisely sections at
the terminal object of these restricted resolutions. Applying this additive
sections functor preserves the homotopy equivalence. Taking degree p homology
therefore gives an isomorphism. Naturality of the injective-resolution comparison
identifies it with the displayed openModuleCohomology map. This also treats the
empty open and p = 0, without finiteness assumptions.
(blueprint: lem-sc-open-module-cohomology-local-iso). -/
theorem openModuleCohomology_map_isIso_of_overFunctor (X : RingedSpace.{u})
    (U : Opens X) {M N : SheafOfModules.{u} (moduleRings X)} (f : M ⟶ N)
    [IsIso ((SheafOfModules.overFunctor (moduleRings X) U).map f)] (p : ℕ) :
    IsIso ((openModuleCohomology X p U).map f) := by
  classical
  let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
  have : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} ((moduleRings X).over U)) :=
    SheafOfModules.isGrothendieckAbelian ((moduleRings X).over U)
  have : EnoughInjectives (SheafOfModules.{u} ((moduleRings X).over U)) := inferInstance
  obtain ⟨hlim, hcolim, _, _, _⟩ := open_restriction_adjunction_exact X U
  let := hlim
  let := hcolim
  let restrict {A : SheafOfModules.{u} (moduleRings X)} (I : InjectiveResolution A) :
      InjectiveResolution (R.obj A) :=
    { cocomplex := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
      injective := (restrict_injectiveResolution X U A I).2
      ι := ((HomologicalComplex.singleMapHomologicalComplex
        R (ComplexShape.up ℕ) 0).app A).inv ≫
        (R.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι }
  let I := injectiveResolution M
  let J := injectiveResolution N
  let φ := InjectiveResolution.desc f J I
  let ψ := (R.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  have comm : (restrict I).ι.f 0 ≫ ψ.f 0 = R.map f ≫ (restrict J).ι.f 0 := by
    change R.map (I.ι.f 0) ≫ R.map (φ.f 0) = R.map f ≫ R.map (J.ι.f 0)
    rw [← R.map_comp, ← R.map_comp, InjectiveResolution.desc_commutes_zero]
  have hn := InjectiveResolution.iso_hom_naturality (R.map f) (restrict I) (restrict J) ψ comm
  have hi : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℕ)).map ψ) := by
    have : IsIso ((restrict I).iso.hom ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℕ)).map ψ) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (restrict I).iso.hom _
  let T : SheafOfModules.{u} ((moduleRings X).over U) ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.forget ((moduleRings X).over U) ⋙
      PresheafOfModules.toPresheaf ((moduleRings X).over U).obj ⋙
      (evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj
        (Opposite.op (Over.mk (𝟙 U)))
  have hi' : IsIso (((T.mapHomotopyCategory (ComplexShape.up ℕ)) ⋙
      HomotopyCategory.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).map
      ((HomotopyCategory.quotient _ _).map ψ)) := by infer_instance
  have hn' := InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ
    (InjectiveResolution.desc_commutes_zero f J I) (openModuleSections X U) p
  have hmap : IsIso (((openModuleSections X U).mapHomologicalComplex _ ⋙
      HomologicalComplex.homologyFunctor _ _ p).map φ) := by
    have hT : IsIso ((HomologicalComplex.homologyFunctor AddCommGrpCat
        (ComplexShape.up ℕ) p).map
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ)) := by
      rw [← NatIso.isIso_map_iff
        (HomotopyCategory.homologyFunctorFactors AddCommGrpCat (ComplexShape.up ℕ) p)]
      exact hi'
    -- Compare the section functors before passing to complexes and homology.
    let e : R ⋙ T ≅ openModuleSections X U := Iso.refl _
    exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ))
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p)) φ).mp hT
  have : IsIso (((openModuleSections X U).rightDerived p).map f ≫
      (J.isoRightDerivedObj (openModuleSections X U) p).hom) := by
    rw [hn']
    infer_instance
  change IsIso (((openModuleSections X U).rightDerived p).map f)
  exact IsIso.of_isIso_comp_right _ (J.isoRightDerivedObj (openModuleSections X U) p).hom

end AlgebraicGeometry.RingedSpace
