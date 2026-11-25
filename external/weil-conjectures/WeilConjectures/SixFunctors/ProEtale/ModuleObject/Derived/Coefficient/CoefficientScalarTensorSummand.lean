/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorOrdinary
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorSummandFormulas
/-! # The scalar tensor square on a total-complex summand

The ordinary scalar tensor square gives equality on every individual summand
of the unbounded signed direct-sum total complex.
(blueprint: lem-sfb-coefficient-scalar-tensor-summand)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension internalScalarMonoidal
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

-- Keep prolongation functors transparent during implicit object matching.

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

-- Preserve the abstract total and section constructions during diagram matching.
attribute [local irreducible] HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

attribute [local irreducible] coefficientSectionScalarTotal

-- Normalize the four functor images of each total-complex summand.
/-- The signed scalar tensor square commutes after each coproduct-summand inclusion.
Source: Stacks Project, Cohomology on Sites, Tag 07A4.
In degree n, test the maps on each coproduct summand indexed by p+q=n.
The internal and section total tensor maps restrict to their ordinary tensorators.
The equivalence comparison restricts to its ordinary comparison and the termwise
scalar comparison restricts to its component in degrees p and q. Thus the square
on each summand is exactly the ordinary scalar tensor square. Coproduct
inclusion is therefore followed by the same map on both sides.
(blueprint: lem-sfb-coefficient-scalar-tensor-summand). -/
theorem coefficientScalarTensor_summand (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d)
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    let := internalScalarMonoidal a Z
    let F := Mod.extendScalars (coefficientMap a Z)
    let ER := (ModuleRingedComparison.equivalence R Z).functor
    let ES := (ModuleRingedComparison.equivalence S Z).functor
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let ERc := ER.mapHomologicalComplex (.up ℤ)
    let ESc := ES.mapHomologicalComplex (.up ℤ)
    let Bc := d.b.extension.mapHomologicalComplex (.up ℤ)
    let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex d.o (.up ℤ)
    ES.map (F.map (HomologicalComplex.ιTensorObj P Q p q n hpq)) ≫
      ES.map ((((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
        P).app Q).f n) ≫
      (ModuleRingedComparison.totalComparison S Z (Fc.obj P) (Fc.obj Q)).hom.f n ≫
      (o.hom.app P ⊗ₘ o.hom.app Q).f n =
    ES.map (F.map (HomologicalComplex.ιTensorObj P Q p q n hpq)) ≫
      (o.hom.app (P ⊗ Q)).f n ≫
      d.b.extension.map ((ModuleRingedComparison.totalComparison R Z P Q).hom.f n) ≫
      (coefficientSectionScalarTotal a Z d.b d.m (ERc.obj P) (ERc.obj Q)).f n := by
  let := internalScalarMonoidal a Z
  let := d.m
  let := d.b.ordinaryAdjunction.isLeftAdjoint
  let F := Mod.extendScalars (coefficientMap a Z)
  let ER := (ModuleRingedComparison.equivalence R Z).functor
  let ES := (ModuleRingedComparison.equivalence S Z).functor
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let ESc := ES.mapHomologicalComplex (.up ℤ)
  let Bc := d.b.extension.mapHomologicalComplex (.up ℤ)
  let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex d.o (.up ℤ)
  let δ := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  let δb := coefficientSectionScalarTotal a Z d.b d.m (ERc.obj P) (ERc.obj Q)
  let r := ModuleRingedComparison.totalComparison R Z P Q
  let s := ModuleRingedComparison.totalComparison S Z (Fc.obj P) (Fc.obj Q)
  refine paste_summand_square ER ES F d.b.extension d.o
    (HomologicalComplex.ιTensorObj P Q p q n hpq)
    (δ.f n) (r.hom.f n) (s.hom.f n) (δb.f n)
    ((o.hom.app P ⊗ₘ o.hom.app Q).f n)
    (Functor.OplaxMonoidal.δ F (P.X p) (Q.X q))
    (ModuleRingedComparison.ordinaryTensorComparison R Z (P.X p) (Q.X q)).hom
    (ModuleRingedComparison.ordinaryTensorComparison S Z (F.obj (P.X p))
      (F.obj (Q.X q))).hom
    (Functor.OplaxMonoidal.δ d.b.extension (ER.obj (P.X p)) (ER.obj (Q.X q)))
    (HomologicalComplex.ιTensorObj (Fc.obj P) (Fc.obj Q) p q n hpq)
    (HomologicalComplex.ιTensorObj (ERc.obj P) (ERc.obj Q) p q n hpq)
    (HomologicalComplex.ιTensorObj (ESc.obj (Fc.obj P)) (ESc.obj (Fc.obj Q)) p q n hpq)
    (HomologicalComplex.ιTensorObj (Bc.obj (ERc.obj P)) (Bc.obj (ERc.obj Q)) p q n hpq)
    (d.o.hom.app (P.X p) ⊗ₘ d.o.hom.app (Q.X q)) ?_ ?_ ?_ ?_ ?_
    (coefficientScalarTensor_ordinary a Z d h (P.X p) (Q.X q))
  · exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P Q p q n hpq
  · exact section_total_summand R Z P Q p q n hpq
  · exact section_total_summand S Z (Fc.obj P) (Fc.obj Q) p q n hpq
  · exact scalar_total_summand a Z d (ERc.obj P) (ERc.obj Q) p q n hpq
  · exact coefficientScalarTensor_summandNaturality (R := R) (S := S) Z
      F ES ER d.b.extension d.o P Q p q n hpq

end AlgebraicGeometry.ProEtale.CondensedRing
