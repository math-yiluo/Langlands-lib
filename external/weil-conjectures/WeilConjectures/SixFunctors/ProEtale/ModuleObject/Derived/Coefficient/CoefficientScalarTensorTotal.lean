/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorSummand
/-! # Signed totalization of the scalar tensor square

The ordinary scalar tensor square extends to unbounded signed direct-sum total
complexes by checking every coproduct summand.
(blueprint: lem-sfb-coefficient-scalar-tensor-total)
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
  Mod.extendScalars Mod.comap internalScalarExtension
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  Localization.Monoidal.tensorBifunctor

-- Keep prolongation functors transparent during implicit object matching.

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

-- Normalize the four functor images of each total-complex summand.
/-- The ordinary scalar tensor square commutes after signed direct-sum totalization.
Source: Stacks Project, Cohomology on Sites, Tag 07A4.
In degree n, test the maps on each coproduct summand indexed by p+q=n.
The internal and section total tensor maps restrict to their ordinary tensorators.
The equivalence comparison restricts to its ordinary comparison and the termwise
scalar comparison restricts to its component in degrees p and q. Thus the square
on each summand is exactly the ordinary scalar tensor square. Coproduct
universality gives equality in every degree, hence equality of chain maps.
(blueprint: lem-sfb-coefficient-scalar-tensor-total). -/
theorem coefficientScalarTensor_total (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d)
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    let := internalScalarMonoidal a Z
    let F := Mod.extendScalars (coefficientMap a Z)
    let ER := (ModuleRingedComparison.equivalence R Z).functor
    let ES := (ModuleRingedComparison.equivalence S Z).functor
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let ERc := ER.mapHomologicalComplex (.up ℤ)
    let ESc := ES.mapHomologicalComplex (.up ℤ)
    let Bc := d.b.extension.mapHomologicalComplex (.up ℤ)
    let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex d.o (.up ℤ)
    ESc.map (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) ≫
      (ModuleRingedComparison.totalComparison S Z (Fc.obj P) (Fc.obj Q)).hom ≫
        (o.hom.app P ⊗ₘ o.hom.app Q) =
    o.hom.app (P ⊗ Q) ≫ Bc.map (ModuleRingedComparison.totalComparison R Z P Q).hom ≫
      coefficientSectionScalarTotal a Z d.b d.m (ERc.obj P) (ERc.obj Q) := by
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
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleRingedComparison.internalModules R Z))
    (c := ComplexShape.up ℤ) (j := n) (F ⋙ ES)
  intro p q hpq
  simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.comp_map] using
    coefficientScalarTensor_summand a Z d h P Q p q n hpq

end AlgebraicGeometry.ProEtale.CondensedRing
