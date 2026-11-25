/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeEquation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeLeftPath
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization

/-! # Pasting the scalar tensor representative diagram

This is the categorical step after the three scalar complex comparison equations
have been established. No K-flatness or termwise flatness is needed in this step.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-pasting)
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
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

-- Match native prolongations before reducing concrete section constructions.
attribute [local irreducible] HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

attribute [local irreducible] coefficientInternalScalarComplex
  coefficientSectionScalarTotal SheafOfModules.scalarPairComplexComparison
  internalScalarTensorComparison

-- Check the normalized comparison diagram without unfolding its functors.
/-- Paste the scalar comparison equations on two complexes and their tensor.
Source: Stacks Project, Cohomology on Sites, Tag 07A4.
Normalize qTensor on each reconstructed pair. Scalar-comparison naturality and
its three assumed comparison equations turn the totalized ordinary square into
the internal derived tensor counit square. Naturality of the tensor comparison
and of qTensor moves the two factor comparisons past tensor and localization.
The assumed derived tensor square then closes the diagram. Cancel the composite
of the derived scalar, tensor and localization comparison isomorphisms.
This step requires the three scalar equations, without any flatness assumptions.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-pasting). -/
theorem coefficientScalarTensorRepresentative_paste
    (Z : Scheme.{u}) (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d)
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    let F := Mod.extendScalars (coefficientMap a Z)
    let ER := (ModuleRingedComparison.equivalence R Z).functor
    let ES := (ModuleRingedComparison.equivalence S Z).functor
    let ESD := (ModuleRingedComparison.derivedEquivalence S Z).functor
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let ERc := ER.mapHomologicalComplex (.up ℤ)
    let o := NatIso.mapHomologicalComplex d.o (.up ℤ)
    let scalarSquare (K : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :=
      ESD.map (coefficientInternalScalarComplex a Z K) ≫
        ES.mapDerivedCategoryFactors.hom.app (Fc.obj K) ≫
        DerivedCategory.Q.map (o.hom.app K) =
      d.p.hom.app (DerivedCategory.Q.obj K) ≫
        d.b.derived.map (ER.mapDerivedCategoryFactors.hom.app K) ≫
        SheafOfModules.scalarPairComplexComparison d.b.extension d.b.extension_additive
          d.b.derived d.b.counit (ERc.obj K)
    scalarSquare P → scalarSquare Q → scalarSquare (P ⊗ Q) →
      coefficientScalarTensorRepresentativeEquation a Z d (ERc.obj P) (ERc.obj Q) := by
  dsimp only
  intro hsP hsQ hsT
  let := internalScalarMonoidal a Z
  let := d.m
  let := d.b.ordinaryAdjunction.isLeftAdjoint
  let F := Mod.extendScalars (coefficientMap a Z)
  let ER := (ModuleRingedComparison.equivalence R Z).functor
  let ES := (ModuleRingedComparison.equivalence S Z).functor
  let ED := (ModuleRingedComparison.derivedEquivalence R Z).functor
  let ESD := (ModuleRingedComparison.derivedEquivalence S Z).functor
  let B := d.b.extension
  let BD := d.b.derived
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let ESc := ES.mapHomologicalComplex (.up ℤ)
  let Bc := B.mapHomologicalComplex (.up ℤ)
  let EP := ERc.obj P
  let EQ := ERc.obj Q
  let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex d.o (.up ℤ)
  let ℓR : DerivedCategory.Q ⋙ ED ≅ ERc ⋙ DerivedCategory.Q :=
    ER.mapDerivedCategoryFactors
  let ℓS : DerivedCategory.Q ⋙ ESD ≅ ESc ⋙ DerivedCategory.Q :=
    ES.mapDerivedCategoryFactors
  let τR := ModuleRingedComparison.tensorComparison R Z
  let τS := ModuleRingedComparison.tensorComparison S Z
  let tensorR := ModuleRingedComparison.tensor R Z
  let tensorS := ModuleRingedComparison.tensor S Z
  let qR (K L : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
      tensorR.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
        DerivedCategory.Q.obj (K ⊗ L) := (ModuleRingedComparison.qTensor R Z).app (K, L)
  let qS (K L : CochainComplex (ModuleRingedComparison.modules S Z) ℤ) :
      tensorS.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
        DerivedCategory.Q.obj (K ⊗ L) := (ModuleRingedComparison.qTensor S Z).app (K, L)
  let c := fun K ↦ coefficientInternalScalarComplex a Z K
  let β := fun K ↦ SheafOfModules.scalarPairComplexComparison B d.b.extension_additive
    BD d.b.counit K
  let δb : Bc.obj (EP ⊗ EQ) ⟶ Bc.obj EP ⊗ Bc.obj EQ :=
    coefficientSectionScalarTotal a Z d.b d.m EP EQ
  have hleft := coefficientScalarTensorRepresentative_leftPath a Z d h P Q hsT
  have htens := h.htensor (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
  have htnat := d.t.hom.naturality
    (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))
  simp only [Functor.comp_map, Functor.prod_map] at htnat
  have hpair :
      tensorS.map (Prod.mkHom (ESD.map (c P)) (ESD.map (c Q))) ≫
        tensorS.map (Prod.mkHom (ℓS.hom.app (Fc.obj P)) (ℓS.hom.app (Fc.obj Q))) ≫
        tensorS.map (Prod.mkHom (DerivedCategory.Q.map (o.hom.app P))
          (DerivedCategory.Q.map (o.hom.app Q))) =
      tensorS.map (Prod.mkHom (d.p.hom.app (DerivedCategory.Q.obj P))
        (d.p.hom.app (DerivedCategory.Q.obj Q))) ≫
        tensorS.map (Prod.mkHom (BD.map (ℓR.hom.app P)) (BD.map (ℓR.hom.app Q))) ≫
        tensorS.map (Prod.mkHom (β EP) (β EQ)) := by
    exact map_pair_three tensorS hsP hsQ
  let k := d.p.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
    BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
    BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q)))
  change BD.map (qR EP EQ) ≫ β (EP ⊗ EQ) ≫ DerivedCategory.Q.map δb =
    d.t.hom.app (DerivedCategory.Q.obj EP, DerivedCategory.Q.obj EQ) ≫
      tensorS.map (Prod.mkHom (β EP) (β EQ)) ≫ qS (Bc.obj EP) (Bc.obj EQ)
  let e := d.p.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≪≫
    BD.mapIso (τR.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≪≫
    BD.mapIso (tensorR.mapIso (Iso.prod (ℓR.app P) (ℓR.app Q)))
  have he : e.hom = k := rfl
  apply cancel_iso_path e he
  dsimp only [k]
  simp only [Category.assoc]
  exact paste_representative_right
    (a := d.p.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q))
    (b := BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    (c := BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))))
    (d := BD.map (qR EP EQ)) (e := β (EP ⊗ EQ)) (f := DerivedCategory.Q.map δb)
    hleft hpair htens htnat

end AlgebraicGeometry.ProEtale.CondensedRing
