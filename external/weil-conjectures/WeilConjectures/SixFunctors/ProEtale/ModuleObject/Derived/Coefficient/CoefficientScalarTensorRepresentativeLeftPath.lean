/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorInternalComplex
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeTotalPath

/-! # The localized left scalar tensor path

This is the first half of the representative diagram, before using the two factor
scalar equations and the assumed derived tensor square.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-left-path)
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

private theorem paste_internal_path {𝒞 : Type*} [Category 𝒞]
    {A G H K M N O P U U₀ V X Y : 𝒞}
    {l : A ⟶ G} {g : A ⟶ H} {m : H ⟶ K} {s : K ⟶ P}
    {t : P ⟶ M} {q : M ⟶ N} {r : N ⟶ G}
    {u : A ⟶ U} {v : U ⟶ O} {w : O ⟶ P} {x : O ⟶ V}
    {y : V ⟶ X} {z : X ⟶ N} {τ : U ⟶ U₀} {aa : U₀ ⟶ V}
    {ab : X ⟶ Y} {ac : Y ⟶ G}
    (hl : l = g ≫ m ≫ s ≫ t ≫ q ≫ r)
    (hi : g ≫ m ≫ s = u ≫ v ≫ w)
    (hf : x ≫ y ≫ z = w ≫ t ≫ q)
    (ht : v ≫ x = τ ≫ aa) (hq : ab ≫ ac = z ≫ r) :
    l = u ≫ τ ≫ aa ≫ y ≫ ab ≫ ac := by
  rw [hl, reassoc_of% hi, ← reassoc_of% hf, reassoc_of% ht, ← hq]

attribute [local irreducible] coefficientInternalScalarComplex
  coefficientSectionScalarTotal SheafOfModules.scalarPairComplexComparison
  internalScalarTensorComparison

-- Compare the native totalization and localization morphisms.
/-- Identify the scalar tensor representative's left path after comparison.
Source: Stacks Project, Cohomology on Sites, Tags 06YU and 07A4.
Use the scalar complex comparison only on P tensor Q. Normalize qTensor on both
reconstructed pairs and apply naturality of the scalar counit. The totalized
ordinary square changes scalar extension before tensor into the tensor of the
factor scalar comparisons. The internal derived counit square and naturality of
tensorComparison and qTensor identify the resulting localized path. This proves
the displayed path identity, without the factor scalar equations or htensor.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-left-path). -/
theorem coefficientScalarTensorRepresentative_leftPath
    (Z : Scheme.{u}) (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d)
    (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
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
    (ESD.map (c (P ⊗ Q)) ≫ ℓS.hom.app (Fc.obj (P ⊗ Q)) ≫
        DerivedCategory.Q.map (o.hom.app (P ⊗ Q)) =
      d.p.hom.app (DerivedCategory.Q.obj (P ⊗ Q)) ≫
        BD.map (ℓR.hom.app (P ⊗ Q)) ≫ β (ERc.obj (P ⊗ Q))) →
    d.p.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
      BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))) ≫
      BD.map (qR EP EQ) ≫ β (EP ⊗ EQ) ≫ DerivedCategory.Q.map δb =
    ESD.map (((internalScalarTensorComparison a Z).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      τS.hom.app ((internalScalarExtension a Z).obj (DerivedCategory.Q.obj P),
        (internalScalarExtension a Z).obj (DerivedCategory.Q.obj Q)) ≫
      tensorS.map (Prod.mkHom (ESD.map (c P)) (ESD.map (c Q))) ≫
      tensorS.map (Prod.mkHom (ℓS.hom.app (Fc.obj P)) (ℓS.hom.app (Fc.obj Q))) ≫
      tensorS.map (Prod.mkHom (DerivedCategory.Q.map (o.hom.app P))
        (DerivedCategory.Q.map (o.hom.app Q))) ≫ qS (Bc.obj EP) (Bc.obj EQ) := by
  dsimp only
  intro hsT
  let := internalScalarMonoidal a Z
  let := d.m
  let := d.b.ordinaryAdjunction.isLeftAdjoint
  let F := Mod.extendScalars (coefficientMap a Z)
  let ER := (ModuleRingedComparison.equivalence R Z).functor
  let ES := (ModuleRingedComparison.equivalence S Z).functor
  let ESD := (ModuleRingedComparison.derivedEquivalence S Z).functor
  let B := d.b.extension
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let ESc := ES.mapHomologicalComplex (.up ℤ)
  let Bc := B.mapHomologicalComplex (.up ℤ)
  let o : Fc ⋙ ESc ≅ ERc ⋙ Bc := NatIso.mapHomologicalComplex d.o (.up ℤ)
  let c := fun K ↦ coefficientInternalScalarComplex a Z K
  have ht := coefficientScalarTensorRepresentative_totalPath a Z d h P Q hsT
  have hfS := coefficientTensor_localization S Z (Fc.obj P) (Fc.obj Q)
  have hir := congrArg (ESD.map) (coefficientScalarTensor_internalComplex a Z P Q)
  simp only [Functor.map_comp,
    ← ModuleRingedComparison.internalLocalizationTensorMap_app] at hir
  have htτ := tensor_comparison_natural S Z (c P) (c Q)
  have hqnat := localization_tensor_natural S Z (o.hom.app P) (o.hom.app Q)
  exact paste_internal_path ht hir hfS htτ hqnat

end AlgebraicGeometry.ProEtale.CondensedRing
