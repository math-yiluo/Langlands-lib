/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorTotal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization

/-! # The localized scalar total tensor path

This normalizes the scalar path using the ordinary signed total tensor square.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-total-path)
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

private theorem scalar_natural (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    {P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ} (f : P ⟶ Q) :
    d.b.derived.map (DerivedCategory.Q.map f) ≫
      SheafOfModules.scalarPairComplexComparison d.b.extension d.b.extension_additive
        d.b.derived d.b.counit Q =
    SheafOfModules.scalarPairComplexComparison d.b.extension d.b.extension_additive
        d.b.derived d.b.counit P ≫
      DerivedCategory.Q.map ((d.b.extension.mapHomologicalComplex (.up ℤ)).map f) := by
  unfold SheafOfModules.scalarPairComplexComparison
  have h₁ (K : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
      (DerivedCategory.quotientCompQhIso _).inv.app K = 𝟙 _ := rfl
  have h₂ (K : CochainComplex (ModuleRingedComparison.modules S Z) ℤ) :
      (DerivedCategory.quotientCompQhIso _).hom.app K = 𝟙 _ := rfl
  erw [h₁, h₁, h₂, h₂]
  erw [d.b.derived.map_id _, d.b.derived.map_id _]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]
  exact d.b.counit.naturality ((HomotopyCategory.quotient _ (.up ℤ)).map f)

private theorem paste_total_path {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G H I J J₀ K L M N P : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : D ⟶ E}
    {e : E ⟶ F} {f : F ⟶ G} {g : A ⟶ H} {h : H ⟶ I}
    {i : B ⟶ I} {j : I ⟶ J} {k : J ⟶ E} {l : J ⟶ J₀}
    {m₀ : J₀ ⟶ F} {m : H ⟶ K} {n : K ⟶ L} {o : L ⟶ J₀}
    {p : L ⟶ M} {q : M ⟶ N} {r : N ⟶ G} {s : K ⟶ P} {t : P ⟶ M}
    (hfac : b ≫ c ≫ d = i ≫ j ≫ k) (hnat : k ≫ e = l ≫ m₀)
    (hp : g ≫ h = a ≫ i) (hscalar : m ≫ n ≫ o = h ≫ j ≫ l)
    (htotal : p ≫ q ≫ r = o ≫ m₀ ≫ f) (hlocal : s ≫ t = n ≫ p) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = g ≫ m ≫ s ≫ t ≫ q ≫ r := by
  rw [reassoc_of% hfac, reassoc_of% hnat, ← reassoc_of% hp,
    ← reassoc_of% hscalar, ← htotal, ← reassoc_of% hlocal]

attribute [local irreducible] coefficientInternalScalarComplex
  coefficientSectionScalarTotal SheafOfModules.scalarPairComplexComparison
  internalScalarTensorComparison

-- Compare the scalar and localization paths on the signed total tensor.
/-- Normalize the scalar path through the localized signed total tensor.
Source: Stacks Project, Cohomology on Sites, Tags 06YU and 07A4.
Normalize the reconstructed localization tensor by its defining conjugation.
Naturality of the scalar counit moves the total comparison past the counit.
Use the scalar comparison on the single complex P tensor Q, and then the signed
ordinary scalar tensor square. Naturality of the localization comparison gives
the displayed path through the internal scalar extension of the total tensor.
No derived scalar tensor comparison, nor factor scalar equation, is used here.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-total-path). -/
theorem coefficientScalarTensorRepresentative_totalPath
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
    let tensorR := ModuleRingedComparison.tensor R Z
    let qR (K L : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
        tensorR.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ⟶
          DerivedCategory.Q.obj (K ⊗ L) := (ModuleRingedComparison.qTensor R Z).app (K, L)
    let c := fun K ↦ coefficientInternalScalarComplex a Z K
    let β := fun K ↦ SheafOfModules.scalarPairComplexComparison B d.b.extension_additive
      BD d.b.counit K
    let δb : Bc.obj (EP ⊗ EQ) ⟶ Bc.obj EP ⊗ Bc.obj EQ :=
      coefficientSectionScalarTotal a Z d.b d.m EP EQ
    let μR : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q ⟶
        DerivedCategory.Q.obj (P ⊗ Q) :=
      (ModuleRingedComparison.internalLocalizationTensorMap R Z).app (P, Q)
    let δ : Fc.obj (P ⊗ Q) ⟶ Fc.obj P ⊗ Fc.obj Q :=
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
    (ESD.map (c (P ⊗ Q)) ≫ ℓS.hom.app (Fc.obj (P ⊗ Q)) ≫
        DerivedCategory.Q.map (o.hom.app (P ⊗ Q)) =
      d.p.hom.app (DerivedCategory.Q.obj (P ⊗ Q)) ≫
        BD.map (ℓR.hom.app (P ⊗ Q)) ≫ β (ERc.obj (P ⊗ Q))) →
    d.p.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
      BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))) ≫
      BD.map (qR EP EQ) ≫ β (EP ⊗ EQ) ≫ DerivedCategory.Q.map δb =
    ESD.map ((internalScalarExtension a Z).map μR) ≫
      ESD.map (c (P ⊗ Q)) ≫ ESD.map (DerivedCategory.Q.map δ) ≫
      ℓS.hom.app (Fc.obj P ⊗ Fc.obj Q) ≫
      DerivedCategory.Q.map (ModuleRingedComparison.totalComparison S Z
        (Fc.obj P) (Fc.obj Q)).hom ≫
      DerivedCategory.Q.map (o.hom.app P ⊗ₘ o.hom.app Q) := by
  intro instF instB instBadj F ER ES ED ESD B BD Fc ERc ESc Bc EP EQ o
    ℓR ℓS τR tensorR qR c β δb μR δ hsT
  let r : ERc.obj (P ⊗ Q) ≅ EP ⊗ EQ := ModuleRingedComparison.totalComparison R Z P Q
  have hfR := coefficientTensor_localization R Z P Q
  have hn := scalar_natural a Z d r.hom
  have htot := congrArg (DerivedCategory.Q.map)
    (coefficientScalarTensor_total a Z d h P Q)
  simp only [Functor.map_comp] at htot
  have hpμ := d.p.hom.naturality μR
  have hℓδ := ℓS.hom.naturality δ
  simp only [Functor.comp_map] at hpμ hℓδ
  have hfacR := congrArg (BD.map) hfR
  simp only [Functor.map_comp] at hfacR
  exact paste_total_path
    (a := d.p.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q))
    (b := BD.map (τR.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    (c := BD.map (tensorR.map (Prod.mkHom (ℓR.hom.app P) (ℓR.hom.app Q))))
    (d := BD.map (qR EP EQ)) (e := β (EP ⊗ EQ)) (f := DerivedCategory.Q.map δb)
    hfacR hn hpμ hsT htot hℓδ

end AlgebraicGeometry.ProEtale.CondensedRing
