/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreTensorData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingTensorChainNaturality

import all WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! The explicit tensor comparison on the K-flat presentation.
(blueprint: lem-pod-reindexing-tensor-presentation-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local instance 1000001] cachedCompose

namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] podReindexingCoefficient podReindexingHomModel
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientTotalTensor coefficientTensorGenerator SheafOfModules.monoidalCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors
  CoefficientClosedStructure.tensor

set_option allowUnsafeReducibility true in
attribute [local irreducible] podReindexingDerivedFunctor podReindexingDerivedFactors

/-- The actual complex reindexing functor restricted to K-flat complexes.
Its object property is the existing resolution-preservation theorem.
(blueprint: lem-pod-reindexing-tensor-presentation-comparison). -/
def tensorKFlatReindexing {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) :
    ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology Y) (R := podReindexingRing l E Y s)) ⥤
    ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := podReindexingRing l E X s)) :=
  ObjectProperty.lift _
    (coefficientKFlatInclusion.{u, u + 1, u} (ProEt.topology Y)
      (podReindexingRing l E Y s) ⋙ podReindexingComplexFunctor l E g s)
    (fun P ↦
      (podReindexing_resolution_preservation.{u, 0, 0} l E g s).2.2.2.2.2.2.2.1 P.obj P.property)

private theorem iso_composite_with_components {C₁ C₂ D : Type*}
    [Category* C₁] [Category* C₂] [Category* D] {A B C' D' : C₁ × C₂ ⥤ D}
    (a : A ≅ B) (b : B ≅ C') (c : C' ≅ D') :
    ∃ e : A ≅ D', ∀ P Q, e.hom.app (P, Q) =
      a.hom.app (P, Q) ≫ b.hom.app (P, Q) ≫ c.hom.app (P, Q) :=
  ⟨a ≪≫ b ≪≫ c, fun _ _ ↦ rfl⟩

/-- The explicit comparison on K-flat representatives, before localization descent.
Source: blueprint dual-Tate compatibility, Steps 1 and 2.
(blueprint: lem-pod-reindexing-tensor-presentation-comparison).

Proof: first apply the localization factorization to the total complex, then the
localized natural chain comparison, and finally the recorded target tensor model.
The chain comparison is natural by its pure normalization. Evaluating this
composite gives exactly the stated formula. All constructions are explicit.
-/
theorem tensor_presentation_comparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (t : ComparisonCoreTensorData l E g s SX SY TX TY) :
    let K := coefficientKFlatInclusion.{u, u + 1, u}
      (ProEt.topology Y) (podReindexingRing l E Y s)
    let KX := coefficientKFlatInclusion.{u, u + 1, u}
      (ProEt.topology X) (podReindexingRing l E X s)
    let F := tensorKFlatReindexing l E g s
    let LX := KX ⋙ podReindexingQ l E X s
    ∃ e : (((K.prod K) ⋙ total l E Y s) ⋙ podReindexingQ l E Y s) ⋙
          podReindexingDerivedFunctor l E g s ≅
        ((F ⋙ LX).prod (F ⋙ LX)) ⋙ SX.tensor,
      ∀ P Q, e.hom.app (P, Q) =
        (podReindexingDerivedFactors l E g s).hom.app
            ((total l E Y s).obj (P.obj, Q.obj)) ≫
          (podReindexingQ l E X s).map (t.tensorChain P.obj Q.obj).hom ≫
          TX.comparison.hom.app (F.obj P, F.obj Q) := by
  let K := coefficientKFlatInclusion.{u, u + 1, u}
    (ProEt.topology Y) (podReindexingRing l E Y s)
  let F := tensorKFlatReindexing l E g s
  let α := podReindexingDerivedFactors l E g s
  let R := podReindexingComplexFunctor l E g s
  let γ : total l E Y s ⋙ R ≅ (R.prod R) ⋙ total l E X s :=
    NatIso.ofComponents (fun P ↦ t.tensorChain P.1 P.2)
      (fun f ↦ tensor_chain_naturality l E g s SX SY TX TY t f.1 f.2)
  exact iso_composite_with_components
    (Functor.isoWhiskerLeft ((K.prod K) ⋙ total l E Y s) α)
    (Functor.isoWhiskerLeft (K.prod K)
      (Functor.isoWhiskerRight γ (podReindexingQ l E X s)))
    (Functor.isoWhiskerLeft (F.prod F) TX.comparison)

end WeilConjectures.PodReindexingCoherence
