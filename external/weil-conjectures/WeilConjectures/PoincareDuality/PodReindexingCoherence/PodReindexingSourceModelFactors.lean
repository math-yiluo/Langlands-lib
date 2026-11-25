/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData

/-! # Isomorphisms identifying the source-shift Hom models

These are composites of the recorded localization and Hom model isomorphisms.
Source: Stacks 0A8X, 08JA; blueprint dual-Tate compatibility, Step 4.
(blueprint: def-pod-reindexing-source-model-factors)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The source model and the localization source-shift comparison.
Source: Stacks 0A8X and 08JA.
(blueprint: def-pod-reindexing-source-model-factors) -/
def sourceModelInput
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (P I : K l E Y s) (a : ℤ) [I.IsKInjective] :
    (podReindexingDerivedFunctor l E g s).obj
        ((podReindexingQ l E Y s).obj (hom l E Y s (P⟦a⟧) I)) ≅
      (podReindexingDerivedFunctor l E g s).obj
        ((podReindexingDerivedHom l E Y s).obj
          (op (((podReindexingQ l E Y s).obj P)⟦a⟧), (podReindexingQ l E Y s).obj I)) :=
  letI := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  (podReindexingDerivedFunctor l E g s).mapIso
    ((podReindexingHomModel l E Y s (P⟦a⟧) I).symm ≪≫
      (podReindexingDerivedHom l E Y s).mapIso
        (((DerivedCategory.Q.commShiftIso a).app P).symm.op.prod
          (Iso.refl ((podReindexingQ l E Y s).obj I))))

/-- The target model isomorphism, shifted by the negative source degree.
Source: Stacks 0A8X and 08JA.
(blueprint: def-pod-reindexing-source-model-factors) -/
def sourceModelOutput
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (P I : K l E Y s) (a : ℤ)
    [CochainComplex.IsKInjective ((podReindexingComplexFunctor l E g s).obj I)] :
    ((podReindexingDerivedHom l E X s).obj
        (op ((podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj P)),
          (podReindexingDerivedFunctor l E g s).obj ((podReindexingQ l E Y s).obj I)))⟦-a⟧ ≅
      ((podReindexingQ l E X s).obj
        (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I)))⟦-a⟧ :=
  (shiftFunctor _ (-a)).mapIso
    ((podReindexingDerivedHom l E X s).mapIso
      (((podReindexingDerivedFactors l E g s).app P).symm.op.prod
        ((podReindexingDerivedFactors l E g s).app I)) ≪≫
      podReindexingHomModel l E X s ((podReindexingComplexFunctor l E g s).obj P)
        ((podReindexingComplexFunctor l E g s).obj I))

end WeilConjectures.PodReindexingCoherence
