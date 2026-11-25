/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingSourceChainSquare
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingSourceLeftNormalization
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingSourceRightNormalization

/-! # The source-shift square on localized representatives

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X and 08JA.
Two separate normalization calculations reduce the derived square to the proved
signed source chain square.
(blueprint: lem-pod-reindexing-source-shift-model)
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

attribute [local irreducible] sourceModelInput sourceModelOutput podReindexingHomModel
  derivedInternalHomOfUniverses homComplexFunctor CategoryTheory.RingedHomUniverses.sourceShift
  complexShift

-- The two normalized derived composites have dependent localization endpoints.
set_option linter.unusedVariables false in
/-- The normalized source-shift square on a source complex and a K-injective
target complex after localization.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
Proof: expand `Comparison.derived_model` at the localized source and target,
use `LeftNormalization` to identify the source-shift arrow, and compare every
Hom-product projection using `Comparison.chain_projection`.  The resulting
chain equality is localized and the comparison and localization isomorphisms
are cancelled.  This is strictly the representative part of the arbitrary
object square; its extension to all derived objects is the separate descent
theorem.
(blueprint: lem-pod-reindexing-source-shift-model) -/
theorem derived_source_shift_model
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∀ (P I : K l E Y s) (hI : I.IsKInjective) (a : ℤ),
      c.derived.hom.app
          (op (((podReindexingQ l E Y s).obj P)⟦a⟧),
            (podReindexingQ l E Y s).obj I) ≫
        (podReindexingDerivedHom l E X s).map
            (Prod.mkHom
            (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app
              ((podReindexingQ l E Y s).obj P)).op
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj
              ((podReindexingQ l E Y s).obj I)))) ≫
        (CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
          (ProEt.topology X) (podReindexingRing l E X s)
          ((podReindexingDerivedFunctor l E g s).obj
            ((podReindexingQ l E Y s).obj P)) a).inv.app
              ((podReindexingDerivedFunctor l E g s).obj
                ((podReindexingQ l E Y s).obj I)) =
      (podReindexingDerivedFunctor l E g s).map
        ((CategoryTheory.RingedHomUniverses.sourceShift.{u + 1, u, u, u + 2}
          (ProEt.topology Y) (podReindexingRing l E Y s)
          ((podReindexingQ l E Y s).obj P) a).inv.app
            ((podReindexingQ l E Y s).obj I)) ≫
        ((podReindexingDerivedFunctor l E g s).commShiftIso (-a)).hom.app
          ((podReindexingDerivedHom l E Y s).obj
            (op ((podReindexingQ l E Y s).obj P), (podReindexingQ l E Y s).obj I)) ≫
        (c.derived.hom.app
          (op ((podReindexingQ l E Y s).obj P), (podReindexingQ l E Y s).obj I))⟦-a⟧' := by
  intro P I hI a
  let _ := hI
  obtain ⟨hFI, _⟩ := c.derived_model P I hI
  let _ := hFI
  let _ := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E Y s)
  let _ := HasDerivedCategory.standard.{u + 1, u + 2} (podReindexingModules l E X s)
  obtain ⟨eY, hY, _⟩ :=
    (CategoryTheory.RingedHomUniverses.leftShift_existsUnique.{u + 1, u, u, u + 2}
      (ProEt.topology Y) (podReindexingRing l E Y s)).exists.choose_spec
      ((podReindexingQ l E Y s).obj P) P I (Iso.refl _) a
  obtain ⟨eX, hX, _⟩ :=
    (CategoryTheory.RingedHomUniverses.leftShift_existsUnique.{u + 1, u, u, u + 2}
      (ProEt.topology X) (podReindexingRing l E X s)).exists.choose_spec
      ((podReindexingQ l E X s).obj ((podReindexingComplexFunctor l E g s).obj P))
      ((podReindexingComplexFunctor l E g s).obj P)
      ((podReindexingComplexFunctor l E g s).obj I) (Iso.refl _) a
  apply (cancel_epi (sourceModelInput l E g s P I a).hom).mp
  apply (cancel_mono (sourceModelOutput l E g s P I a).hom).mp
  have hL := source_left_normalization l E g s SX SY TX TY c P I a eX hX
  have hR := source_right_normalization l E g s SX SY TX TY c P I a eY hY
  have hC := congrArg
    (fun f ↦ (podReindexingDerivedFactors l E g s).hom.app (hom l E Y s (P⟦a⟧) I) ≫
      (podReindexingQ l E X s).map f ≫
      ((podReindexingQ l E X s).commShiftIso (-a)).hom.app
        (hom l E X s ((podReindexingComplexFunctor l E g s).obj P)
          ((podReindexingComplexFunctor l E g s).obj I)))
    (source_chain_square l E g s SX SY TX TY c P I a eY eX hY hX)
  exact (Category.assoc _ _ _).trans
    (hL.trans (hC.trans (hR.symm.trans (Category.assoc _ _ _).symm)))

end WeilConjectures.PodReindexingCoherence
