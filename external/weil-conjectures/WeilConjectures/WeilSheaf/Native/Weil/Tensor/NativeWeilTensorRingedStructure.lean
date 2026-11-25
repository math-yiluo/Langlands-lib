/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridge
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-! # The explicit native monoidal structure transported from a ringed presentation

Source: Stacks 0FPT and transport along an equivalence of abelian categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]

/-- Lift the specified native additive equivalence to the actual derived categories.
Source: localization of equivalences; Stacks 06YS.
(blueprint: def-sf-native-weil-tensor-ringed-structure). -/
def nativeWeilRingedDerivedEquivalence :
    DerivedCategory (ProEtaleWeilSheaf k₀ l X) ≌
      DerivedCategory (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) :=
  letI : b.native.inverse.Additive := b.native.inverse_additive
  b.native.mapDerivedCategory

variable (SB : CoefficientClosedStructure
  (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))

/-- Transport the given ringed monoidal structure, without any choice of a witness.
Source: equivalence transport of monoidal categories; Stacks 0FPT.
(blueprint: def-sf-native-weil-tensor-ringed-structure). -/
@[instance_reducible]
def nativeWeilRingedMonoidal : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  letI := SB.monoidal
  Monoidal.transport (nativeWeilRingedDerivedEquivalence b).symm

/-- Transport the given symmetry on that explicit monoidal structure.
Source: equivalence transport of symmetric categories; Stacks 0FPT.
(blueprint: def-sf-native-weil-tensor-ringed-structure). -/
@[instance_reducible]
def nativeWeilRingedSymmetric (βB : @SymmetricCategory _ _ SB.monoidal) :
    @SymmetricCategory _ _ (nativeWeilRingedMonoidal b SB) :=
  letI := SB.monoidal
  letI := βB
  inferInstanceAs (SymmetricCategory
    (Monoidal.Transported (nativeWeilRingedDerivedEquivalence b).symm))

/-- The transported coefficient unit is the original native coefficient module in degree zero.
Source: the coefficient unit in ringed tensor coherence, and exact forgetting of singles.
(blueprint: def-sf-native-weil-tensor-ringed-structure). -/
def nativeWeilRingedUnit
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB) :
    (nativeWeilRingedMonoidal b SB).tensorUnit ≅
      (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X) := by
  letI : b.native.inverse.Additive := b.native.inverse_additive
  let η : b.native.inverse.obj
      (SheafOfModules.unit ((sheafCompose b.J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj b.R)) ≅
        adicConstant k₀ l X :=
    b.native.inverse.mapIso b.nativeUnit.symm ≪≫
      (b.native.unitIso.app (adicConstant k₀ l X)).symm
  exact b.native.inverse.mapDerivedCategory.mapIso cB.unitIso ≪≫
    (Functor.mapDerivedCategorySingleFunctor b.native.inverse 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso η

end AlgebraicGeometry.ProEtaleWeilSheaf
