/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # CompactSupportScalarExtensionLaws

A proved generic calculation for the compact-support finite action.
(blueprint: lem-weil-compact-support-scalar-extension-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace WeilConjectures

/-- The base-changed map sends a pure tensor a tensor f to a tensor F(f).
Source: blueprint lem-fix-operation-reduction.proof.md, final paragraph;
finite-action proof step 2, scalar extension of Hom maps.
(blueprint: lem-weil-compact-support-scalar-extension-laws).
Proof: The base-changed map sends a pure tensor a tensor f to a tensor F(f).
The identity equation is the functor identity law. For composition, induct on
both tensor factors, use the prescribed bilinear composition formula on pure
tensors and the functor composition law, then use additivity. -/
theorem compactSupportScalarExtensionLaws
    {R : Type*} [CommRing R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (p : R) (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (∀ K : C, (F.mapLinearMap R).baseChange (Localization.Away p)
      ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) = (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (a : Localization.Away p ⊗[R] (K ⟶ L))
        (b : Localization.Away p ⊗[R] (L ⟶ M)),
      (F.mapLinearMap R).baseChange (Localization.Away p)
        (ScalarLocalization.composition R C p K L M b a) =
      ScalarLocalization.composition R D p (F.obj K) (F.obj L) (F.obj M)
        ((F.mapLinearMap R).baseChange (Localization.Away p) b)
        ((F.mapLinearMap R).baseChange (Localization.Away p) a)) := by
  constructor
  · intro K
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 K) = _
    rw [F.map_id]
  · intro K L M a b
    induction b using TensorProduct.inductionOn with
    | tmul b g =>
      induction a using TensorProduct.inductionOn with
      | tmul a h =>
        rw [ScalarLocalization.composition_tmul]
        change (b * a) ⊗ₜ[R] F.map (h ≫ g) =
          ScalarLocalization.composition R D p (F.obj K) (F.obj L) (F.obj M)
            (b ⊗ₜ[R] F.map g) (a ⊗ₜ[R] F.map h)
        rw [ScalarLocalization.composition_tmul, F.map_comp]
      | add a a' ha ha' => simp [map_add, ha, ha']
    | add b b' hb hb' => simp [map_add, hb, hb']

end WeilConjectures
