/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorFamilyIdentityComposition
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorFamilyTensorConstraints

/-! # Coherence of fixed normalized completion and tensor families

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-family-coherence). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Section-normalized identity and composition for fixed normalized comparisons.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL and 07A4 (blueprint: lem-pod-reindexing-tensor-family-coherence).

Proof: use Over.mapId and Over.mapComp on each original local section to define
identity and composition of ordinary relabelling. These are module maps because
the completed coefficient maps agree after every quotient projection; limit
extensionality gives their coefficient equality. Reverse site transports give
the inverses. Thus the displayed Relabelling equations hold by construction.
On strict quotient complexes, both reduction routes send p tensor b to the same
relabeled generator. The limit routes are the same diagonal maps on both Roos
coordinates, by the coordinate and restricted-system laws of completion.
Localize these equalities to obtain the reduction and limit parts of Identity
and Composition. For tensors apply Generators and Model: on homogeneous triples
both associator paths send (x tensor y) tensor z to x tensor (y tensor z), and
both symmetry paths multiply Fy tensor Fx by (-1)^(pq). The coefficient unit is
sent to the coefficient unit; multiplication on tensors gives both unitors.
These are equalities of full strict systems and of both Roos coordinates.
Naturality and the representative models descend them to the specified derived
maps. No choice of new completion or tensor comparisons occurs. The identity,
empty-scheme and zero-input cases use the same section formulas. -/
theorem podReindexingTensorFamilyCoherence
    (completion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)], PodCompletionReindex l E f)
    (tensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex l E f (completion f))
    (hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (completion f))
    (htensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (completion f) (tensor f)) :
    ∃ identity : ∀ W : Scheme.{u}, isoReductionIntegralInverse l E (𝟙 W) ≅ 𝟭 _,
    ∃ composition : ∀ {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V)
      [IsIso h] [IsIso f], isoReductionIntegralInverse l E (h ≫ f) ≅
        isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h,
      let A : PodReindexFamily l E := ⟨completion, tensor, identity, composition⟩
      A.Relabelling l E ∧ A.Identity l E ∧ A.Composition l E ∧
        ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
          [∀ v : V, Invertible (l : V.residueField v)]
          [∀ w : W, Invertible (l : W.residueField w)], A.TensorConstraints l E f := by
  obtain ⟨identity, composition, hR, hI, hC⟩ :=
    podReindexingTensorFamilyIdentityComposition l E completion tensor hcompletion htensor
  refine ⟨identity, composition, ?_⟩
  let A : PodReindexFamily l E := ⟨completion, tensor, identity, composition⟩
  dsimp [A]
  refine ⟨hR, hI, hC, ?_⟩
  intro V W f _ _ _
  exact podReindexingTensorFamilyTensorConstraints l E completion tensor hcompletion htensor
    identity composition (V := V) (W := W) f

end WeilConjectures
