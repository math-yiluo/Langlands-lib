/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import all WeilConjectures.SixFunctors.IntegralHom.FiniteTensorPresentationEvaluation
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterAdjunction

/-! # Target and comparison components of an integral reduction presentation

This isolates the target tensor presentation and its derived comparison from the
normalization field of `ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-target).
(blueprint: lem-sf-integral-hom-models-exist-reduction-components).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The finite-level target tensor presentation exists.

Source: Stacks Tags 07A4 and 07A6; blueprint order 2478, proof step 3.
Proof: obtain the generic closed symmetric monoidal structure, its tensor
comparison, and its representative Koszul symmetry. The braided left-tensor
adjunction is natural in its tensor parameter; its counit is the braiding followed
by the native counit. The finite evaluation argument for exactly that counit gives
the required sectionwise and derived evaluation equations. These are exactly the
fields of `TensorPresentation`.
-/
theorem reduction_target_exists
    (n : ℕ) :
    Nonempty (TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) := by
  classical
  letI : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  letI : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  obtain ⟨S, T, β, ⟨hcoh⟩⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal.{t + 1, t, u,
      (max u (t + 1)) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)
  let adj := leftTensorParameterAdjunction S β
  exact ⟨TensorPresentation.mk S.tensor T.comparison adj
    (evaluation_for_adj Y (integralCoefficientCommRingSheaf l E Y n) S T β adj.adj
      (fun _ _ ↦ rfl) hcoh.symmetry_model)⟩

end WeilConjectures.IntegralHom
