/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase

/-! # Uniqueness of the rational normalized partial closed datum

Source: Stacks Project, Tag 08J9; the rational localization step in the
blueprint `lem-pod-derived-automorphism-hom-evaluation`.
(blueprint: lem-pod-rational-closed-uniqueness)

Pure tensors generate the localized Hom groups. Equality on the prescribed
pure-tensor inverse transposes therefore determines every transpose, and
`podPartialClosed_ext` turns equality of those transposes into equality of the
partial closed data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem localized_addHom_ext
    {R : Type*} [CommRing R] {A : Type*} [Category* A]
    [Preadditive A] [Linear R A] (p : R)
    (L X : ScalarLocalization R A p) (X₀ : A) (hX : X = ⟨X₀⟩)
    {M : Type*} [AddCommGroup M] (f g : (L ⟶ X) →+ M)
    (h : ∀ (a : Localization.Away p) (m : L.obj ⟶ X₀) (q : L ⟶ X),
      HEq q (a ⊗ₜ[R] m) → f q = g q) : f = g := by
  cases hX
  apply AddMonoidHom.ext
  intro q
  induction q using TensorProduct.inductionOn with
  | tmul a m => exact h a m _ HEq.rfl
  | add q q' hq hq' => simp only [map_add, hq, hq']

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- Two rational partial closed data satisfying the pure-tensor normalization
are equal. This is the uniqueness part of `podRationalClosed_existsUnique`.
Source: Stacks Project, Tag 08J9; the assigned localization normalization in
`lem-pod-derived-automorphism-hom-evaluation` (agent refinement of coefficient transport).
Proof: the recorded rational Hom object equals the unchanged integral Hom
object. Transport along this equality and induct on its tensor-product Hom
module. The normalization makes the two inverse transposes equal on every
pure tensor; additivity gives equality on zero and sums. Injectivity of the
inverse equivalences then gives equality of the forward transposes. Apply
`podPartialClosed_ext`; its naturality fields are propositions.
(blueprint: lem-pod-rational-closed-uniqueness). -/
theorem podRationalClosed_unique
    (S S' : PodPartialClosed (rationalDerivedTensor l E W)
      (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W))
    (hS : ∀ (L : sfRationalConstructibleCategory l E W)
      (P : (constructibleRationalHomPairs l E W).FullSubcategory)
      (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
        (integralPairOfRationalHomPair l E W P))
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
      HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
      HEq ((S.transpose L P).symm q)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          ((podIntegralClosed l E W).transpose L.obj
            (integralPairOfRationalHomPair l E W P)).symm f))
    (hS' : ∀ (L : sfRationalConstructibleCategory l E W)
      (P : (constructibleRationalHomPairs l E W).FullSubcategory)
      (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
        (integralPairOfRationalHomPair l E W P))
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
      HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
      HEq ((S'.transpose L P).symm q)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          ((podIntegralClosed l E W).transpose L.obj
            (integralPairOfRationalHomPair l E W P)).symm f)) :
    S = S' := by
  apply podPartialClosed_ext
  intro L P
  have hi : (S.transpose L P).symm.toAddMonoidHom =
      (S'.transpose L P).symm.toAddMonoidHom := by
    apply localized_addHom_ext (Padic.coefficientExtensionUniformizer l E) L
      ((rationalDerivedInternalHom l E W).obj P)
      ((constructibleIntegralHom l E W).obj (integralPairOfRationalHomPair l E W P))
      ((rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec.1 P)
    intro a f q hq
    exact eq_of_heq ((hS L P f a q hq).trans (hS' L P f a q hq).symm)
  apply AddEquiv.ext
  intro f
  apply (S'.transpose L P).symm.injective
  rw [AddEquiv.symm_apply_apply]
  exact (DFunLike.congr_fun hi _).symm.trans ((S.transpose L P).symm_apply_apply f)

end WeilConjectures
