/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Hom

/-!
# Traces of the Frobenius on the stalks of a tensor product of Weil sheaves

Under the isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)`
(`AlgebraicGeometry.WeilSheaf.stalkAtTensorObjLinearEquiv`) the Frobenius of the stalk becomes
`φ ↦ F_G ∘ φ ∘ F_{F^∨}⁻¹`. Its trace is `tr F_G · tr F_F`, since `F_{F^∨}⁻¹` is the transpose of
`F_F`. Hence the traces of the powers of the local Frobenius of `F ⊗ G` are the products of those
of `F` and `G`.

## Main results

- `AlgebraicGeometry.WeilSheaf.trace_stalkAt_tensorObj_frobeniusEnd_pow`: the trace of the
  `k`-th power of the Frobenius on a stalk of `F ⊗ G` is the product of those of `F` and `G`.
- `AlgebraicGeometry.WeilSheaf.traceFunction_tensorObj`: the trace function of `F ⊗ G` is the
  product of those of `G` and `F`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section StalkAt

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

/-- The trace of the `k`-th power of the Frobenius on the stalk of `F ⊗ G` at `s` is the product
of the traces on the stalks of `G` and `F`. -/
theorem trace_stalkAt_tensorObj_frobeniusEnd_pow (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (k : ℕ) :
    LinearMap.trace (PadicAlgCl l) _ (((F.tensorObj G hF).stalkAt s m hs).frobeniusEnd ^ k) =
      LinearMap.trace (PadicAlgCl l) _ ((G.stalkAt s m hs).frobeniusEnd ^ k) *
        LinearMap.trace (PadicAlgCl l) _ ((F.stalkAt s m hs).frobeniusEnd ^ k) := by
  rw [FrobeniusModule.trace_frobeniusEnd_pow_eq_mul_of_linearEquiv _ _ _
    (stalkAtTensorObjLinearEquiv s m hs hF G) (stalkAtTensorObjLinearEquiv_frobenius s m hs hF G),
    ← (stalkAtDualEquiv s m hs F hF).trace_frobenius_symm_pow,
    FrobeniusModule.trace_dual_frobenius_symm_pow]

end StalkAt

/-- At a closed point `x`, the trace of the `k`-th power of the local Frobenius of `F ⊗ G` is
the product of those of `G` and `F`. -/
theorem trace_stalk_tensorObj_frobeniusEnd_pow (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (x : X.finitePoints) (k : ℕ) :
    LinearMap.trace (PadicAlgCl l) _ (((F.tensorObj G hF).stalk x).frobeniusEnd ^ k) =
      LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ k) *
        LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^ k) :=
  trace_stalkAt_tensorObj_frobeniusEnd_pow _ _ _ F G hF k

/-- The trace function of `F ⊗ G` is the product of the trace functions of `G` and `F`. -/
theorem traceFunction_tensorObj (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (F.tensorObj G hF).traceFunction n y = G.traceFunction n y * F.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace, traceFunction_eq_trace,
    trace_stalk_tensorObj_frobeniusEnd_pow]

/-- The tensor product of two lisse Weil sheaves is lisse. -/
theorem IsLisse.tensorObj {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse) :
    (F.tensorObj G hF).IsLisse :=
  ProEtale.IsAdicLisseSheaf.ihom hF.dual hG

end AlgebraicGeometry.WeilSheaf

