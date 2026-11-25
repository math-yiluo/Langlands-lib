/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.TraceSemilinear
public import WeilConjectures.TraceFormula.UnitBasis
public import WeilConjectures.TraceFormula.WeilScalarUnit

/-!
# Categorical traces over a separably closed point as linear traces

Let `Ω` be a separably closed field and `V` a module object over `ℚ̲̄_ℓ` on `Spec Ω` with a unit
basis. Through the identification `End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ`
(`ProEtale.CondensedRing.endTensorUnitRingEquiv`), the categorical trace of an endomorphism `φ`
of `V` is the trace of the `ℚ̄_ℓ`-linear map `x ↦ x ≫ φ` on any `ℚ̄_ℓ`-vector space `W`
identified with the sections `𝟙_ ⟶ V`, the constants `c` acting on the sections through the
multiplications `ProEtale.CondensedRing.scalarEndRingHom` of the unit
(`ProEtale.CondensedRing.endTensorUnitRingEquiv_traceOrZero_eq_trace`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The constants `ℚ̄_ℓ`, acting by precomposition on the sections `𝟙_ ⟶ V` of a module object
on `Spec Ω`: the ring isomorphism `ℚ̄_ℓ ≃+* (End 𝟙_)ᵐᵒᵖ` inverse to `endTensorUnitRingEquiv`. -/
noncomputable def endTensorUnitOpRingEquiv :
    _root_.PadicAlgCl ℓ ≃+*
      (End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))))))ᵐᵒᵖ :=
  (endTensorUnitRingEquiv ℓ Ω).symm.trans (RingEquiv.toOpposite _)

lemma endTensorUnitOpRingEquiv_apply (c : _root_.PadicAlgCl ℓ) :
    endTensorUnitOpRingEquiv ℓ Ω c = .op (scalarEndRingHom ℓ (Spec (.of Ω)) c) := by
  refine MulOpposite.unop_injective ((endTensorUnitRingEquiv ℓ Ω).injective ?_)
  rw [MulOpposite.unop_op, endTensorUnitRingEquiv_scalarEndRingHom]
  exact (endTensorUnitRingEquiv ℓ Ω).apply_symm_apply c

variable {ℓ Ω}

/-- **Categorical traces over a separably closed point are linear traces**: let `V` be a module
object on `Spec Ω` with a unit basis, `φ` an endomorphism of `V`, and `e : W ≃+ (𝟙_ ⟶ V)` an
identification of a finite-dimensional `ℚ̄_ℓ`-vector space `W` with the sections of `V`, which
sends `c • w` to `scalarEndRingHom c ≫ e w`. If `e` intertwines a linear endomorphism `f` of `W`
with `x ↦ x ≫ φ`, then `Tr(φ) = Tr(f)` through `End (𝟙_) ≃+* ℚ̄_ℓ`. -/
theorem endTensorUnitRingEquiv_traceOrZero_eq_trace
    {V : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : UnitBasis V ι) (φ : V ⟶ V)
    {W : Type*} [AddCommGroup W] [Module (_root_.PadicAlgCl ℓ) W]
    [FiniteDimensional (_root_.PadicAlgCl ℓ) W] (e : W ≃+ (𝟙_ _ ⟶ V))
    (he : ∀ (c : _root_.PadicAlgCl ℓ) (w : W),
      e (c • w) = (scalarEndRingHom ℓ (Spec (.of Ω)) c).asHom ≫ e w)
    (f : W →ₗ[_root_.PadicAlgCl ℓ] W) (hf : ∀ w, e (f w) = e w ≫ φ) :
    endTensorUnitRingEquiv ℓ Ω (traceOrZero φ) = LinearMap.trace _ W f := by
  have h := LinearMap.trace_eq_ringEquiv_trace_of_addEquiv (endTensorUnitOpRingEquiv ℓ Ω) e
    (fun c w ↦ by rw [he, endTensorUnitOpRingEquiv_apply, End.smul_left, MulOpposite.unop_op])
    f (Preadditive.rightCompEndOp (𝟙_ _) φ) hf
  rw [b.trace_rightCompEndOp φ, endTensorUnitOpRingEquiv, RingEquiv.trans_apply,
    RingEquiv.toOpposite_apply] at h
  rw [MulOpposite.op_injective h, RingEquiv.apply_symm_apply]

end AlgebraicGeometry.ProEtale.CondensedRing
