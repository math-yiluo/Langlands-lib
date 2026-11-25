/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Trace
public import WeilConjectures.WeilSheaf.StalkTensor
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Hom

/-!
# Stalks of the internal hom out of a lisse Weil sheaf

For a lisse Weil sheaf `D` and a Weil sheaf `F`, the internal hom `[D, F]` is a Weil sheaf
(`AlgebraicGeometry.WeilSheaf.ihom`). At a geometric point `s`, the evaluation induces a
pairing `[D, F]_s × D_s → F_s` which is perfect (`D` being lisse,
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`) and compatible
with the Frobenius of the stalks
(`AlgebraicGeometry.WeilSheaf.ihomEvaluationPairing_stalkAt_frobenius`). Hence the Frobenius
of `[D, F]_s = Hom(D_s, F_s)` is `f ↦ F ∘ f ∘ F⁻¹`, and its trace is `tr(F | F_s) tr(F⁻¹ | D_s)`
(`AlgebraicGeometry.WeilSheaf.trace_frobeniusEnd_stalkAt_ihom`). For `D = G^∨` the dual of a
lisse Weil sheaf, `[G^∨, F]` is the tensor product `G ⊗ F`, and the trace function is
multiplicative: `t_{[G^∨, F]} = t_G t_F`
(`AlgebraicGeometry.WeilSheaf.traceFunction_ihom_dual`).

## Blueprint

These are the stalk computations behind "the trace of a tensor product is the product of the
traces" in the proof of the Fourier trace formula (sketch blueprint
`sec-The-Plancherel-formula`).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- Isomorphic Frobenius modules have the same trace of the inverse Frobenius. -/
theorem Equiv.trace_frobenius_symm {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    LinearMap.trace K _ N.frobenius.symm.toLinearMap =
      LinearMap.trace K _ M.frobenius.symm.toLinearMap := by
  have h : N.frobenius.symm.toLinearMap =
      e.toLinearEquiv.conj M.frobenius.symm.toLinearMap := by
    refine LinearMap.ext fun x ↦ (LinearEquiv.symm_apply_eq _).2 ?_
    rw [LinearEquiv.conj_apply_apply, ← e.map_frobenius]
    simp
  rw [h, LinearMap.trace_conj']

/-- The inverse of the Frobenius of the dual `M^∨` is the transpose of the Frobenius of `M`, so
their traces agree. -/
theorem trace_dual_frobenius_symm (M : FrobeniusModule.{u, v} K) :
    LinearMap.trace K _ M.dual.frobenius.symm.toLinearMap =
      LinearMap.trace K _ M.frobeniusEnd := by
  rw [← LinearMap.trace_transpose' M.frobeniusEnd]
  congr 1

/-- If a perfect pairing `p : V × M → N` of Frobenius modules is compatible with the Frobenius,
then `tr(F | V) = tr(F | N) tr(F⁻¹ | M)` (`LinearMap.trace_eq_mul_of_bijective`). -/
theorem trace_frobeniusEnd_eq_mul_of_bijective {V M N : FrobeniusModule.{u, v} K}
    (p : V.carrier →ₗ[K] M.carrier →ₗ[K] N.carrier) (hp : Function.Bijective p)
    (h : ∀ v m, p (V.frobeniusEnd v) (M.frobenius m) = N.frobeniusEnd (p v m)) :
    LinearMap.trace K _ V.frobeniusEnd =
      LinearMap.trace K _ N.frobeniusEnd * LinearMap.trace K _ M.frobenius.symm.toLinearMap :=
  LinearMap.trace_eq_mul_of_bijective p hp _ _ _ h

end FrobeniusModule

namespace AlgebraicGeometry

namespace WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The internal hom `[D, F]` of Weil sheaves out of a lisse Weil sheaf `D`: the internal hom of
the underlying pro-étale Weil sheaves, which is constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf`). -/
noncomputable def ihom (D : WeilSheaf k₀ l X) (hD : D.IsLisse) (F : WeilSheaf k₀ l X) :
    WeilSheaf k₀ l X where
  obj := ProEtaleWeilSheaf.ihom k₀ l X D.obj F.obj
  property := IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf hD F.property

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)

/-- The pairing `[D, F]_s × D_s → F_s` of stalks induced by the evaluation is compatible with
the Frobenius of the stalks. -/
lemma ihomEvaluationPairing_stalkAt_frobenius (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier
        (((D.ihom hD F).stalkAt s m hs).frobenius v) ((D.stalkAt s m hs).frobenius x) =
      (F.stalkAt s m hs).frobenius
        (Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier v x) := by
  have h := stalkPairing_frobenius s m hs _ _ _ _
    (frobeniusPowIso_tensor (D.ihom hD F) D F _
      (ProEtaleWeilSheaf.ihom_evaluation_str D.obj F.obj) m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    stalkAt_frobenius_eq_stalkFrobeniusIso, Mod.evaluationPairing_apply,
    Mod.evaluationPairing_apply]
  exact ModuleCat.tmul_eq_of_tensorHom_comp h v x

/-- The `ℚ̄_ℓ`-bilinear pairing `[D, F]_s × D_s → F_s` of stalks induced by the evaluation. -/
noncomputable def stalkAtIhomPairing (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) :
    ((D.ihom hD F).stalkAt s m hs).carrier →ₗ[PadicAlgCl l]
      (D.stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (F.stalkAt s m hs).carrier :=
  WeilCoefficients.homLinearMap
    (Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier)

/-- The pairing `[D, F]_s × D_s → F_s` of stalks is perfect. -/
theorem bijective_stalkAtIhomPairing (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) : Function.Bijective (stalkAtIhomPairing s m hs D hD F) :=
  WeilCoefficients.bijective_homLinearMap
    (IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse hD _ s)

/-- The pairing of stalks is the pairing induced by the evaluation. -/
lemma stalkAtIhomPairing_apply (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    stalkAtIhomPairing s m hs D hD F v x =
      Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier v x :=
  rfl

/-- The pairing `[D, F]_s × D_s → F_s` of stalks is compatible with the Frobenius. -/
theorem stalkAtIhomPairing_frobenius (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    stalkAtIhomPairing s m hs D hD F (((D.ihom hD F).stalkAt s m hs).frobeniusEnd v)
        ((D.stalkAt s m hs).frobenius x) =
      (F.stalkAt s m hs).frobeniusEnd (stalkAtIhomPairing s m hs D hD F v x) := by
  rw [FrobeniusModule.frobeniusEnd, FrobeniusModule.frobeniusEnd, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, stalkAtIhomPairing_apply, stalkAtIhomPairing_apply]
  exact ihomEvaluationPairing_stalkAt_frobenius s m hs D hD F v x

/-- The perfect stalk pairing identifies the stalk of the internal hom with linear maps. -/
private noncomputable def stalkAtIhomLinearEquiv (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) :
    ((D.ihom hD F).stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l]
      ((D.stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (F.stalkAt s m hs).carrier) :=
  LinearEquiv.ofBijective (stalkAtIhomPairing s m hs D hD F)
    (bijective_stalkAtIhomPairing s m hs D hD F)

private lemma stalkAtIhomLinearEquiv_apply (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    stalkAtIhomLinearEquiv s m hs D hD F v x =
      Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier v x :=
  rfl

/-- Under the stalk equivalence, Frobenius acts by pre- and post-composition. -/
private lemma stalkAtIhomLinearEquiv_frobenius (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier) :
    stalkAtIhomLinearEquiv s m hs D hD F (((D.ihom hD F).stalkAt s m hs).frobenius v) =
      (F.stalkAt s m hs).frobeniusEnd ∘ₗ stalkAtIhomLinearEquiv s m hs D hD F v ∘ₗ
        (D.stalkAt s m hs).frobenius.symm.toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (D.stalkAt s m hs).frobenius.surjective x
  rw [FrobeniusModule.frobeniusEnd, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    stalkAtIhomLinearEquiv_apply, stalkAtIhomLinearEquiv_apply]
  exact ihomEvaluationPairing_stalkAt_frobenius s m hs D hD F v y

/-- The trace of the Frobenius on the stalk of the internal hom `[D, F]` out of a lisse Weil
sheaf: `tr(F | [D, F]_s) = tr(F | F_s) tr(F⁻¹ | D_s)`, the stalk being `Hom(D_s, F_s)` with the
Frobenius `f ↦ F ∘ f ∘ F⁻¹`. -/
theorem trace_frobeniusEnd_stalkAt_ihom (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) :
    LinearMap.trace (PadicAlgCl l) _ ((D.ihom hD F).stalkAt s m hs).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd *
        LinearMap.trace (PadicAlgCl l) _ (D.stalkAt s m hs).frobenius.symm.toLinearMap := by
  simpa only [pow_one] using
    FrobeniusModule.trace_frobeniusEnd_pow_eq_mul_of_linearEquiv
      ((D.ihom hD F).stalkAt s m hs) (D.stalkAt s m hs) (F.stalkAt s m hs)
      (stalkAtIhomLinearEquiv s m hs D hD F) (stalkAtIhomLinearEquiv_frobenius s m hs D hD F) 1

/-- The trace of the Frobenius on the stalk of `[G^∨, F] = G ⊗ F`, for a lisse Weil sheaf `G`,
is the product of the traces on the stalks of `G` and `F`. -/
theorem trace_frobeniusEnd_stalkAt_ihom_dual (G : WeilSheaf k₀ l X) (hG : G.IsLisse)
    (F : WeilSheaf k₀ l X) :
    LinearMap.trace (PadicAlgCl l) _ (((G.dual hG).ihom hG.dual F).stalkAt s m hs).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (G.stalkAt s m hs).frobeniusEnd *
        LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd := by
  rw [trace_frobeniusEnd_stalkAt_ihom, ← (stalkAtDualEquiv s m hs G hG).trace_frobenius_symm,
    FrobeniusModule.trace_dual_frobenius_symm, mul_comm]

/-- **The trace function is multiplicative under the tensor product with a lisse Weil sheaf.**
For a lisse Weil sheaf `G`, the trace function of `[G^∨, F] = G ⊗ F` is `t_G t_F`. -/
theorem traceFunction_ihom_dual (G : WeilSheaf k₀ l X) (hG : G.IsLisse) (F : WeilSheaf k₀ l X)
    (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((G.dual hG).ihom hG.dual F).traceFunction n x = G.traceFunction n x * F.traceFunction n x :=
  trace_frobeniusEnd_stalkAt_ihom_dual _ n _ G hG F

end WeilSheaf

end AlgebraicGeometry
