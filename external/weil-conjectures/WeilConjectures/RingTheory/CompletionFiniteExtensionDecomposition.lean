/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.QuasiFinite.Basic
import WeilConjectures.RingTheory.CompletionTensorLocalMapsInjective
import WeilConjectures.RingTheory.CompletionTensorLocalMapsSurjective

/-!
# Finite-prime decomposition of completed tensors

Source: Stacks Project, Algebra, Tag 07N9 (lemma-completion-finite-extension).
(blueprint: lem-weil-pbc-completion-finite-extension-decomposition)
-/

@[expose] public section
universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- A ring map carrying `I` into `J` induces a map of adic completions. -/
private noncomputable def mapCompletion
    {T : Type*} {U : Type*} [CommRing T] [CommRing U]
    (I : Ideal T) (J : Ideal U) (φ : T →+* U) (hφ : I.map φ ≤ J) :
    AdicCompletion I T →+* AdicCompletion J U := by
  let f (n : ℕ) : AdicCompletion I T →+* U ⧸ J ^ n :=
    (Ideal.quotientMap (J ^ n) φ (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact pow_le_pow_left' hφ n)).comp (evalₐ I n).toRingHom
  have hf {i j : ℕ} (hij : i ≤ j) :
      (Ideal.Quotient.factorPow J hij).comp (f j) = f i := by
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I j x)
    have hi : evalₐ I i x = Ideal.Quotient.mk (I ^ i) r := by
      have hv : x.val j = Submodule.Quotient.mk r := by
        have h := factor_evalₐ_eq_eval I (n := j) x (by simp)
        rw [← hr] at h
        exact h.symm
      have hvi := x.property hij
      rw [hv] at hvi
      have h := factor_eval_eq_evalₐ I (n := i) x (by simp)
      rw [show eval I T i x = Submodule.Quotient.mk r from hvi.symm] at h
      exact h.symm
    simp [f, ← hr, hi]
  exact liftRingHom J f (fun hij ↦ hf hij)

private theorem mapCompletion_eval
    {T : Type*} {U : Type*} [CommRing T] [CommRing U]
    (I : Ideal T) (J : Ideal U) (φ : T →+* U) (hφ : I.map φ ≤ J)
    (n : ℕ) (x : AdicCompletion I T) (r : T)
    (hx : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r) :
    evalₐ J n (mapCompletion I J φ hφ x) = Ideal.Quotient.mk (J ^ n) (φ r) := by
  rw [mapCompletion, evalₐ_liftRingHom]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    hx, Ideal.quotientMap_mk]

-- The unchanged statement contains an unused auxiliary ideal `J`.
set_option linter.unusedVariables false in
/-- The finite-prime decomposition and levelwise compatibility data in the completion theorem.
Source: Stacks Project, Algebra, Lemma 10.97.8 (Tag 07N9), steps 1--4.
(blueprint: lem-weil-pbc-completion-finite-extension-decomposition)

The proof follows Tag 07N9 as follows. Localize at `p`, identify the resulting
primes over the maximal ideal with `p.primesOver S`, and use finite generation and
Noetherianity to obtain finiteness. At every level `n`, the quotient by the `n`th
power of the maximal ideal is a finite zero-dimensional local algebra. The product
of its localizations at its maximal ideals is therefore an isomorphism (with the
empty product interpreted as the zero ring). Localization at a prime of a quotient
identifies each factor with the corresponding quotient of `Localization.AtPrime q`.
Passing to compatible inverse-limit sequences gives the displayed algebra equivalence
`e`; the induced maps from `C` are the ring homomorphisms `g`, and the quotient
identifications give the displayed levelwise equation. Evaluating the product
equivalence on `a ⊗ 1` gives the final compatibility equation. -/
theorem completion_finite_extension_decomposition
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    Finite Q ∧
      ∃ (e : (C ⊗[R] S) ≃ₐ[S] (∀ q : Q, D q))
        (g : ∀ q : Q, C →+* D q),
        (∀ (q : Q) (n : ℕ) (a : C) (r : A),
          AdicCompletion.evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
          AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g q a) =
            Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p)) r)) ∧
        (∀ (a : C) (q : Q), e (a ⊗ₜ[R] (1 : S)) q = g q a) := by
  intro A m C B J Q D
  clear J B
  let φ (q : Q) : A →+* Localization.AtPrime q.1 :=
    Localization.localRingHom p q.1 (algebraMap R S)
      (Ideal.LiesOver.over (P := q.1) (p := p))
  have hφ (q : Q) : m.map (φ q) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q.1) := by
    have : IsLocalHom (φ q) := Localization.isLocalHom_localRingHom _ _ _ _
    exact IsLocalRing.map_maximalIdeal_le (φ q)
  let g (q : Q) : C →+* D q :=
    mapCompletion m (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) (φ q) (hφ q)
  have hlevel (q : Q) (n : ℕ) (a : C) (r : A)
      (ha : evalₐ m n a = Ideal.Quotient.mk (m ^ n) r) :
      evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g q a) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
          (φ q r) := mapCompletion_eval _ _ _ _ _ _ _ ha
  have hg (q : Q) (r : R) : g q (algebraMap R C r) = algebraMap R (D q) r := by
    apply ext_evalₐ
    intro n
    rw [algebraMap_apply]
    rw [hlevel q n _ _ (evalₐ_of m n (algebraMap R A r))]
    rw [show algebraMap R (D q) r =
      of (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1) (algebraMap R (Localization.AtPrime q.1) r) from
          algebraMap_apply _ r, evalₐ_of]
    congr 1
    simpa only [φ, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.1)] using
      Localization.localRingHom_to_map p q.1 (algebraMap R S)
        (Ideal.LiesOver.over (P := q.1) (p := p)) r
  let gR : C →ₐ[R] (∀ q : Q, D q) :=
    { RingHom.pi g with commutes' := fun r ↦ funext fun q ↦ hg q r }
  let fR : (C ⊗[R] S) →ₐ[R] (∀ q : Q, D q) :=
    Algebra.TensorProduct.lift gR (IsScalarTower.toAlgHom R S (∀ q : Q, D q))
      (fun _ _ ↦ Commute.all _ _)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  let f : (C ⊗[R] S) →ₐ[S] (∀ q : Q, D q) :=
    { toRingHom := fR.toRingHom
      commutes' := by
        intro s
        change fR (1 ⊗ₜ[R] s) = algebraMap S _ s
        simp [fR] }
  have hcompat (a : C) (q : Q) : f (a ⊗ₜ[R] (1 : S)) q = g q a := by
    change (fR (a ⊗ₜ[R] (1 : S))) q = g q a
    simp [fR, gR]
  refine ⟨(Algebra.QuasiFinite.finite_primesOver (S := S) p).to_subtype, ?_⟩
  have hflevel (q : Q) (n : ℕ) (a : C) (r : A)
      (ha : evalₐ m n a = Ideal.Quotient.mk (m ^ n) r) :
      evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
          (f (a ⊗ₜ[R] (1 : S)) q) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
          (φ q r) := by
    rw [hcompat]
    exact hlevel q n a r ha
  have hf : Function.Bijective f :=
    ⟨completion_tensor_localMaps_injective R S p f hflevel,
      completion_tensor_localMaps_surjective R S p f hflevel⟩
  let e := AlgEquiv.ofBijective f hf
  exact ⟨e, g, hlevel, hcompat⟩
end AdicCompletion
