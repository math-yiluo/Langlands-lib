/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.LocalCompletionQuotient

/-!
# Quotient identification of formal fibres

Source: Stacks Project, More on Algebra, proof of Lemma 07PN.
(blueprint: lem-weil-pbc-formal-fibre-quotient-iso)
-/

@[expose] public section

universe u

/-- The formal fibre of the completion of `R_p` at `q ≤ p` is the generic formal
fibre of the completion of `(R/q)_(p/q)`, as an algebra over `κ(q)`.
Source: Stacks Project, More on Algebra, proof of Lemma 07PN.
(blueprint: lem-weil-pbc-formal-fibre-quotient-iso)

Proof:
1. Localization of a quotient identifies `(R/q)_(p/q)` with `R_p/qR_p`.
   The induced surjection of local rings carries the maximal ideal onto the
   maximal ideal, and its kernel is `qR_p`.
2. Completion of this surjection identifies the completion of `(R/q)_(p/q)`
   with `completion(R_p)/q completion(R_p)`, compatibly with the structure maps.
   This uses completion of a quotient of a Noetherian local ring.
3. The tensor-quotient identification writes this quotient as
   `(R/q) ⊗[R] completion(R_p)`. Tensor cancellation over `R/q`, followed by
   tensor symmetry, identifies its tensor product with `κ(q)` with
   `κ(q) ⊗[R] completion(R_p)`. All maps fix the `κ(q)` factor, so the
   resulting ring isomorphism is a `κ(q)`-algebra isomorphism. -/
theorem nonempty_formalFibre_quotient_algEquiv
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q p : Ideal R) [q.IsPrime] [p.IsPrime] (hqp : q ≤ p) :
    let pbar := p.map (Ideal.Quotient.mk q)
    letI : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
    let L := Localization.AtPrime pbar
    let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
    let Cp := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p)
    Nonempty ((TensorProduct (R ⧸ q) q.ResidueField C) ≃ₐ[q.ResidueField] q.Fiber Cp) := by
  dsimp only
  let B := R ⧸ q
  let pbar := p.map (Ideal.Quotient.mk q)
  have : pbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hqp
  have hc : pbar.comap (Ideal.Quotient.mk q) = p := by
    dsimp [pbar]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hqp]
  let A := Localization.AtPrime p
  let D := Localization.AtPrime pbar
  let φ := Localization.localRingHom p pbar (Ideal.Quotient.mk q) hc.symm
  have hφ : Function.Surjective φ :=
    (RingHom.surjectiveOnStalks_of_surjective
      (f := Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective).localRingHom_surjective
      p pbar hc.symm
  have hφker : RingHom.ker φ = q.map (algebraMap R A) := by
    have hcompl : Submonoid.map (Ideal.Quotient.mk q) p.primeCompl = pbar.primeCompl := by
      simpa only [hc] using
        (Ideal.map_primeCompl_comap_of_surjective
          (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective pbar)
    simpa only [φ, Localization.localRingHom, Ideal.mk_ker] using
      (IsLocalization.ker_map (S := A) D (Ideal.Quotient.mk q) hcompl)
  have hmax : (IsLocalRing.maximalIdeal A).map φ = IsLocalRing.maximalIdeal D :=
    IsLocalRing.map_maximalIdeal_of_surjective φ hφ
  have H := AdicCompletion.exists_local_completion_quotient A D φ hφ
  dsimp only at H
  rw [hmax, hφker, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at H
  obtain ⟨_, θ, _, hθ, _, _, e, he⟩ := H
  let Cp := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let C := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let Q := Cp ⧸ q.map (algebraMap R Cp)
  let eR : Q ≃ₐ[R] C :=
    { e with
      commutes' := fun x ↦ by
        change e (Ideal.Quotient.mk _ (algebraMap R Cp x)) = algebraMap R C x
        rw [he, IsScalarTower.algebraMap_apply R A Cp]
        rw [show θ (algebraMap A Cp (algebraMap R A x)) =
          algebraMap D C (φ (algebraMap R A x)) from RingHom.congr_fun hθ _]
        rw [Localization.localRingHom_to_map]
        rfl }
  let eT := Algebra.TensorProduct.quotIdealMapEquivQuotTensor Cp q
  let eB : Q ≃ₐ[B] C :=
    AlgEquiv.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := q)) eR
  let eBC : C ≃ₐ[B] TensorProduct R B Cp := eB.symm.trans eT
  let eF := Algebra.TensorProduct.congr (AlgEquiv.refl : q.ResidueField ≃ₐ[q.ResidueField]
    q.ResidueField) eBC
  let cancel := Algebra.TensorProduct.cancelBaseChange R B q.ResidueField q.ResidueField Cp
  exact ⟨eF.trans cancel⟩
