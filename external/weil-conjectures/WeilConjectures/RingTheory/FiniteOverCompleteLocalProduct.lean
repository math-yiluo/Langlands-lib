/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionFiniteExtension
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Finite algebras over complete local rings

Source: literature/stacks-project/algebra.tex, Lemma Tag 0325
(blueprint: lem-weil-pbc-finite-over-complete-local-product)
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite algebra over a complete Noetherian local ring is a finite product of
complete Noetherian local rings, with the domain case as stated in Tag 0325.

Proof:
1. A finite algebra over a Noetherian ring is Noetherian (`IsNoetherianRing.of_finite`).
2. Put `m = maximalIdeal R`, `L = R_m` and `C = AdicCompletion (maximalIdeal L) L`.
   Every denominator of `L` is a unit in `R`, giving `R ≃ₐ[R] L`. Transport maximal
   ideals and adic completeness along this equivalence. The canonical completion
   equivalence of `L` therefore gives `R ≃ₐ[R] C`.
3. Apply `completion_finite_extension` at `m`. Its factors `D q` are the maximal-ideal
   completions of `S_q`, indexed by the finite type of primes over `m`. Tensoring the
   equivalence of step 2 with `S` and composing with the completion product equivalence
   gives `S ≃ₐ[R] ∀ q, D q`. Each maximal ideal of `S` contracts to `m` by integrality;
   the resulting injection into the primes over `m` proves finiteness of maximal ideals.
4. Every `S_q` is Noetherian and local. Its completion is Noetherian by
   `AdicCompletion.isNoetherianRing`, and local and complete by Mathlib's completion
   instances. Reindex the product by `Fin (Fintype.card Q)`. An empty index type gives
   the zero ring, so no nontriviality hypothesis on `S` is needed here.
5. If `S` is a domain, the index type is nonempty: an empty product would force `1 = 0`.
   If two indices were distinct, their characteristic and complementary characteristic
   functions would give two nonzero elements with zero product. Transport them back
   to `S` to contradict the domain hypothesis. Thus the index type has exactly one
   element, and evaluation gives a ring equivalence `S ≃+* D q`.
6. Transport localness and completeness along this ring equivalence. The maximal ideal
   contracts to `m` by integrality. Every prime over `m` is maximal by integrality, and
   hence equals the unique maximal ideal of `S`.
Source: literature/stacks-project/algebra.tex, Lemma Tag 0325
(blueprint: lem-weil-pbc-finite-over-complete-local-product)
-/
theorem finite_over_complete_local_product
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Algebra R S] [Module.Finite R S] :
    IsNoetherianRing S ∧
      Finite {M : Ideal S // M.IsMaximal} ∧
      (∃ (t : ℕ) (A : Fin t → Type v) (rings : ∀ i, CommRing (A i)),
        letI := rings
        ∃ (algebras : ∀ i, Algebra R (A i)),
          letI := algebras
          ∃ (locals : ∀ i, IsLocalRing (A i)),
            letI := locals
            Nonempty (S ≃ₐ[R] (∀ i, A i)) ∧
              (∀ i, IsNoetherianRing (A i)) ∧
              (∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))) ∧
      (IsDomain S →
        IsNoetherianRing S ∧
          ∃ hL : IsLocalRing S,
            letI := hL
            IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
              (IsLocalRing.maximalIdeal S).comap (algebraMap R S) =
                IsLocalRing.maximalIdeal R ∧
              ∀ M : Ideal S, M.IsPrime →
                M.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
                  M = IsLocalRing.maximalIdeal S) := by
  classical
  have hN : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let m := IsLocalRing.maximalIdeal R
  let L := Localization.AtPrime m
  let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
  let Q := m.primesOver S
  let D := fun q : Q ↦
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
      (Localization.AtPrime q.1)
  let eL : R ≃ₐ[R] L := IsLocalization.atUnits R m.primeCompl (by
    intro r hr
    exact (IsLocalRing.notMem_maximalIdeal.mp hr))
  have hLc : IsAdicComplete (IsLocalRing.maximalIdeal L) L := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal eL.toRingEquiv]
    exact (IsAdicComplete.congr_ringEquiv m eL.toRingEquiv).mpr inferInstance
  let eC : R ≃ₐ[R] C :=
    eL.trans ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal L)).restrictScalars R)
  obtain ⟨hQ, e, _⟩ :=
    AdicCompletion.completion_finite_extension R S m
  have : Finite Q := hQ
  have hDN : ∀ q : Q, IsNoetherianRing (D q) := fun q ↦
    AdicCompletion.isNoetherianRing (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
  have hDL : ∀ q : Q, IsLocalRing (D q) := fun q ↦ inferInstance
  have hDC : ∀ q : Q, IsAdicComplete (IsLocalRing.maximalIdeal (D q)) (D q) :=
    fun q ↦ inferInstance
  let eT : S ≃ₐ[R] (TensorProduct R C S) :=
    (Algebra.TensorProduct.lid R S).symm.trans
      (Algebra.TensorProduct.congr eC (AlgEquiv.refl : S ≃ₐ[R] S))
  let _ := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
  let eS : S ≃ₐ[R] (∀ q : Q, D q) := eT.trans (e.restrictScalars R)
  have hfin : Finite {M : Ideal S // M.IsMaximal} := by
    let f : {M : Ideal S // M.IsMaximal} → Q := fun M ↦ by
      have : M.1.IsMaximal := M.2
      have hcom := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) M.1
      exact ⟨M.1, M.2.isPrime, ⟨(IsLocalRing.eq_maximalIdeal hcom).symm⟩⟩
    exact Finite.of_injective f (by
      intro M N h
      exact Subtype.ext (congrArg (fun q : Q ↦ q.1) h))
  refine ⟨hN, hfin, ?_, ?_⟩
  · let _ := Fintype.ofFinite Q
    let f := Fintype.equivFin Q
    refine ⟨Fintype.card Q, fun i ↦ D (f.symm i), inferInstance,
      inferInstance, inferInstance, ?_, ?_, ?_⟩
    · exact ⟨eS.trans (AlgEquiv.piCongrLeft' R D f)⟩
    · exact fun i ↦ hDN (f.symm i)
    · exact fun i ↦ hDC (f.symm i)
  · intro hDom
    have hne : Nonempty Q := by
      by_contra hn
      have : IsEmpty Q := not_nonempty_iff.mp hn
      exact one_ne_zero (eS.injective (Subsingleton.elim (eS 1) (eS 0)))
    have hsub : Subsingleton Q := ⟨by
      intro i j
      by_contra hij
      let x : ∀ q : Q, D q := fun q ↦ if q = i then 1 else 0
      let y : ∀ q : Q, D q := fun q ↦ if q = i then 0 else 1
      have hxy : x * y = 0 := by
        ext q
        by_cases hqi : q = i <;> simp [x, y, hqi]
      have hz : eS.symm x * eS.symm y = 0 := by
        rw [← map_mul, hxy, map_zero]
      rcases mul_eq_zero.mp hz with hx | hy
      · have hx' : x = 0 := by
          simpa using congrArg eS hx
        have : (1 : D i) = 0 := by
          simpa [x] using congrFun hx' i
        exact one_ne_zero this
      · have hy' : y = 0 := by
          simpa using congrArg eS hy
        have : (1 : D j) = 0 := by
          simpa [y, Ne.symm hij] using congrFun hy' j
        exact one_ne_zero this⟩
    let q₀ : Q := Classical.choice hne
    let _ : Unique Q := ⟨⟨q₀⟩, fun q ↦ Subsingleton.elim q q₀⟩
    let e₀ : S ≃+* D q₀ := eS.toRingEquiv.trans (RingEquiv.piUnique D)
    have hSL : IsLocalRing S := e₀.symm.isLocalRing
    refine ⟨hN, hSL, ?_, ?_, ?_⟩
    · apply (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal S) e₀).mp
      simpa using hDC q₀
    · exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
          (IsLocalRing.maximalIdeal S))
    · intro M hM hcom
      have : M.IsPrime := hM
      have hmax : (M.comap (algebraMap R S)).IsMaximal := by
        rw [hcom]
        infer_instance
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_of_isIntegral_of_isMaximal_under M hmax)

end Algebra
