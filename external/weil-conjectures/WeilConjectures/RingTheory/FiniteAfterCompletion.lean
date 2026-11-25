/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Algebra.ChangeIdealCompletion
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import WeilConjectures.RingTheory.ExtendedCompletionModuleReduction

/-!
# Finite modules after completion

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 0394
(blueprint: lem-weil-pbc-finite-after-completion).
-/

@[expose] public section

universe u v

namespace AdicCompletion

/--
For a local homomorphism of local rings whose maximal ideals are finitely generated and whose
special fibre is finite-dimensional, the completion of the target is the completion for the
extended maximal ideal and is finite over the completion of the source.
Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 0394
(blueprint: lem-weil-pbc-finite-after-completion).
Proof (following the seven steps of the node):
1. The special fibre is Artinian by lem-weil-pbc-finite-dim-algebra-artinian and local;
   lem-weil-pbc-artinian-local-unique-prime makes n the only prime above mS.
2. By lem-weil-pbc-zero-locus-eq-iff-radical-eq its radical is n; then
   lem-weil-pbc-fg-ideal-radical-power gives n^t ≤ mS for some t ≥ 1.
3. The powers of mS are the extended powers of m. Together with mS ≤ n, this gives
   the canonical comparison isomorphism by lem-weil-pbc-change-ideal-completion.
4. Regard S' as the completion of the R-module S. Its canonical R-completion action
   agrees, through γ and componentwise comparison, with the action through φhat.
5. By lem-weil-pbc-module-completion-complete and lem-weil-pbc-adic-completion-mod-ideal,
   S' and R-completion are complete, and their quotients modulo m are S/mS and R/m.
6. Powers of the extended ideal act as powers of m. Thus S' is separated for that
   ideal, and its quotient is the given finite-dimensional special fibre.
7. Apply lem-weil-pbc-finite-over-complete-ring to S' over R-completion; transport
   finite generation along the comparison isomorphism from step 4.
-/
theorem finite_after_completion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (m : Ideal R) (n : Ideal S) (φ : R →+* S)
    (hm : m = IsLocalRing.maximalIdeal R)
    (hn : n = IsLocalRing.maximalIdeal S)
    [IsLocalHom φ]
    (hm_fg : m.FG) (hn_fg : n.FG)
    (hfinite : letI := (Ideal.quotientMap (Ideal.map φ m) φ Ideal.le_comap_map).toAlgebra
      Module.Finite (R ⧸ m) (S ⧸ Ideal.map φ m)) :
    ∃ (γ : AdicCompletion (Ideal.map φ m) S ≃+* AdicCompletion n S)
      (φhat : AdicCompletion m R →+* AdicCompletion n S),
      (∀ (k : ℕ) (x : AdicCompletion (Ideal.map φ m) S) (s : S),
        AdicCompletion.evalₐ (Ideal.map φ m) k x =
          Ideal.Quotient.mk ((Ideal.map φ m) ^ k) s →
        AdicCompletion.evalₐ n k (γ x) = Ideal.Quotient.mk (n ^ k) s) ∧
      (∀ (k : ℕ) (x : AdicCompletion m R) (r : R),
        AdicCompletion.evalₐ m k x = Ideal.Quotient.mk (m ^ k) r →
        AdicCompletion.evalₐ n k (φhat x) = Ideal.Quotient.mk (n ^ k) (φ r)) ∧
      letI := φhat.toAlgebra
      Module.Finite (AdicCompletion m R) (AdicCompletion n S) := by
  subst m
  subst n
  let J := Ideal.map φ (IsLocalRing.maximalIdeal R)
  have hJn : J ≤ IsLocalRing.maximalIdeal S := IsLocalRing.map_maximalIdeal_le φ
  let := (Ideal.quotientMap J φ Ideal.le_comap_map).toAlgebra
  have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ J) := hfinite
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  have : IsArtinianRing (S ⧸ J) :=
    IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ J)
  have hrad : IsLocalRing.maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro P hP
    have : P.IsPrime := hP.2
    let q := Ideal.Quotient.mk J
    have : (Ideal.map q P).IsPrime := Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by simpa [q] using hP.1)
    have hmax : P.IsMaximal := by
      have h := Ideal.comap_isMaximal_of_surjective q
        Ideal.Quotient.mk_surjective (K := Ideal.map q P)
      simpa [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
        q, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hP.1] using h
    have heq : P = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hmax
    exact le_of_eq heq.symm
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hn_fg
  have hc' : (IsLocalRing.maximalIdeal S) ^ (c + 1) ≤ J :=
    (Ideal.pow_le_pow_right (by omega)).trans hc
  obtain ⟨γ, hγ⟩ := changeIdealCompletionRing
    (IsLocalRing.maximalIdeal S) J (c + 1) 1 (by omega) (by omega) hc'
    (by simpa using hJn)
  have hγeval (k : ℕ) (x : AdicCompletion J S) (s : S)
      (hx : evalₐ J k x = Ideal.Quotient.mk (J ^ k) s) :
      evalₐ (IsLocalRing.maximalIdeal S) k (γ x) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal S) ^ k) s := by
    have hv : x.val (1 * k) = Submodule.Quotient.mk s := by
      have h := factor_evalₐ_eq_eval J (n := 1 * k) x (by simp)
      have hx' : evalₐ J (1 * k) x =
          Ideal.Quotient.mk (J ^ (1 * k)) s := by
        rw [Nat.one_mul k]
        exact hx
      rw [hx'] at h
      exact h.symm
    have hv' := hγ x k
    rw [hv] at hv'
    have h := factor_eval_eq_evalₐ (IsLocalRing.maximalIdeal S) (n := k) (γ x) (by simp)
    rw [show eval (IsLocalRing.maximalIdeal S) S k (γ x) =
      Submodule.Quotient.mk s from hv'] at h
    exact h.symm
  let f (k : ℕ) : AdicCompletion (IsLocalRing.maximalIdeal R) R →+* S ⧸ J ^ k :=
    (Ideal.quotientMap (J ^ k) φ (by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow])).comp
        (evalₐ (IsLocalRing.maximalIdeal R) k).toRingHom
  have hf {i j : ℕ} (hij : i ≤ j) :
      (Ideal.Quotient.factorPow J hij).comp (f j) = f i := by
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (evalₐ (IsLocalRing.maximalIdeal R) j x)
    have hi : evalₐ (IsLocalRing.maximalIdeal R) i x =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ i) r := by
      have hv : x.val j = Submodule.Quotient.mk r := by
        have h := factor_evalₐ_eq_eval (IsLocalRing.maximalIdeal R) (n := j) x (by simp)
        rw [← hr] at h
        exact h.symm
      have hvi := x.property hij
      rw [hv] at hvi
      have h := factor_eval_eq_evalₐ (IsLocalRing.maximalIdeal R) (n := i) x (by simp)
      rw [show eval (IsLocalRing.maximalIdeal R) R i x =
        Submodule.Quotient.mk r from hvi.symm] at h
      exact h.symm
    simp [f, ← hr, hi]
  let ψ := liftRingHom J f (fun hij ↦ hf hij)
  have hψ (k : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal R) R) (r : R)
      (hx : evalₐ (IsLocalRing.maximalIdeal R) k x =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R) ^ k) r) :
      evalₐ J k (ψ x) = Ideal.Quotient.mk (J ^ k) (φ r) := by
    rw [evalₐ_liftRingHom]
    simp only [f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hx, Ideal.quotientMap_mk]
  let φhat := γ.toRingHom.comp ψ
  refine ⟨γ, φhat, hγeval, ?_, ?_⟩
  · intro k x r hx
    exact hγeval k (ψ x) (φ r) (hψ k x r hx)
  · have hprops := extendedCompletion_module_reduction R S
      (IsLocalRing.maximalIdeal R) φ hm_fg hfinite ψ hψ
    let := ψ.toAlgebra
    let K := (IsLocalRing.maximalIdeal R).map
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    have : IsAdicComplete K (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
      isAdicComplete_self (IsLocalRing.maximalIdeal R) hm_fg
    let := φ.toAlgebra
    have hψof (r : R) :
        ψ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
          algebraMap R (AdicCompletion J S) r := by
      apply ext_evalₐ
      intro k
      change evalₐ J k (ψ (of (IsLocalRing.maximalIdeal R) R r)) =
        evalₐ J k (of J S (φ r))
      rw [evalₐ_of]
      exact hψ k (of (IsLocalRing.maximalIdeal R) R r) r
        (evalₐ_of (IsLocalRing.maximalIdeal R) k r)
    have : IsScalarTower R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (AdicCompletion J S) := IsScalarTower.of_algebraMap_eq hψof
    have hhaus : IsHausdorff (IsLocalRing.maximalIdeal R) (AdicCompletion J S) :=
      (IsHausdorff.map_algebraMap_iff (I := IsLocalRing.maximalIdeal R) (S := S)).mp inferInstance
    have : IsHausdorff K (AdicCompletion J S) :=
      (IsHausdorff.map_algebraMap_iff (I := IsLocalRing.maximalIdeal R)
        (S := AdicCompletion (IsLocalRing.maximalIdeal R) R)).mpr hhaus
    have : Module.Finite
        (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸ K)
        (AdicCompletion J S ⧸ (K • ⊤ :
          Submodule (AdicCompletion (IsLocalRing.maximalIdeal R) R) (AdicCompletion J S))) :=
      hprops
    have hψfinite : ψ.Finite :=
      (Module.finite_and_span_eq_top_of_adicComplete K (AdicCompletion J S)).1
    exact γ.finite.comp hψfinite

end AdicCompletion
