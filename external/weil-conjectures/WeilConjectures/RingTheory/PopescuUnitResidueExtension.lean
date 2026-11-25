/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Defs

import WeilConjectures.RingTheory.PopescuAlgebraicResidueEnlargement
import WeilConjectures.RingTheory.PopescuTranscendentalResidueEnlargement
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Residue-field geometry of an admissible unit enlargement

Source: Stacks Project, Tags 07FH and 07FI.
(blueprint: lem-weil-pbc-popescu-unit-residue-extension).
-/

@[expose] public section

set_option autoImplicit false
universe u v

namespace Algebra

private theorem exists_geometric_residue_power
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B]
    [IsArtinianRing B] [IsLocalRing B]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (A₀ : Subalgebra k B) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible (IsLocalRing.maximalIdeal B))
    (x : B) (hx : IsUnit x) :
    ∃ (A : Subalgebra k B) (_ : IsLocalRing A), ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible (IsLocalRing.maximalIdeal B) ∧
      ∃ (Q : ℕ) (_ : 1 ≤ Q) (a : A),
        IsLocalRing.residue B (a : B) = IsLocalRing.residue B (x ^ Q) ∧
        ∃ (m : ℕ) (y : Fin m → A), (∀ j, (y j : B) = x) ∧
          ∃ (alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A)),
            letI := alg
            IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) ∧
            (∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
              (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ a₀) =
                IsLocalRing.residue A (Subalgebra.inclusion hle a₀)) ∧
            ((m = 0 ∧ Algebra.FormallyEtale (IsLocalRing.ResidueField A₀)
                (IsLocalRing.ResidueField A)) ∨
              (m = 1 ∧
                (∀ j, Transcendental (IsLocalRing.ResidueField A₀)
                  (IsLocalRing.residue A (y j))) ∧
                IntermediateField.adjoin (IsLocalRing.ResidueField A₀)
                  (Set.range (fun j ↦ IsLocalRing.residue A (y j))) = ⊤)) := by
  classical
  have : IsArtinianRing A₀ := hA₀.1
  have : IsLocalHom A₀.val := ⟨fun a ha ↦ by
    by_contra hnonunit
    have hnil : IsNilpotent a :=
      Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hnonunit
    exact (hnil.map A₀.val.toRingHom).not_isUnit ha⟩
  let f := IsLocalRing.ResidueField.mapAlgHom A₀.val
  let : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B) :=
    f.toRingHom.toAlgebra
  have : IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField B) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hf : ∀ a₀ : A₀, algebraMap (IsLocalRing.ResidueField A₀)
      (IsLocalRing.ResidueField B) (IsLocalRing.residue A₀ a₀) =
        IsLocalRing.residue B (a₀ : B) := fun _ ↦ rfl
  by_cases hα : IsAlgebraic (IsLocalRing.ResidueField A₀) (IsLocalRing.residue B x)
  · obtain ⟨A, hlocal, hle, hA, Q, hQ, a, ha, alg, htower, hres, hetale⟩ :=
      exists_popescu_algebraic_residue_enlargement k B p hp A₀ hA₀ x hx hf hα
    let := hlocal
    refine ⟨A, hlocal, hle, hA, Q, hQ, a, ha, 0, Fin.elim0, ?_, alg, htower,
      hres, Or.inl ⟨rfl, hetale⟩⟩
    exact fun j ↦ Fin.elim0 j
  · obtain ⟨A, hlocal, hle, hA, a, ha, alg, htower, hres, htrans, hgen⟩ :=
      exists_popescu_transcendental_residue_enlargement k B p hp A₀ hA₀ x hx hf hα
    let := hlocal
    let := alg
    refine ⟨A, hlocal, hle, hA, 1, le_rfl, a, ?_, 1, fun _ ↦ a,
      fun _ ↦ ha, alg, htower, hres, Or.inr ⟨rfl, fun _ ↦ htrans, ?_⟩⟩
    · simp [ha]
    · convert hgen using 2
      ext b
      simp


/-- The geometric enlargement, without any input or output differential basis.
Source: Stacks Project, smoothing.tex, Tags 07FH and 07FI; steps 1–4 and 6–8 of
lem-weil-pbc-popescu-unscaled-unit-basis.
(blueprint: lem-weil-pbc-popescu-unit-residue-extension).

Proof: Put B = Λ_q/(qΛ_q)^n and x = π(s). It is Artinian local and x is a unit.
Admissibility identifies the maximal ideal of A₀ with the contraction of that of B,
so its residue field F₀ embeds into K = B/m_B. Let α be the residue of x.
If α is transcendental, localize A₀[T] at m₀[T] and evaluate T at x. Reduction is
F₀[T] → K, which is injective, and localization has residue F₀(α). Its maximal
ideal is the extension of the nilpotent m₀; it is Noetherian, hence Artinian.
The fibre flatness criterion makes evaluation flat, since B is flat over A₀ and
its closed fibre is a vector space over F₀(α). A flat local map is faithfully flat,
hence injective. Its image A is Artinian local, flatly included in B, and has
m_A B = m_B. Its residue is essentially finite type over k, so the Artinian
residue criterion makes A essentially finite type. Take m = 1, y₀ = x, Q = 1,
and z = x⁻¹; the error is zero.
If α is algebraic, choose Q = p^e ≥ 1 with β = α^Q separable over F₀. Nilpotent
maximal ideals make A₀ and B henselian. Lift F₀(β)/F₀ to a finite étale local
A₀-algebra D and use the henselian étale retraction of D ⊗[A₀] B at the prime
specified by F₀(β) → K to map D into B. The same fibre flatness argument makes
this map injective and its image admissible. Its residue extension is finite
separable, hence formally étale. Take m = 0. Lift β⁻¹ to a unit z of A; the
residue of z x^Q - 1 is zero, so this error is nilpotent. In both cases the
residue algebra and scalar tower come from inclusion A₀ → A; the displayed
compatibility holds by the universal property of the residue quotient.
No differential basis is used in constructing A. -/
theorem exists_popescu_unit_residue_extension
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (s : Λ) (hs : s ∉ q) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (Q : ℕ) (_ : 1 ≤ Q) (z : Aˣ),
        IsNilpotent (((z : A) : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) *
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
            (algebraMap Λ (Localization.AtPrime q) s)) ^ Q - 1) ∧
        ∃ (m : ℕ) (y : Fin m → A),
          (∀ j, (y j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) s)) ∧
          ∃ (alg : Algebra (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A)),
            letI := alg
            IsScalarTower k (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) ∧
            (∀ a : A₀, algebraMap (IsLocalRing.ResidueField A₀)
              (IsLocalRing.ResidueField A) (IsLocalRing.residue A₀ a) =
                IsLocalRing.residue A (Subalgebra.inclusion hle a)) ∧
            ((m = 0 ∧ Algebra.FormallyEtale (IsLocalRing.ResidueField A₀)
                (IsLocalRing.ResidueField A)) ∨
              (m = 1 ∧
                (∀ j, Transcendental (IsLocalRing.ResidueField A₀)
                  (IsLocalRing.residue A (y j))) ∧
                IntermediateField.adjoin (IsLocalRing.ResidueField A₀)
                  (Set.range (fun j ↦ IsLocalRing.residue A (y j))) = ⊤)) := by
  let L := Localization.AtPrime q
  let J : Ideal L := q.map (algebraMap Λ L)
  have hJ : J = IsLocalRing.maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
  have hpow : J ^ n ≤ J := Ideal.pow_le_self (by omega)
  have hproper : J ^ n ≠ ⊤ := by
    intro h
    have hle := hpow
    rw [h, hJ] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top (top_le_iff.mp hle)
  let B := L ⧸ J ^ n
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (J ^ n)) Ideal.Quotient.mk_surjective
  have hmax : IsLocalRing.maximalIdeal B = J.map (Ideal.Quotient.mk (J ^ n)) := by
    exact (IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (J ^ n)) Ideal.Quotient.mk_surjective).symm.trans
        (congrArg (Ideal.map (Ideal.Quotient.mk (J ^ n))) hJ.symm)
  have : IsArtinianRing B := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    rw [Ideal.minimalPrimes, Set.mem_ofPred]
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simpa [← hJ] using hpow
    · intro P hP hle
      have hrad := Ideal.radical_mono hP.2
      rw [J.radical_pow (by omega), hJ, (IsLocalRing.maximalIdeal.isMaximal L).isPrime.radical,
        hP.1.radical] at hrad
      exact hrad
  let x : B := Ideal.Quotient.mk (J ^ n) (algebraMap Λ L s)
  have hx : IsUnit x :=
    (IsLocalization.map_units L (⟨s, hs⟩ : q.primeCompl)).map (Ideal.Quotient.mk (J ^ n))
  obtain ⟨A, hlocal, hle, hA, Q, hQ, a, ha, m, y, hy, alg, htower, hres, hcase⟩ :=
    exists_geometric_residue_power k B p hp A₀ (hmax ▸ hA₀) x hx
  let := hlocal
  have : IsArtinianRing A := hA.1
  have haunit : IsUnit a := by
    by_contra hnunit
    have hnil : IsNilpotent a :=
      Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hnunit
    have hnilB := hnil.map A.val.toRingHom
    have hz : IsLocalRing.residue B (a : B) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        (Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mp hnilB)
    have hnonzero := (IsLocalRing.residue_ne_zero_iff_isUnit (x ^ Q)).mpr (hx.pow Q)
    exact hnonzero (ha.symm.trans hz)
  obtain ⟨u, hu⟩ := haunit
  let z : Aˣ := u⁻¹
  have hz : IsNilpotent ((z : A).val * x ^ Q - 1) := by
    apply Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_mul, map_one, ← ha, ← hu]
    change IsLocalRing.residue B ((u⁻¹ : Aˣ) : A).val *
      IsLocalRing.residue B (u : A).val - 1 = 0
    rw [← map_mul, ← Subalgebra.coe_mul, Units.inv_mul]
    simp
  refine ⟨A, hlocal, hle, hmax ▸ hA, Q, hQ, z, hz, m, y, hy, alg, htower, hres, hcase⟩

end Algebra
