/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.LocalProperties.Basic
import WeilConjectures.RingTheory.PrincipalLocalizationConormalAtPrimeBaseChange
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import WeilConjectures.RingTheory.RegularSequenceConormal

/-!
# Stable conormal comparison with a complete intersection presentation

Source: Stacks Project, Algebra, proof of Lemma 00SC, last paragraph, using Lemma 00S6.
-/

@[expose] public section

universe u

namespace Ideal

set_option backward.isDefEq.respectTransparency false in
/-- Ideal generators span the conormal module over the quotient ring. -/
private theorem span_conormal_generators (D : Type u) [CommRing D]
    (c : ℕ) (f : Fin c → D) :
    Submodule.span (D ⧸ Ideal.span (Set.range f))
      (Set.range fun j ↦ (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) = ⊤ := by
  let I := Ideal.span (Set.range f)
  let e : Fin c → I.Cotangent := fun j ↦
    I.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩
  have hD : Submodule.span D (Set.range e) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
    refine Submodule.span_induction
      (p := fun z hz ↦ I.toCotangent ⟨z, hz⟩ ∈ Submodule.span D (Set.range e))
      ?_ ?_ ?_ ?_ x.property
    · rintro z ⟨j, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self j)
    · change I.toCotangent 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy hxx hyy
      change I.toCotangent (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ hxx hyy
    · intro r x hx hxx
      change I.toCotangent (r • ⟨x, hx⟩) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ r hxx
  apply (Submodule.restrictScalars_eq_top_iff D (D ⧸ I) I.Cotangent).mp
  rw [Submodule.restrictScalars_span D (D ⧸ I) Ideal.Quotient.mk_surjective]
  exact hD

set_option backward.isDefEq.respectTransparency false in
/-- A linear combination of equation classes is the class of the lifted combination. -/
private theorem conormal_sum (D : Type u) [CommRing D] (c : ℕ) (f a : Fin c → D) :
    let I := Ideal.span (Set.range f)
    ∑ j, Ideal.Quotient.mk I (a j) •
        I.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩ =
      I.toCotangent (∑ j, a j •
        (⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩ : I)) := by
  dsimp only
  rw [map_sum]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- A conormal basis detects the coefficients of a relation modulo the square. -/
private theorem coefficients_mem_of_conormal_basis (D : Type u) [CommRing D]
    (c : ℕ) (f a : Fin c → D)
    (b : Module.Basis (Fin c) (D ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent)
    (hb : ∀ j, b j = (Ideal.span (Set.range f)).toCotangent
      ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩)
    (ha : ∑ j, a j * f j ∈ Ideal.span (Set.range f) ^ 2) :
    ∀ j, a j ∈ Ideal.span (Set.range f) := by
  let I := Ideal.span (Set.range f)
  have hz : ∑ j, Ideal.Quotient.mk I (a j) • b j = 0 := by
    simp_rw [hb]
    rw [conormal_sum, Ideal.toCotangent_eq_zero]
    simpa only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul] using ha
  intro j
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ hz j)

set_option backward.isDefEq.respectTransparency false in
/-- Local conormal bases detect every coefficient by maximal-localization ideal membership. -/
private theorem coefficients_mem_of_locally_regular (D : Type u) [CommRing D]
    (c : ℕ) (f a : Fin c → D)
    (hreg : ∀ (m : Ideal D) [m.IsPrime], Ideal.span (Set.range f) ≤ m →
      RingTheory.Sequence.IsRegular (Localization.AtPrime m)
        (List.ofFn fun j ↦ algebraMap D (Localization.AtPrime m) (f j)))
    (ha : ∑ j, a j * f j ∈ Ideal.span (Set.range f) ^ 2) :
    ∀ j, a j ∈ Ideal.span (Set.range f) := by
  let I := Ideal.span (Set.range f)
  intro j
  apply Ideal.mem_of_localization_maximal
  intro m hm
  have : m.IsMaximal := hm
  by_cases hle : I ≤ m
  · let B := Localization.AtPrime m
    let g : Fin c → B := fun j ↦ algebraMap D B (f j)
    have hmap : I.map (algebraMap D B) = Ideal.span (Set.range g) := by
      rw [Ideal.map_span]
      congr 1
      exact Set.range_comp (algebraMap D B) f |>.symm
    obtain ⟨_, ⟨b, hb⟩, _⟩ :=
      RingTheory.Sequence.regularSequence_conormal_free B c g (hreg m hle)
    have ha' : ∑ j, algebraMap D B (a j) * g j ∈ Ideal.span (Set.range g) ^ 2 := by
      have hh := Ideal.mem_map_of_mem (algebraMap D B) ha
      rw [Ideal.map_pow, hmap] at hh
      simpa only [map_sum, map_mul] using hh
    rw [hmap]
    exact coefficients_mem_of_conormal_basis B c g (fun j ↦ algebraMap D B (a j))
      b hb ha' j
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime m) hle]
    exact Submodule.mem_top

set_option backward.isDefEq.respectTransparency false in
/-- The equation classes form a basis when the sequence is regular at every containing prime.
Source: Stacks Project, Algebra, Tag 00SV (3), the local independence argument. -/
private theorem basis_of_locally_regular (D : Type u) [CommRing D]
    (c : ℕ) (f : Fin c → D)
    (hreg : ∀ (p : Ideal D) [p.IsPrime], Ideal.span (Set.range f) ≤ p →
      RingTheory.Sequence.IsRegular (Localization.AtPrime p)
        (List.ofFn fun j ↦ algebraMap D (Localization.AtPrime p) (f j))) :
    Nonempty (Module.Basis (Fin c) (D ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent) := by
  classical
  let I := Ideal.span (Set.range f)
  let e : Fin c → I.Cotangent := fun j ↦
    I.toCotangent ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩
  have hli : LinearIndependent (D ⧸ I) e := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha j
    choose t ht using fun i ↦ Ideal.Quotient.mk_surjective (a i)
    have hz : I.toCotangent (∑ i, t i •
        (⟨f i, Ideal.subset_span (Set.mem_range_self i)⟩ : I)) = 0 := by
      rw [← conormal_sum]
      change ∑ i, Ideal.Quotient.mk I (t i) • e i = 0
      calc
        _ = ∑ i, a i • e i := Finset.sum_congr rfl fun i _ ↦
          congrArg (fun z : D ⧸ I ↦ z • e i) (ht i)
        _ = 0 := ha
    have hsq : ∑ i, t i * f i ∈ I ^ 2 := by
      rw [Ideal.toCotangent_eq_zero] at hz
      simpa only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul] using hz
    rw [← ht j]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (coefficients_mem_of_locally_regular D c f t hreg hsq j)
  let b : Module.Basis (Fin c) (D ⧸ I) I.Cotangent :=
    Module.Basis.mk hli (span_conormal_generators D c f).ge
  exact ⟨b⟩

/-- The local conormal module becomes finite free after adding the variables of a
complete intersection presentation of a principal localization.

Source: Stacks Project, Algebra, Lemma 00SC (lemma-lci), last paragraph of the proof,
through the equation from Lemma 00S6 (lemma-conormal-module-localize).
(blueprint: lem-weil-pbc-complete-intersection-presentation-stable-conormal)

Proof:
1. The map Q/J → S_g → S_q makes Q/J nontrivial. The spectrum homeomorphism
induced by e transfers the dimension identity to Q/J. Since t ≤ m, it becomes
`dim Spec(Q/J) + t = m`.
2. Apply the global complete intersection local regular sequence theorem at every
prime of Q containing J. The regular sequence conormal theorem gives a basis for
the conormal of the extended ideal at each such prime.
3. The equation classes span J/J². For a relation in J², local independence in step 2
puts each coefficient in the extended ideal at every maximal prime containing J.
At maximal primes not containing J the extended ideal is the whole localized ring.
Ideal.mem_of_localization_maximal therefore puts each coefficient in J. Lifting
quotient coefficients shows the equation classes are linearly independent globally.
Together with spanning this constructs a basis of J/J² over Q/J with index Fin t.
4. The principal localization comparison, base changed to S_q, identifies
`(I/I²)_q × S_q^m` with `(S_q tensor_(Q/J) J/J²) × S_q^n`.
Base change the basis of step 3 to S_q. Tensoring a finite power of Q/J gives
S_q^t. Compose these equivalences, then join the two finite powers using
`Fin t ⊕ Fin n ≃ Fin (t+n)`. No local free-summand cancellation is used.
-/
theorem stable_conormal_of_completeIntersection_presentation
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (g : MvPolynomial (Fin n) k ⧸ I) (hg : g ∉ q.asIdeal)
    (m t : ℕ) (f : Fin t → MvPolynomial (Fin m) k) (htm : t ≤ m)
    (e : (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] Localization.Away g)
    (hdim : topologicalKrullDim (PrimeSpectrum (Localization.Away g)) =
      ((m - t : ℕ) : WithBot ℕ∞)) :
    Nonempty
      ((LocalizedModule q.asIdeal.primeCompl I.Cotangent ×
          (Fin m → Localization.AtPrime q.asIdeal)) ≃ₗ[Localization.AtPrime q.asIdeal]
        (Fin (t + n) → Localization.AtPrime q.asIdeal)) := by
  classical
  let Q := MvPolynomial (Fin m) k
  let J : Ideal Q := Ideal.span (Set.range f)
  let S := MvPolynomial (Fin n) k ⧸ I
  let R := Localization.AtPrime q.asIdeal
  have hu : IsUnit (algebraMap S R g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff R q.asIdeal g).mpr hg
  let φ : (Q ⧸ J) →+* R := (IsLocalization.Away.lift g hu).comp e.toRingHom
  let : Algebra (Q ⧸ J) R := φ.toAlgebra
  have : Nontrivial (Q ⧸ J) := φ.domain_nontrivial
  have hd : topologicalKrullDim (PrimeSpectrum (Q ⧸ J)) =
      ((m - t : ℕ) : WithBot ℕ∞) := by
    let H := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    exact (H.isHomeomorph.topologicalKrullDim_eq H).trans hdim
  have hadd : topologicalKrullDim (PrimeSpectrum (Q ⧸ J)) +
      (t : WithBot ℕ∞) = (m : WithBot ℕ∞) := by
    rw [hd, ← Nat.cast_add, Nat.sub_add_cancel htm]
  have hreg : ∀ (p : Ideal Q) [p.IsPrime], J ≤ p →
      RingTheory.Sequence.IsRegular (Localization.AtPrime p)
        (List.ofFn fun j ↦ algebraMap Q (Localization.AtPrime p) (f j)) := by
    intro p hp hJp
    have h := MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension
      k m t f hadd p hJp
    simpa only [List.map_ofFn, Function.comp_def] using h
  obtain ⟨b⟩ := basis_of_locally_regular Q t f hreg
  obtain ⟨E⟩ := principalLocalization_conormal_atPrime_baseChange n I q g hg m J e
  let F : TensorProduct (Q ⧸ J) R J.Cotangent ≃ₗ[R] (Fin t → R) :=
    LinearEquiv.baseChange (Q ⧸ J) R _ _ b.equivFun ≪≫ₗ
      TensorProduct.piScalarRight (Q ⧸ J) R R (Fin t)
  let C : ((Fin t → R) × (Fin n → R)) ≃ₗ[R] (Fin (t + n) → R) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin t) (Fin n) R R).symm ≪≫ₗ
      LinearEquiv.piCongrLeft R (fun _ : Fin (t + n) ↦ R) finSumFinEquiv
  exact ⟨E ≪≫ₗ F.prodCongr (LinearEquiv.refl R (Fin n → R)) ≪≫ₗ C⟩

end Ideal
