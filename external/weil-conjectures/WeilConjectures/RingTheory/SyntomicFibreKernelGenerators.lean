/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicPolynomialFibreComparison
import WeilConjectures.RingTheory.LocalizedIdealConormalGeneratorBound
import WeilConjectures.RingTheory.LciConormalFreeRankCodimension
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Fibre generators in a fixed polynomial presentation

Source: Stacks Project, Tag 00SY, proof of (3) implies (2); Tag 00SC.
(blueprint: lem-weil-pbc-syntomic-fibre-kernel-generators).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

private theorem lift_generators_from_localized_quotient
    {P A : Type*} [CommRing P] [CommRing A] [Algebra P A]
    (M : Submonoid P) [IsLocalization M A] (I : Ideal P) (m : Ideal A)
    (hfg : ((I.map (algebraMap P A)).map (Ideal.Quotient.mk m)).FG) :
    ∃ (c : ℕ) (f : Fin c → P),
      c = ((I.map (algebraMap P A)).map (Ideal.Quotient.mk m)).spanFinrank ∧
      Ideal.span (Set.range f) ≤ I ∧
      I.map (algebraMap P A) ≤
        (Ideal.span (Set.range f)).map (algebraMap P A) ⊔ m := by
  classical
  let π := Ideal.Quotient.mk m
  let K := (I.map (algebraMap P A)).map π
  obtain ⟨s, hsCard, hsSpan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  change Ideal.span (s : Set (A ⧸ m)) = K at hsSpan
  have hlift (x : s) : ∃ (a : I) (t : M),
      (x : A ⧸ m) * π (algebraMap P A t) = π (algebraMap P A a) := by
    have hx : (x : A ⧸ m) ∈ K := by
      rw [← hsSpan]
      exact Submodule.subset_span x.property
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective π
      Ideal.Quotient.mk_surjective).mp hx
    obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff M A).mp hy
    exact ⟨a, t, by rw [← hxy, ← map_mul, hat]⟩
  choose a t hat using hlift
  let f : Fin s.card → P := fun i ↦ a (s.equivFin.symm i)
  let J := (Ideal.span (Set.range f)).map (algebraMap P A)
  have hfI : Ideal.span (Set.range f) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (a (s.equivFin.symm i)).property
  have hKJ : K ≤ J.map π := by
    rw [← hsSpan]
    apply Ideal.span_le.mpr
    intro x hx
    let z : s := ⟨x, hx⟩
    have hnum : π (algebraMap P A (a z)) ∈ J.map π := by
      apply Ideal.mem_map_of_mem
      apply Ideal.mem_map_of_mem
      apply Ideal.subset_span
      exact ⟨s.equivFin z, by simp [f]⟩
    have hu : IsUnit (π (algebraMap P A (t z))) :=
      (IsLocalization.map_units A (t z)).map π
    apply (Ideal.mul_unit_mem_iff_mem (J.map π) hu).mp
    exact (hat z).symm ▸ hnum
  refine ⟨s.card, f, hsCard, hfI, ?_⟩
  have hle := Ideal.map_le_iff_le_comap.mp hKJ
  simpa only [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, π, Ideal.mk_ker, J] using hle

/-- Bounded equations generate the presentation kernel modulo the base prime in the
polynomial local ring. Source: Stacks Project, Tag 00SY, proof of (3) implies (2),
choice of equations; Tag 00SC, conormal rank.
(blueprint: lem-weil-pbc-syntomic-fibre-kernel-generators).

Proof: Put p = q ∩ R and Q = φ⁻¹(q). Base change the surjection to κ(p) and identify
κ(p) ⊗ P with κ(p)[x₁,…,xₙ], and its quotient with κ(p) ⊗ S. Transport the prime
corresponding to q and the given complete-intersection neighbourhood to this quotient.
The conormal rank theorem gives a basis with c = n - d ≤ n elements. The images of
I = ker φ generate the fibre ideal and therefore its conormal residue vector space.
The residue field at the fibre prime equals that at Q. In this vector space the
images of I are a spanning set, so select c of them forming a basis and take their
original representatives fᵢ ∈ I. Every coefficient denominator from κ(p) comes
from R ∖ p, hence is invertible in P_Q; every polynomial denominator lies outside
the inverse-image prime, hence is invertible in P_Q as well. Multiplying a chosen
basis vector by such a denominator preserves a basis. The polynomial fibre ring
is Noetherian; its localized ideal is therefore finite. Nakayama in that local
ring makes the fᵢ generate the fibre ideal. The fibre local ring is P_Q/pP_Q,
by the fibre-local-ring comparison.
Taking the inverse image of this equality says I P_Q ⊆ (fᵢ)P_Q + pP_Q.
This argument needs no flatness. For c = 0 the fibre ideal is zero and the same
containment holds with the zero ideal. The specified prime excludes a zero fibre. -/
theorem exists_bounded_fibre_kernel_generators
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      c ≤ n ∧ Ideal.span (Set.range f) ≤ RingHom.ker φ.toRingHom ∧
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) ≤
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (Ideal.span (Set.range f)) ⊔
      Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap φ.toRingHom)))
        (q.asIdeal.comap (algebraMap R S)) := by
  classical
  let P := MvPolynomial (Fin n) R
  let Q := q.asIdeal.comap φ.toRingHom
  let A := Localization.AtPrime Q
  let p := q.asIdeal.comap (algebraMap R S)
  let m := p.map (algebraMap R A)
  let I := RingHom.ker φ.toRingHom
  let k := p.ResidueField
  let Ibar := I.map (MvPolynomial.map (algebraMap R k))
  obtain ⟨t, hcit, e, he⟩ := exists_syntomic_polynomial_fibre_comparison q n φ hφ hci
  obtain ⟨d, _, _, ⟨b⟩⟩ :=
    Ideal.exists_basis_cotangent_localization_of_completeIntersection n Ibar t hcit
  let B := Localization.AtPrime (t.asIdeal.comap (Ideal.Quotient.mk Ibar))
  let L := Ibar.map (algebraMap _ B)
  have hLfg : L.FG := Ibar.fg_of_isNoetherianRing.map _
  have hLrank : L.spanFinrank ≤ n := by
    exact (Ideal.spanFinrank_localized_ideal_le_of_conormal_generators Ibar
      Ibar.fg_of_isNoetherianRing t (n - d) b b.span_eq).trans (Nat.sub_le _ _)
  let K := (I.map (algebraMap P A)).map (Ideal.Quotient.mk m)
  have hKL : K.map e.toRingHom = L := by
    rw [Ideal.map_map]
    exact he
  have hKfg : K.FG := by
    have hh := hLfg.map e.symm.toRingHom
    rw [← hKL] at hh
    have hback : (K.map e.toRingHom).map e.symm.toRingHom = K :=
      Ideal.map_of_equiv e
    exact hback ▸ hh
  have hKrank : K.spanFinrank ≤ n := by
    have hr := Ideal.spanFinrank_map_eq_of_ringEquiv e K
    change (K.map e.toRingHom).spanFinrank = K.spanFinrank at hr
    rw [← hr, hKL]
    exact hLrank
  obtain ⟨c, f, hc, hfI, hgen⟩ :=
    lift_generators_from_localized_quotient Q.primeCompl I m hKfg
  exact ⟨c, f, hc.trans_le hKrank, hfI, hgen⟩

end Algebra
