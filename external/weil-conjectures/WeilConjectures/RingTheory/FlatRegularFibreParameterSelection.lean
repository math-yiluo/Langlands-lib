/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.FlatPolynomialAppendOfFibreRegularSequence
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Selecting polynomial parameters in a regular closed fibre

Source: Stacks Project, Smoothing Ring Maps, Tag 07FH, lemma-solution-modulo,
parameter selection for property (1); Algebra, Tags 00NQ, 00OP, 07DY and 00MP.
-/

@[expose] public section

set_option autoImplicit false
universe u v
namespace Algebra

private theorem parameters_from_generators
    (S : Type v) [CommRing S] [IsRegularLocalRing S]
    (r : ℕ) (ys : Fin r → S)
    (hys : Ideal.span (Set.range ys) = IsLocalRing.maximalIdeal S) :
    ∃ (e : ℕ) (s : Fin e → Fin r),
      IsLocalRing.IsRegularSystemOfParameters (List.ofFn (fun i ↦ ys (s i))) := by
  classical
  let a : Finset S := Finset.univ.image ys
  have ha : Ideal.span (a : Set S) = IsLocalRing.maximalIdeal S := by
    simpa [a] using hys
  obtain ⟨b, hb, hminimal⟩ := exists_minimal_le_of_wellFoundedLT
    (fun b : Finset S ↦ Ideal.span (b : Set S) = IsLocalRing.maximalIdeal S) a ha
  let d := (IsLocalRing.maximalIdeal S).spanFinrank
  have hd : ringKrullDim S = (d : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hcard : b.card = d :=
    (IsRegularLocalRing.minimal_generators_iff_card_eq_dimension S d hd b
      hminimal.prop).mp (by
        intro c hc hgen
        exact (not_le_of_gt hc) (hminimal.le_of_le hgen hc.le))
  have hidx : ∀ z : b, ∃ j : Fin r, ys j = (z : S) := by
    intro z
    have hz : (z : S) ∈ a := hb z.property
    simpa [a] using hz
  choose idx hidx using hidx
  let s : Fin b.card → Fin r := fun i ↦ idx (b.equivFin.symm i)
  have hvals : Set.range (fun i ↦ ys (s i)) = (b : Set S) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      change ys (s i) ∈ (b : Set S)
      rw [show ys (s i) = (b.equivFin.symm i : S) from hidx _]
      exact (b.equivFin.symm i).property
    · intro hz
      refine ⟨b.equivFin ⟨z, hz⟩, ?_⟩
      simpa [s] using hidx (b.equivFin.symm (b.equivFin ⟨z, hz⟩))
  refine ⟨b.card, s, ?_, ?_⟩
  · change Ideal.span {z | z ∈ List.ofFn (fun i ↦ ys (s i))} = _
    have hset : {z | z ∈ List.ofFn (fun i ↦ ys (s i))} =
        Set.range (fun i ↦ ys (s i)) := by
      ext z
      simp
    rw [hset, hvals]
    exact hminimal.prop
  · simp only [List.length_ofFn]
    rw [hcard, hd]

/-- For an initially flat polynomial coordinate map with regular local closed fibre,
a subset of given maximal-ideal generators gives a flat appended map. The selected
parameters generate the maximal ideal modulo the first-coordinate ideal.
Source: Stacks Project, Tag 07FH, lemma-solution-modulo, selection of parameters
for property (1); Algebra, Tags 00NQ, 00OP, 07DY and 00MP.
(blueprint: lem-weil-pbc-flat-regular-fibre-parameter-selection).

Proof: Write L = Λ_q, A₀ = k[X_j] at the contracted prime, and I₀ for the
extended prime in L. The quotient S = L/I₀ is regular local by hfibre. The images
of ys generate its maximal ideal. In its cotangent space choose a basis from
these finitely many generators and let s index that subset. Nakayama implies
that these selected images generate the maximal ideal of S. Their number equals
its embedding dimension, which equals its Krull dimension by regular locality.
They are a regular system of parameters, hence a regular sequence by 00NQ.
Lifting their generation from S gives m_L = I₀ + (ys (s i)/1).

Append the selected coordinates, obtaining A₁, the localization of k[X_j,Y_i]
at its contracted prime. The maps A₀ → A₁ → L are local and all three rings are
Noetherian. The closed fibre of A₀ → A₁ is κ(p₀)[Y_i] localized at its origin:
the added variables lie in the contracted prime, and their ideal is already
maximal over κ(p₀). By 00OP this fibre is regular local of dimension e, with the
Y_i as parameters. The map of closed fibres sends them to the selected regular
sequence in S, so 07DY gives fibre flatness. Apply 00MP with base A₀, middle A₁,
target L and finite nonzero L-module L, using hflat for its flatness over A₀.
It gives flatness over A₁. The induced map is the canonical localRingHom by
uniqueness of localization. If S is a field, take e = 0; if r = 0, the given
maximal ideal is zero and this case applies. Repeated generators cause no
problem because a basis is extracted from the spanning family. -/
theorem exists_flat_regular_fibre_parameter_selection
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (q : Ideal Λ) [q.IsPrime]
    (t r : ℕ) (xs : Fin t → Λ) (ys : Fin r → Λ)
    (hyq : ∀ i, ys i ∈ q)
    (hys : Ideal.span (Set.range (fun i ↦ algebraMap Λ (Localization.AtPrime q) (ys i))) =
      q.map (algebraMap Λ (Localization.AtPrime q)))
    (hflat : (Localization.localRingHom
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom) q
      (MvPolynomial.aeval (R := k) xs).toRingHom rfl).Flat)
    (hfibre : IsRegularLocalRing (Localization.AtPrime q ⧸
      (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q)).comp
          (MvPolynomial.aeval (R := k) xs).toRingHom))) :
    ∃ (e : ℕ) (s : Fin e → Fin r),
      let φ : MvPolynomial (Fin (t + e)) k →ₐ[k] Λ :=
        MvPolynomial.aeval (Fin.addCases xs (fun i ↦ ys (s i)))
      (Localization.localRingHom (q.comap φ.toRingHom) q φ.toRingHom rfl).Flat ∧
        q.map (algebraMap Λ (Localization.AtPrime q)) =
          (q.comap (MvPolynomial.aeval (R := k) xs).toRingHom).map
              ((algebraMap Λ (Localization.AtPrime q)).comp
                (MvPolynomial.aeval (R := k) xs).toRingHom) ⊔
            Ideal.span (Set.range (fun i ↦
              algebraMap Λ (Localization.AtPrime q) (ys (s i)))) := by
  classical
  let L := Localization.AtPrime q
  let f := (MvPolynomial.aeval (R := k) xs).toRingHom
  let I : Ideal L := (q.comap f).map ((algebraMap Λ L).comp f)
  let S := L ⧸ I
  have : IsRegularLocalRing S := hfibre
  have hIle : I ≤ IsLocalRing.maximalIdeal L := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    change (q.comap f).map ((algebraMap Λ L).comp f) ≤ _
    rw [← Ideal.map_map]
    exact Ideal.map_mono Ideal.map_comap_le
  let ybar : Fin r → S := fun i ↦ Ideal.Quotient.mk I (algebraMap Λ L (ys i))
  have hspan : Ideal.span (Set.range ybar) = IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← Localization.AtPrime.map_eq_maximalIdeal, ← hys,
      Ideal.map_span, ← Set.range_comp]
    rfl
  obtain ⟨e, s, hparams⟩ := parameters_from_generators S r ybar hspan
  have hseq : RingTheory.Sequence.IsRegular S (List.ofFn (fun i ↦ ybar (s i))) :=
    (IsRegularLocalRing.isRegular_and_quotients_of_generators S e
      (by simpa only [List.length_ofFn] using hparams.2.symm)
      (List.ofFn (fun i ↦ ybar (s i))) hparams).1
  refine ⟨e, s, ?_, ?_⟩
  · exact flat_polynomial_append_of_fibre_regular_sequence k Λ q t e xs
      (fun i ↦ ys (s i)) (fun i ↦ hyq (s i)) hflat hseq
  · change q.map (algebraMap Λ L) = I ⊔
      Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys (s i))))
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    let J : Ideal L := Ideal.span (Set.range (fun i ↦ algebraMap Λ L (ys (s i))))
    have hJmap : J.map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal S := by
      rw [Ideal.map_span, ← Set.range_comp]
      convert hparams.1 using 1
      congr 1
      ext z
      simp only [Set.mem_range, Function.comp_apply, List.mem_ofFn]
      rfl
    have heq : (IsLocalRing.maximalIdeal L).map (Ideal.Quotient.mk I) =
        J.map (Ideal.Quotient.mk I) := by
      rw [IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective, hJmap]
    have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk I)) heq
    simpa only [Ideal.comap_map_quotientMk, sup_eq_right.mpr hIle] using hcomap

end Algebra
