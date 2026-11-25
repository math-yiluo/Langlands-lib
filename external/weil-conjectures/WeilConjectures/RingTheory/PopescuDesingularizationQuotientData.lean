/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.PopescuDesingularizationSubstitution
import WeilConjectures.RingTheory.PopescuDesingularizationInvertedQuotient
import WeilConjectures.RingTheory.StrictlyStandardLocalizationSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Flat

/-! # Quotient data for the desingularization construction

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, through the construction
of `B'` and the two observations on its remaining relations.
-/

@[expose] public section

universe u v w

namespace Algebra

open MvPolynomial

private theorem flat_atPrime_of_smoothAtPrime
    {R : Type u} [CommRing R] {S : Type w} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (h : IsSmoothAtPrime R q) :
    Module.Flat R (Localization.AtPrime q.asIdeal) := by
  obtain ⟨d, hd, hsm⟩ := h
  let T := Localization.Away d
  let B := Localization.AtPrime q.asIdeal
  let : Smooth R T := hsm
  have hle : Submonoid.powers d ≤ q.asIdeal.primeCompl := by
    rw [Submonoid.powers_le]
    exact hd
  let : Algebra T B := IsLocalization.localizationAlgebraOfSubmonoidLe T B
    (Submonoid.powers d) q.asIdeal.primeCompl hle
  have : IsScalarTower S T B := IsLocalization.localization_isScalarTower_of_submonoid_le
    T B (Submonoid.powers d) q.asIdeal.primeCompl hle
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap S T)) B :=
    IsLocalization.isLocalization_of_submonoid_le T B
      (Submonoid.powers d) q.asIdeal.primeCompl hle
  have : Module.Flat T B :=
    IsLocalization.flat B (q.asIdeal.primeCompl.map (algebraMap S T))
  have : IsScalarTower R T B := IsScalarTower.to₁₃₄ R S T B
  exact Module.Flat.trans R T B

private theorem smoothAtPrime_of_affine_mod_parameter
    (R : Type u) [CommRing R] (π : R) (n c : ℕ)
    (r : Fin c → Fin n → R)
    (g e : Fin c → MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R)
    (hg : ∀ j, g j =
      X (σ := ULift.{w} (Fin c ⊕ Fin n)) (ULift.up (Sum.inl j)) +
      ∑ i, C (r j i) * X (ULift.up (Sum.inr i)) + C π * e j)
    (q : PrimeSpectrum (MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R ⧸
      Ideal.span (Set.range g)))
    (hπ : algebraMap R _ π ∈ q.asIdeal) : IsSmoothAtPrime R q := by
  classical
  let Q := MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R
  let G := Ideal.span (Set.range g)
  let S := Q ⧸ G
  let P : PreSubmersivePresentation R S (ULift.{w} (Fin c ⊕ Fin n)) (Fin c) :=
    PreSubmersivePresentation.naive (v := g) (fun j ↦ ULift.up (Sum.inl j))
      (fun i j h ↦ Sum.inl_injective (ULift.up_injective h))
  let d := P.jacobian
  let f : Q →+* S ⧸ q.asIdeal :=
    (Ideal.Quotient.mk q.asIdeal).comp (Ideal.Quotient.mk G)
  have hfπ : f (C π) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hπ
  have hentry (i j : Fin c) : f (P.jacobiMatrix i j) = if i = j then 1 else 0 := by
    rw [P.jacobiMatrix_apply]
    change f (pderiv (ULift.up (Sum.inl i)) (g j)) = _
    rw [hg j]
    by_cases hij : i = j
    · subst j
      simp [map_add, map_sum, hfπ]
    · simp [map_add, map_sum, hfπ, hij]
  have hd : d ∉ q.asIdeal := by
    have heq : (Ideal.Quotient.mk q.asIdeal) d = 1 := by
      rw [show d = P.jacobian from rfl, P.jacobian_eq_jacobiMatrix_det]
      change f P.jacobiMatrix.det = 1
      rw [RingHom.map_det]
      have hm : f.mapMatrix P.jacobiMatrix = 1 := by
        ext i j
        simp [RingHom.mapMatrix_apply, hentry, Matrix.one_apply]
      rw [hm, Matrix.det_one]
    intro hmem
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact zero_ne_one (hz.symm.trans heq)
  let T := Localization.Away d
  let P' := (PreSubmersivePresentation.localizationAway T d).comp P
  have hu : IsUnit P'.jacobian := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit d).mul
      (IsLocalization.Away.algebraMap_isUnit d)
  let Ps : SubmersivePresentation R T _ _ := ⟨P', hu⟩
  have : IsStandardSmooth R T := Ps.isStandardSmooth
  exact ⟨d, hd, inferInstance⟩

/-- The construction part of the desingularization argument, before eliminating the
remaining relations locally. No conclusion about the annihilator ideal or singular ideal
is assumed here.

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07CR, presentation through the
paragraph defining `B'` and the two observations on `f_{c+j}`
(blueprint: lem-weil-pbc-popescu-desingularization-quotient-data).

Proof: choose a strictly standard presentation and translate the variables by lifts of
 their images under the section. The translated variables map to `π⁴ λᵢ` in `Λ`, and the
constant terms of all relations lie in `π⁴R`. Applying the section to the Jacobian-minor
identity produces a scalar `uπ`, with `u` congruent to one modulo `π³`, in the ideal of
constant Jacobian minors. The scalar left-inverse lemma gives a matrix `s` with product
`uπ` times the identity. Substitute `xᵢ = π² ∑ sᵢⱼ vⱼ + π³ wᵢ`. Expanding each of the
first `c` equations constructs `gⱼ`, rather than cancelling `π³`: its constant and linear
terms and every higher monomial are explicitly divisible by `π³`. Thus `fⱼ = π³gⱼ`,
and `gⱼ` reduces to `vⱼ + ∑ rⱼᵢwᵢ` modulo `π`. Take the finitely presented algebra
`S = R[v,w]/(g)` (lift its universe if necessary). Let `K` be generated by the remaining
substituted `f`. Every generator is divisible by `π²`, so `K ≤ (π²)`. Substitution into
the strictly standard ideal-square relation gives `(π)K ≤ K²`. The quotient `S/K` is
the algebra `B` of the source. Evaluation at `v=0`, `wᵢ=πλᵢ` induces the factorization:
the `gⱼ` evaluate into `πΛ` and are killed by `π³`; stability of annihilators for all
positive powers, by induction, makes these evaluations zero. After inverting `π`,
eliminate `w` to identify `B_π` with `A_π[v]`; strictly standard localization and smooth
composition make it smooth. At a prime of `S` containing `π`, its residue-field fibre
eliminates `v` and has identity Jacobian minor. It is standard smooth of dimension `n`.
Equation-count flatness gives flatness of the prime localization over `R`; the flat
smooth-fibre criterion gives smoothness at the prime. These are exactly the two local
properties stated below. -/
theorem exists_desingularization_quotient_data
    (R : Type u) (Λ : Type v) (A : Type w)
    [CommRing R] [CommRing Λ] [CommRing A]
    [Algebra R Λ] [Algebra R A] [IsNoetherianRing R] [FinitePresentation R A]
    (π : R) (α : A →ₐ[R] Λ)
    (hΛ : ∀ l : Λ, l * algebraMap R Λ π = 0 ↔
      l * (algebraMap R Λ π) ^ 2 = 0)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hρ : ∃ ρ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (R ⧸ Ideal.span {π ^ 4}),
      ∀ (a : A) (r : R),
        ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ r →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (algebraMap R Λ r)) :
    ∃ (S : Type (max u w)) (_ : CommRing S) (_ : Algebra R S),
      FinitePresentation R S ∧
      ∃ K : Ideal S,
        K ≤ Ideal.span {(algebraMap R S π) ^ 2} ∧
        Ideal.span {algebraMap R S π} * K ≤ K ^ 2 ∧
        FinitePresentation R (S ⧸ K) ∧
        ∃ (β : (S ⧸ K) →ₐ[R] Λ) (aB : A →ₐ[R] (S ⧸ K)),
          β.comp aB = α ∧
          Smooth R (Localization.Away (algebraMap R (S ⧸ K) π)) ∧
          ∀ q : PrimeSpectrum S, algebraMap R S π ∈ q.asIdeal →
            IsSmoothAtPrime R q ∧ Module.Flat R (Localization.AtPrime q.asIdeal) := by
  classical
  obtain ⟨n, m, c, P, hc, s, lam, r, g, e, hg, hfirst, hdiv, hquad, hα⟩ :=
    exists_desingularization_substitution R Λ A π α hstandard hρ
  let Q := MvPolynomial (ULift.{w} (Fin c ⊕ Fin n)) R
  let ξ : Fin n → Q := fun i ↦
    C π ^ 2 * ∑ k, C (s i k) * X (ULift.up (Sum.inl k)) +
      C π ^ 3 * X (ULift.up (Sum.inr i))
  let F : Fin m → Q := fun j ↦ aeval (R := R) ξ (P.relation j)
  change ∀ j, F (Fin.castLE hc j) = C π ^ 3 * g j at hfirst
  let G : Ideal Q := Ideal.span (Set.range g)
  let I : Ideal Q := Ideal.span (Set.range F)
  let S := Q ⧸ G
  let qS : Q →ₐ[R] S := Ideal.Quotient.mkₐ R G
  let K : Ideal S := I.map qS.toRingHom
  let B := S ⧸ K
  let qB : S →ₐ[R] B := Ideal.Quotient.mkₐ R K
  have hfpS : FinitePresentation R S :=
    FinitePresentation.quotient (Submodule.fg_span (Set.finite_range g))
  have hfpB : FinitePresentation R B := by
    let : FinitePresentation R S := hfpS
    exact FinitePresentation.quotient
      (Ideal.FG.map (Submodule.fg_span (Set.finite_range F)) qS.toRingHom)
  have hdivI : I ≤ Ideal.span {C π ^ 2} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hdiv j
  have hqSπ : qS.toRingHom (C π) = algebraMap R S π := qS.commutes π
  have hdivK : K ≤ Ideal.span {(algebraMap R S π) ^ 2} := by
    have h := Ideal.map_mono (f := qS.toRingHom) hdivI
    simpa only [K, Ideal.map_span, Set.image_singleton, map_pow,
      RingHom.coe_coe, hqSπ] using h
  have hquadI : Ideal.span {C π} * I ≤ G + I ^ 2 := by
    rw [Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨a, ha, b, ⟨j, rfl⟩, rfl⟩
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact hquad j
  have hmapG : G.map qS.toRingHom = ⊥ := by
    change G.map (Ideal.Quotient.mk G) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have hquadK : Ideal.span {algebraMap R S π} * K ≤ K ^ 2 := by
    have hqSπ' : qS (C π) = algebraMap R S π := qS.commutes π
    have h := Ideal.map_mono (f := qS.toRingHom) hquadI
    change (Ideal.span {C π} * I).map qS.toRingHom ≤ (G + I ^ 2).map qS.toRingHom at h
    rw [Ideal.map_mul, Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_pow,
      hmapG, bot_sup_eq, Ideal.map_span, Set.image_singleton] at h
    change Ideal.span {qS.toRingHom (C π)} * K ≤ K ^ 2 at h
    simpa [hqSπ, hqSπ', K] using h
  let δ : MvPolynomial (Fin n) R →ₐ[R] B := (qB.comp qS).comp (aeval ξ)
  have hδ : P.ker ≤ RingHom.ker δ.toRingHom := by
    rw [← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change qB (qS (F j)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem qS.toRingHom (Ideal.subset_span ⟨j, rfl⟩)
  let aB : A →ₐ[R] B := AlgHom.liftOfSurjective (aeval P.val) P.aeval_val_surjective δ
    (by
      convert hδ using 1
      exact P.ker_eq_ker_aeval_val.symm)
  let ε : Q →ₐ[R] Λ := aeval (fun x ↦ match x.down with
    | Sum.inl _ => 0
    | Sum.inr i => algebraMap R Λ π * lam i)
  have hεξ : ε.comp (aeval ξ) = α.comp (aeval P.val) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ε, ξ, Q, hα, pow_succ, mul_assoc]
  have hεF (j : Fin m) : ε (F j) = 0 := by
    change (ε.comp (aeval ξ)) (P.relation j) = 0
    rw [hεξ]
    simp
  have hεg (j : Fin c) : ε (g j) = 0 := by
    have hlin : ε (g j) = algebraMap R Λ π *
        (∑ i, algebraMap R Λ (r j i) * lam i + ε (e j)) := by
      rw [hg j]
      simp only [map_add, map_sum, map_mul]
      dsimp [ε, Q]
      simp only [aeval_X, aeval_C]
      simp only [zero_add, mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hkill : algebraMap R Λ π ^ 3 * ε (g j) = 0 := by
      have h := hεF (Fin.castLE hc j)
      rw [hfirst j] at h
      have hεC : ε (C π) = algebraMap R Λ π := ε.commutes π
      convert h using 1
      simp [hεC]
    let t := ∑ i, algebraMap R Λ (r j i) * lam i + ε (e j)
    have ht4 : t * algebraMap R Λ π ^ 4 = 0 := by
      rw [hlin] at hkill
      simpa [t, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hkill
    have ht3 : t * algebraMap R Λ π ^ 3 = 0 := by
      have h := (hΛ (t * algebraMap R Λ π ^ 2)).mpr
        (by simpa [pow_succ, mul_assoc] using ht4)
      simpa [pow_succ, mul_assoc] using h
    have ht2 : t * algebraMap R Λ π ^ 2 = 0 := by
      have h := (hΛ (t * algebraMap R Λ π)).mpr
        (by simpa [pow_succ, mul_assoc] using ht3)
      simpa [pow_two, mul_assoc] using h
    rw [hlin, mul_comm]
    exact (hΛ t).mpr ht2
  have hGε : G ≤ RingHom.ker ε.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hεg j
  let εS : S →ₐ[R] Λ := Ideal.Quotient.liftₐ G ε hGε
  have hKε : K ≤ RingHom.ker εS.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hεF j
  let β : B →ₐ[R] Λ := Ideal.Quotient.liftₐ K εS hKε
  have hcomp : β.comp aB = α := by
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := P.aeval_val_surjective a
    change β (aB ((aeval P.val) p)) = α ((aeval P.val) p)
    rw [AlgHom.liftOfSurjective_apply]
    change (ε.comp (aeval ξ)) p = _
    rw [hεξ]
    rfl
  obtain ⟨eqv⟩ := desingularization_inverted_quotient_equiv R A π n m c P hc s g hfirst
  have hsmooth : Smooth R (Localization.Away (algebraMap R B π)) := by
    let Aπ := Localization.Away (algebraMap R A π)
    have : Smooth R Aπ :=
      smooth_localizationAway_of_isStrictlyStandardElement _ hstandard
    have : Smooth Aπ (MvPolynomial (Fin c) Aπ) :=
      ⟨inferInstance, inferInstance⟩
    have : Smooth R (MvPolynomial (Fin c) Aπ) := Smooth.comp R Aπ _
    exact Smooth.of_equiv eqv.symm
  refine ⟨S, inferInstance, inferInstance, hfpS, K, hdivK, hquadK, hfpB,
    β, aB, hcomp, hsmooth, ?_⟩
  intro q hπ
  have hsm := smoothAtPrime_of_affine_mod_parameter R π n c r g e hg q hπ
  exact ⟨hsm, flat_atPrime_of_smoothAtPrime q hsm⟩

end Algebra
