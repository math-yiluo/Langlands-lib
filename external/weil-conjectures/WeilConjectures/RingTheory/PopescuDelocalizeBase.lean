/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.StrictlyStandardElement
import WeilConjectures.RingTheory.SmoothStandardSmoothRetract
import WeilConjectures.RingTheory.StandardSmoothIncludeGenerators
import WeilConjectures.RingTheory.PopescuDelocalizeCertificate

/-!
# Delocalizing a smooth factorization

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F4
(blueprint: lem-weil-pbc-popescu-delocalize-base).
-/

@[expose] public section

universe u v w x

namespace Algebra

open MvPolynomial in
private theorem elementary_of_polynomial_certificate
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [FinitePresentation R B] {N M c : ℕ} (P : Presentation R B (Fin N) (Fin M))
    (hc : c ≤ min N M) (s : R) (a₀ : MvPolynomial (Fin N) R)
    (hdet : C s - a₀ * Matrix.det (fun i j : Fin c ↦
      pderiv (Fin.castLE (le_trans hc (min_le_left N M)) i)
        (P.relation (Fin.castLE (le_trans hc (min_le_right N M)) j))) ∈
      Ideal.span (Set.range P.relation))
    (hrel : ∀ j : Fin M, c ≤ j.val → C s * P.relation j ∈
      Ideal.span {f | ∃ k : Fin M, k.val < c ∧ f = P.relation k}) :
    IsElementaryStandardElement (R := R) (algebraMap R B s) := by
  refine ⟨N, M, c, P, hc, aeval P.val a₀, ?_, ?_⟩
  · have hz : aeval P.val (C s - a₀ * Matrix.det (fun i j : Fin c ↦
        pderiv (Fin.castLE (le_trans hc (min_le_left N M)) i)
          (P.relation (Fin.castLE (le_trans hc (min_le_right N M)) j)))) = 0 := by
      rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val] at hdet
      exact hdet
    rw [map_sub, map_mul, aeval_C, sub_eq_zero] at hz
    exact hz.trans (congrArg ((aeval P.val a₀) * ·) ((aeval P.val).map_det _))
  · intro j hj
    have hd : P.σ (algebraMap R B s) - C s ∈ Ideal.span (Set.range P.relation) := by
      rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
      simp
    have hg : P.relation j ∈ Ideal.span (Set.range P.relation) :=
      Ideal.subset_span ⟨j, rfl⟩
    have hh : (P.σ (algebraMap R B s) - C s) * P.relation j ∈
        (Ideal.span (Set.range P.relation)) ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hd hg
    have hsum := Ideal.add_mem _
      (Ideal.mem_sup_left (hrel j hj)) (Ideal.mem_sup_right hh)
    rw [Submodule.add_eq_sup]
    convert hsum using 1
    ring


/-- A smooth factorization after localizing the base descends to a finitely presented
factorization in which some denominator becomes elementary standard.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F4
(blueprint: lem-weil-pbc-popescu-delocalize-base).

Proof (the eleven steps of the blueprint node):
1. Use `lem-weil-pbc-smooth-retract-standard-smooth` to replace the smooth intermediate
   algebra by a standard smooth algebra with a retraction, preserving the factorization.
2. Choose finitely many generators and relations for `A` using
   `def-weil-pbc-finitely-presented-algebra`; their images in the target satisfy the relations.
3. By `lem-weil-pbc-standard-smooth-include-generators`, choose a standard smooth presentation
   whose first variables are the images of those generators and whose initial minor is a unit.
4. Rescale the extra variables by denominators so their images come from the target ring;
   `def-weil-pbc-polynomial-partial-derivative` shows the minor changes by a unit.
5. Use `lem-weil-pbc-polynomial-scalar-extension` and `lem-weil-pbc-localization-base-change`
   to identify the polynomial scalar extension with localization. Fractions have common
   denominators, equality can be cleared by a denominator, and derivatives commute with it.
6. Clear denominators in the smooth equations, preserving the presentation and unit minor.
7. Clear denominators in a relation expressing the inverse of the minor to obtain
   `s₀ = a₀ Δ + ∑ aⱼ fⱼ` in the polynomial ring over the original base.
8. Each original relation vanishes in the localized presentation, so some denominator
   multiplies it into the ideal of the smooth equations.
9. Each smooth equation vanishes after evaluation in the localized target, so some
   denominator kills its evaluation in the original target (`def-weil-pbc-module-localization`).
10. Quotient the polynomial ring by the denominator-scaled smooth equations and the original
    relations. This is finitely presented and gives both maps; agreement on generators proves
    their composite is the original map (`def-weil-pbc-mv-polynomial-ring`).
11. Multiply all chosen denominators. The product times every remaining relation belongs
    to the initial relation ideal. The identity in step 7, multiplied by the equation
    denominators, makes the product divisible by the initial Jacobian minor in the quotient.
    These are both conditions of `theorem-finite-etale-covers-proper-henselian--2` (1). -/
theorem exists_factorization_isElementaryStandardElement_of_localized_smooth
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [FinitePresentation R A] (α : A →ₐ[R] Λ) (S : Submonoid R)
    {B' : Type x} [CommRing B'] [Algebra (Localization S) B']
    [Smooth (Localization S) B']
    (β' : Localization (algebraMapSubmonoid A S) →ₐ[Localization S] B')
    (γ' : B' →ₐ[Localization S] Localization (algebraMapSubmonoid Λ S))
    (hfactor : γ'.comp β' =
      IsLocalization.mapₐ S (Localization S)
        (Localization (algebraMapSubmonoid A S)) (Localization (algebraMapSubmonoid Λ S)) α) :
    ∃ (B : Type (max u v w x)) (_ : CommRing B) (_ : Algebra R B)
      (_ : FinitePresentation R B) (β : A →ₐ[R] B) (γ : B →ₐ[R] Λ),
      γ.comp β = α ∧ ∃ s : S, IsElementaryStandardElement (R := R) (algebraMap R B s.val) := by
  classical
  obtain ⟨D, hD, hRD, hstd, ι, ρ, hρι, _⟩ :=
    Smooth.exists_standardSmooth_retract (Localization S) B'
  let := hD
  let := hRD
  let := hstd
  let βD := ι.comp β'
  let γD := γ'.comp ρ
  have hDfactor : γD.comp βD =
      IsLocalization.mapₐ S (Localization S)
        (Localization (algebraMapSubmonoid A S))
        (Localization (algebraMapSubmonoid Λ S)) α := by
    dsimp [βD, γD]
    rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc ρ, hρι, AlgHom.id_comp]
    exact hfactor
  obtain ⟨n, t, ⟨P⟩⟩ := Presentation.exists_presentation_fin R A
  obtain ⟨m, c, hc, Q, _, hmap, hval⟩ :=
    exists_standardSmoothPresentation_include_generators (R := Localization S) n
      (fun i ↦ βD (algebraMap A (Localization (algebraMapSubmonoid A S)) (P.val i)))
  obtain ⟨F, l, s, a₀, hl, hF, heval, hdet, hrel⟩ :=
    exists_delocalization_polynomial_certificate α S P hc Q βD γD hDfactor hmap hval
  let J : Ideal (MvPolynomial (Fin (n + m)) R) := Ideal.span (Set.range F)
  let B := ULift.{max v w x} (MvPolynomial (Fin (n + m)) R ⧸ J)
  let e : B ≃ₐ[R] (MvPolynomial (Fin (n + m)) R ⧸ J) := ULift.algEquiv
  let q : MvPolynomial (Fin (n + m)) R →ₐ[R] B :=
    e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  have hq : Function.Surjective q :=
    e.symm.surjective.comp (Ideal.Quotient.mkₐ_surjective R J)
  let G := Generators.ofAlgHom q hq
  have hG : MvPolynomial.aeval G.val = q := by
    ext i
    simp [G, Generators.ofAlgHom]
  let PB : Presentation R B (Fin (n + m)) (Fin (c + t)) :=
    { G with
      relation := F
      span_range_relation_eq_ker := by
        rw [G.ker_eq_ker_aeval_val, hG]
        ext f
        change f ∈ J ↔ q f = 0
        simp [q, e, Ideal.Quotient.eq_zero_iff_mem] }
  have : FinitePresentation R B := PB.finitePresentation_of_isFinite
  have hqzero {f : MvPolynomial (Fin (n + m)) R} (hf : f ∈ J) : q f = 0 := by
    simp [q, e, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
  have hker : RingHom.ker (MvPolynomial.aeval P.val).toRingHom ≤
      RingHom.ker (q.comp (MvPolynomial.rename (Fin.castAdd m))).toRingHom := by
    have hk : RingHom.ker (MvPolynomial.aeval P.val).toRingHom = P.ker :=
      P.ker_eq_ker_aeval_val.symm
    rw [hk, ← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change q (MvPolynomial.rename (Fin.castAdd m) (P.relation j)) = 0
    rw [← hF j]
    exact hqzero (Ideal.subset_span ⟨Fin.natAdd c j, rfl⟩)
  let β : A →ₐ[R] B := AlgHom.liftOfSurjective (MvPolynomial.aeval P.val)
    P.aeval_val_surjective (q.comp (MvPolynomial.rename (Fin.castAdd m))) hker
  have hJ : J ≤ RingHom.ker (MvPolynomial.aeval l).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact heval j
  let γ : B →ₐ[R] Λ := (Ideal.Quotient.liftₐ J (MvPolynomial.aeval l) hJ).comp e.toAlgHom
  have hγq : γ.comp q = MvPolynomial.aeval l := by
    ext i
    simp [γ, q, e, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  have hβα : γ.comp β = α := by
    apply (AlgHom.cancel_right P.aeval_val_surjective).mp
    dsimp only [β]
    rw [AlgHom.comp_assoc, AlgHom.liftOfSurjective_comp, ← AlgHom.comp_assoc,
      hγq, MvPolynomial.aeval_comp_rename]
    ext i
    simpa using hl i
  have hB : IsElementaryStandardElement (R := R) (algebraMap R B s.val) := by
    apply elementary_of_polynomial_certificate PB (le_min hc (Nat.le_add_right c t)) s.val a₀
    · simpa [PB, Fin.castLE, Fin.castAdd] using hdet
    · exact hrel
  exact ⟨B, inferInstance, inferInstance, inferInstance, β, γ, hβα, s, hB⟩

end Algebra
