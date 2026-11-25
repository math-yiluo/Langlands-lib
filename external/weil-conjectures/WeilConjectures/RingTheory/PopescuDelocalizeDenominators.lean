/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.PopescuRescaledPresentation

/-!
# Denominator data for delocalization

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma Tag 07F4.
(blueprint: lem-weil-pbc-popescu-delocalize-denominators).
-/

@[expose] public section

universe u v w x

namespace Algebra

open MvPolynomial

private theorem clear_polynomial_ideal
    {R : Type u} [CommRing R] (S : Submonoid R) {ι : Type v}
    (I : Ideal (MvPolynomial ι R)) (p : MvPolynomial ι R)
    (hp : MvPolynomial.map (algebraMap R (Localization S)) p ∈
      I.map (MvPolynomial.map (algebraMap R (Localization S)))) :
    ∃ s : S, C s.val * p ∈ I := by
  let : Algebra (MvPolynomial ι R) (MvPolynomial ι (Localization S)) :=
    MvPolynomial.algebraMvPolynomial
  obtain ⟨q, hq, hqp⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (S.map (C (σ := ι))) (MvPolynomial ι (Localization S)) I p).mp hp
  obtain ⟨s, hs, rfl⟩ := hq
  exact ⟨⟨s, hs⟩, hqp⟩

private theorem unit_minor_certificate
    {R : Type u} {D : Type x} [CommRing R] [CommRing D]
    (S : Submonoid R) {ι : Type v} {c : ℕ}
    (f : Fin c → MvPolynomial ι R) (δ : MvPolynomial ι R)
    (e : MvPolynomial ι (Localization S) →+* D)
    (he : Function.Surjective e)
    (hker : RingHom.ker e = Ideal.span (Set.range (fun j ↦
      MvPolynomial.map (algebraMap R (Localization S)) (f j))))
    (hδ : IsUnit (e (MvPolynomial.map (algebraMap R (Localization S)) δ))) :
    ∃ (s : S) (a₀ : MvPolynomial ι R) (a : Fin c → MvPolynomial ι R),
      C s.val = a₀ * δ + ∑ j, a j * f j := by
  classical
  let ρ := MvPolynomial.map (algebraMap R (Localization S)) (σ := ι)
  let J := Ideal.span (insert δ (Set.range f))
  have hδJ : ρ δ ∈ J.map ρ := Ideal.mem_map_of_mem ρ (Ideal.subset_span (by simp))
  have hkerJ : RingHom.ker e ≤ J.map ρ := by
    rw [hker, Ideal.map_span]
    apply Ideal.span_mono
    intro p hp
    rcases hp with ⟨j, rfl⟩
    exact ⟨f j, by simp, rfl⟩
  obtain ⟨d, hd⟩ := isUnit_iff_exists_inv.mp hδ
  obtain ⟨b, hb⟩ := he d
  have herr : b * ρ δ - 1 ∈ RingHom.ker e := by
    simp only [RingHom.mem_ker, map_sub, map_mul, map_one, hb]
    rw [mul_comm, hd, sub_self]
  have h1 : (1 : MvPolynomial ι (Localization S)) ∈ J.map ρ := by
    have := (J.map ρ).sub_mem ((J.map ρ).mul_mem_left b hδJ) (hkerJ herr)
    simpa only [sub_sub_cancel] using this
  obtain ⟨s, hs⟩ := clear_polynomial_ideal S J 1 (by simpa using h1)
  simp only [mul_one] at hs
  obtain ⟨a₀, q, hq, heq⟩ := Ideal.mem_span_insert.mp hs
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq
  exact ⟨s, a₀, a, ha ▸ heq⟩

/-- The rescaling and denominator-clearing data before forming the quotient.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F4, proof from rescaling the
extra variables through choosing the elements `sⱼ` and `s'ⱼ`.
(blueprint: lem-weil-pbc-popescu-delocalize-denominators).

Proof: put `K = Localization S` and `T = R[X]`. For each extra index choose
`dᵢ ∈ S` and `lᵢ ∈ Λ` with `γ (Q.val i) = lᵢ/dᵢ`; for the first `n` indices
put `dᵢ = 1` and `lᵢ = α (P.val i)`, using `hfactor` and `hval`. The new generators
are `dᵢ * Q.val i`. If `qⱼ` are the old relations, substitute `Xᵢ/dᵢ` into them.
This is an automorphism of `K[X]`, inverse to substitution by `dᵢ * Xᵢ`, so the
new equations generate the new evaluation kernel. The chain rule scales row `i`
of the initial Jacobian by `dᵢ⁻¹`; hence its determinant still evaluates to a unit.
Multiply each equation by a common denominator of its finitely many coefficients,
obtaining `fⱼ ∈ T`. These multipliers are units in `K`, so the kernel ideal is
unchanged and the new minor still evaluates to a unit. The new generator values
map under `γ` to `lᵢ/1`.

Lift the inverse of this minor from `D` to `K[X]` using surjectivity of evaluation.
Then `1 = b₀ * Δ(f) + ∑ bⱼ * fⱼ` in `K[X]`, because the error lies in the
relation ideal. Choose a common denominator `d ∈ S` for the finitely many
coefficients of all `bⱼ`, obtaining polynomials `aⱼ` whose coefficient extensions
are `d * bⱼ`. The difference `C d - a₀ * Δ(f) - ∑ aⱼ * fⱼ` maps to zero in
`K[X]`. This polynomial ring is the localization of `T` at the constants from
`S`, so some `e ∈ S` kills that difference in `T`. Replace each `aⱼ` by
`C e * aⱼ` and take `s₀ = e * d`, giving the asserted exact identity in `T`.

Each renamed relation of `P` evaluates to zero in `D`: the first `n` generators
were fixed, and `β` preserves the original relations. Express that polynomial in
the localized ideal `(f)`. Clear the finitely many coefficients of the expression
and kill the residual polynomial equality by another localization annihilator,
just as above; their product is `sgⱼ`. Finally each `fⱼ` evaluates at `l` to zero
after localization, since it vanishes on the new generators of `D` and `γ` maps
those generators to `lᵢ/1`. The localization kernel criterion in `Λ` gives `sfⱼ`
killing this evaluation. Empty families use empty products and determinant `1`.
No injectivity of a localization map was used; the extra annihilators handle its
kernel, including when `0 ∈ S`. -/
theorem exists_delocalization_denominator_data
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    (α : A →ₐ[R] Λ) (S : Submonoid R) {n t m c : ℕ}
    (P : Presentation R A (Fin n) (Fin t)) (hc : c ≤ n + m)
    {D : Type x} [CommRing D] [Algebra (Localization S) D]
    (Q : SubmersivePresentation (Localization S) D (Fin (n + m)) (Fin c))
    (β : Localization (algebraMapSubmonoid A S) →ₐ[Localization S] D)
    (γ : D →ₐ[Localization S] Localization (algebraMapSubmonoid Λ S))
    (hfactor : γ.comp β =
      IsLocalization.mapₐ S (Localization S)
        (Localization (algebraMapSubmonoid A S)) (Localization (algebraMapSubmonoid Λ S)) α)
    (hmap : Q.map = Fin.castLE hc)
    (hval : ∀ i : Fin n, Q.val (Fin.castAdd m i) =
      β (algebraMap A (Localization (algebraMapSubmonoid A S)) (P.val i))) :
    ∃ (f : Fin c → MvPolynomial (Fin (n + m)) R)
      (l : Fin (n + m) → Λ) (s₀ : S) (a₀ : MvPolynomial (Fin (n + m)) R)
      (a : Fin c → MvPolynomial (Fin (n + m)) R) (sg : Fin t → S) (sf : Fin c → S),
      (∀ i : Fin n, l (Fin.castAdd m i) = α (P.val i)) ∧
      C s₀.val = a₀ * Matrix.det (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j)) +
        ∑ j, a j * f j ∧
      (∀ j : Fin t, C (sg j).val * rename (Fin.castAdd m) (P.relation j) ∈
        Ideal.span (Set.range f)) ∧
      ∀ j : Fin c, aeval l (C (sf j).val * f j) = 0 := by
  classical
  let K := Localization S
  let L := Localization (algebraMapSubmonoid Λ S)
  let ρ := MvPolynomial.map (algebraMap R K) (σ := Fin (n + m))
  have hfirst : ∀ i : Fin n, γ (Q.val (Fin.castAdd m i)) =
      algebraMap Λ L (α (P.val i)) := by
    intro i
    rw [hval]
    have hi := DFunLike.congr_fun hfactor
      (algebraMap A (Localization (algebraMapSubmonoid A S)) (P.val i))
    simpa [L, IsLocalization.mapₐ_coe, IsLocalization.map_eq] using hi
  obtain ⟨f, l, z, hl, hz, hγ, he, hker, hδ⟩ :=
    exists_rescaled_integral_presentation S hc Q γ (fun i ↦ α (P.val i)) hmap hfirst
  let e := (aeval z : MvPolynomial (Fin (n + m)) K →ₐ[K] D).toRingHom
  change RingHom.ker e = Ideal.span (Set.range (fun j ↦ ρ (f j))) at hker
  let δ := Matrix.det (fun i j : Fin c ↦ pderiv (Fin.castLE hc i) (f j))
  obtain ⟨s₀, a₀, a, ha⟩ := unit_minor_certificate S f δ e he hker hδ
  have hg : ∀ j : Fin t, ∃ s : S,
      C s.val * rename (Fin.castAdd m) (P.relation j) ∈ Ideal.span (Set.range f) := by
    intro j
    apply clear_polynomial_ideal S
    rw [Ideal.map_span, ← Set.range_comp']
    rw [← hker]
    change e (ρ (rename (Fin.castAdd m) (P.relation j))) = 0
    have hcomp : (e.comp ρ).comp ((rename (Fin.castAdd m)).toRingHom) =
        β.toRingHom.comp ((algebraMap A (Localization (algebraMapSubmonoid A S))).comp
          (aeval P.val).toRingHom) := by
      ext r
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          rename_C, map_C, aeval_C, e, ρ]
        change algebraMap K D (algebraMap R K r) =
          β (algebraMap A (Localization (algebraMapSubmonoid A S)) (algebraMap R A r))
        rw [← IsScalarTower.algebraMap_apply R A
          (Localization (algebraMapSubmonoid A S)),
          IsScalarTower.algebraMap_apply R K (Localization (algebraMapSubmonoid A S))]
        exact (β.commutes (algebraMap R K r)).symm
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          rename_X, map_X, aeval_X, e, ρ]
        change z (Fin.castAdd m r) =
          β (algebraMap A (Localization (algebraMapSubmonoid A S)) (P.val r))
        rw [hz, hval]
    have hj := DFunLike.congr_fun hcomp (P.relation j)
    change e (ρ (rename (Fin.castAdd m) (P.relation j))) =
      β (algebraMap A (Localization (algebraMapSubmonoid A S))
        (aeval P.val (P.relation j))) at hj
    simpa only [P.aeval_val_relation, map_zero] using hj
  have hf : ∀ j : Fin c, ∃ s : S, aeval l (C s.val * f j) = 0 := by
    intro j
    have hfj : e (ρ (f j)) = 0 := by
      apply RingHom.mem_ker.mp
      rw [hker]
      exact Ideal.mem_span_range_self
    have hzero : algebraMap Λ L (aeval l (f j)) = 0 := by
      have hcompat (p : MvPolynomial (Fin (n + m)) R) :
          γ (e (ρ p)) = algebraMap Λ L (aeval l p) := by
        induction p using MvPolynomial.induction_on with
        | C r =>
          simp only [e, ρ, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
          rw [γ.commutes, ← IsScalarTower.algebraMap_apply R K L,
            ← IsScalarTower.algebraMap_apply R Λ L]
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p i hp =>
          simp only [map_mul, ρ, map_X, e, AlgHom.toRingHom_eq_coe,
            RingHom.coe_coe, aeval_X, hγ]
          exact congrArg (· * algebraMap Λ L (l i)) hp
      have hj := hcompat (f j)
      simpa only [hfj, map_zero] using hj.symm
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (algebraMapSubmonoid Λ S) L
      (aeval l (f j))).mp hzero
    obtain ⟨r, hr, hrval⟩ := s.property
    refine ⟨⟨r, hr⟩, ?_⟩
    simpa only [map_mul, aeval_C, hrval] using hs
  choose sg hsg using hg
  choose sf hsf using hf
  exact ⟨f, l, s₀, a₀, a, sg, sf, hl, ha, hsg, hsf⟩

end Algebra
