/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
import WeilConjectures.RingTheory.PopescuLiftInduction
import WeilConjectures.RingTheory.PopescuLiftOne
import WeilConjectures.RingTheory.PopescuLiftSuccessor

/-!
# Lifting a Popescu resolution modulo eighth powers

Source: Stacks Project, Smoothing Ring Maps, Lemma 07F8, in Situation 07F7
(blueprint: lem-weil-pbc-popescu-lift-solution).
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem quotient_ann_transport {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    {I K : Ideal S} (he : I = K) (a : R)
    (h : ∀ x : S ⧸ K, a • x = 0 ↔ a ^ 2 • x = 0) :
    ∀ x : S ⧸ I, a • x = 0 ↔ a ^ 2 • x = 0 := by
  let e := (Ideal.quotientEquivAlgOfEq R he).toLinearEquiv
  intro x
  have hax := h (e x)
  have heq (b : R) : b • e x = 0 ↔ b • x = 0 := by
    rw [← e.map_smul, ← e.map_zero]
    exact e.injective.eq_iff
  exact (heq a).symm.trans (hax.trans (heq (a ^ 2)))

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
variable (r : ℕ) (π : Fin r → R)

local notation "J" => Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
local notation "J_A" => Ideal.map (algebraMap R A) J
local notation "J_Λ" => Ideal.map (algebraMap R Λ) J
local notation "R₀" => R ⧸ J
local notation "A₀" => A ⧸ J_A
local notation "Λ₀" => Λ ⧸ J_Λ

/-- A resolution modulo all the eighth powers lifts to the original local problem.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07F8, Situation 07F7
(blueprint: lem-weil-pbc-popescu-lift-solution).

The reduced algebra structures are Mathlib's `Ideal.Quotient.algebraQuotientMapQuotient`
instances; the reduced map and prime are specified by their compatibility with the quotient
maps, which determines them uniquely; the finite-presentation witness (true by base change)
is included only to type the recorded definition of `CanBePopescuResolved`.
The annihilator equalities are expressed pointwise as equivalences of vanishing products.

Proof (the seven steps of the node):
1. Induct on `r`, with the one-element case as base.
2. Reduction by an ideal in the inverse image of `q` remains Situation 07F7: the base is
Noetherian, the algebra finitely presented by base change, and the quotient prime is prime
(lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-tensor-quotient-base-change,
lem-weil-pbc-finite-presentation-base-change-composition). Iterated reductions agree.
3. Singular ideals map into singular ideals under base change: smooth principal
localizations remain smooth after base change, and take radicals
(def-weil-pbc-singular-ideal, lem-weil-pbc-smooth-ring-map-base-change-composition,
lem-weil-pbc-localization-base-change, lem-weil-pbc-tensor-quotient-base-change).
4. For one element, apply lem-weil-pbc-popescu-desingularize-lifting-apply (07F0) to a
resolution of the reduction. Its hypotheses are precisely the two annihilator equalities
and strict standardness. Obtain a finitely presented factorization through `B`, smooth
away from `π`, and the stated containment of the reduced singular ideal.
5. The image of `π` belongs to the singular ideal of `B`, since its localization is smooth
(lem-weil-pbc-polynomial-ring-smooth, lem-weil-pbc-smooth-ring-map-principal-localization,
lem-weil-pbc-localization-base-change, lem-weil-pbc-smooth-ring-map-base-change-composition).
Thus `π^8 Λ` lies in `h_B`, and the radical ideal of the reduced resolution lies in its image.
6. Lift an element of that ideal outside the quotient prime to show `h_B` is not contained
in `q`. Step 3 and the reduced resolution imply `h_A ≤ h_B`, giving a resolution
(def-weil-pbc-popescu-resolution).
7. For more than one element, first reduce by the first eighth power. The remaining
annihilator hypotheses identify with the original ones by iterated quotients; strict
standardness survives by lem-weil-pbc-strictly-standard-base-change (07CC). Apply induction
to the remaining elements, then the one-element case to lift back to `R`.
-/
theorem canBePopescuResolved_of_quotient_eighth_powers
    (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) (hr : 1 ≤ r)
    (hπ : ∀ i : Fin r, algebraMap R Λ (π i) ∈ q.asIdeal)
    (hR : ∀ (i : Fin r)
      (x : R ⧸ Ideal.span {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hΛ : ∀ (i : Fin r)
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin r, j.val < i.val ∧ y = algebraMap R Λ (π j) ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hstandard : ∀ i : Fin r, IsStrictlyStandardElement (R := R) (algebraMap R A (π i)))
    (hresolved :
      ∃ (_ : FinitePresentation R₀ A₀) (α₀ : A₀ →ₐ[R₀] Λ₀) (q₀ : PrimeSpectrum Λ₀),
        α₀.toRingHom.comp (Ideal.Quotient.mk J_A) =
          (Ideal.Quotient.mk J_Λ).comp α.toRingHom ∧
        PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
        CanBePopescuResolved α₀ q₀) :
    CanBePopescuResolved α q := by
  have lift : ∀ n, 1 ≤ n → PopescuEighthPowerLifting.{u, v, w} n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact popescuEighthPowerLifting_one
    | succ n hn ih =>
      intro R A Λ _ _ _ _ _ _ _ π α q hπ hR hΛ hstandard hresolved
      have hfirst := popescuEighthPowerLifting_tail n hn ih R A Λ π α q
        hπ hR hΛ hstandard hresolved
      apply popescuEighthPowerLifting_one R A Λ (fun _ ↦ π 0) α q
      · exact fun _ ↦ hπ 0
      · intro i
        apply quotient_ann_transport (R := R) _ (π 0) (hR 0)
        congr 1
        ext y
        simp
      · intro i
        apply quotient_ann_transport (R := R) _ (π 0) (hΛ 0)
        congr 1
        ext y
        simp
      · exact fun _ ↦ hstandard 0
      · exact hfirst
  exact lift r hr R A Λ π α q hπ hR hΛ hstandard hresolved

end Algebra
