/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftInduction
import WeilConjectures.RingTheory.PopescuLiftQuotientData

/-!
# Induction step for lifting Popescu resolutions

Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), case `r > 1`.
(blueprint: lem-weil-pbc-popescu-lift-successor)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Resolve the quotient by the first eighth power by applying the shorter-list hypothesis.
Source: Stacks Project, Lemma 07F8 (lemma-lift-solution), final paragraph.
(blueprint: lem-weil-pbc-popescu-lift-successor)

Proof:
1. Form R' = R/(π₀⁸), A' = A/(π₀⁸)A, Λ' = Λ/(π₀⁸)Λ and the induced prime q'.
The first-power ideal is contained in q because π₀ maps into q. Quotient rings are
Noetherian, and A' is finitely presented over R' by quotient tensor base change.
2. Use the tail π'ⱼ equal to the image of π(j+1) in R'. The third isomorphism theorem
identifies each preceding-power quotient of R' and Λ' with the corresponding original
quotient. Construct both maps by the quotient universal property; their composites fix
quotient classes. They intertwine multiplication, hence transport hR and hΛ at j+1.
3. Strict standardness survives base change by standardElements_baseChange; the tensor
quotient equivalence identifies the base-changed element with its quotient class.
4. The final tail quotient is isomorphic to the original total quotient, compatibly with
α and q. Transport hresolved through these algebra equivalences: smooth principal
localizations, and therefore the singular and extended radical ideals, correspond.
5. Apply ih over R' to the n tail elements, using hn. Its conclusion resolves the
first quotient. Record its induced map and prime with the quotient compatibility equations.
This concludes only resolvability after quotienting by π₀⁸, not the original problem. -/
theorem popescuEighthPowerLifting_tail
    (n : ℕ) (hn : 1 ≤ n) (ih : PopescuEighthPowerLifting.{u, v, w} n)
    (R : Type u) (A : Type v) (Λ : Type w)
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [IsNoetherianRing R] [FinitePresentation R A]
    (π : Fin (n + 1) → R) (α : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hπ : ∀ i : Fin (n + 1), algebraMap R Λ (π i) ∈ q.asIdeal)
    (hR : ∀ (i : Fin (n + 1))
      (x : R ⧸ Ideal.span {y | ∃ j : Fin (n + 1), j.val < i.val ∧ y = π j ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hΛ : ∀ (i : Fin (n + 1))
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin (n + 1), j.val < i.val ∧ y = algebraMap R Λ (π j) ^ 8}),
      π i • x = 0 ↔ π i ^ 2 • x = 0)
    (hstandard : ∀ i : Fin (n + 1), IsStrictlyStandardElement (R := R) (algebraMap R A (π i)))
    (hresolved : PopescuEighthPowerQuotientResolved (n + 1) π α q) :
    PopescuEighthPowerQuotientResolved 1 (fun _ ↦ π 0) α q := by
  obtain ⟨hfp, α₀, q₀, hα₀, hq₀, hπ₀, hR₀, hΛ₀, hstandard₀, hresolved₀⟩ :=
    popescuEighthPowerLifting_quotientData n hn R A Λ π α q hπ hR hΛ hstandard hresolved
  let J := Ideal.span (Set.range (fun _ : Fin 1 ↦ π 0 ^ 8))
  let R₀ := R ⧸ J
  let A₀ := A ⧸ Ideal.map (algebraMap R A) J
  let Λ₀ := Λ ⧸ Ideal.map (algebraMap R Λ) J
  let τ : Fin n → R₀ := fun j ↦ Ideal.Quotient.mk J (π j.succ)
  have htail := ih R₀ A₀ Λ₀ τ α₀ q₀ hπ₀ hR₀ hΛ₀ hstandard₀ hresolved₀
  exact ⟨hfp, α₀, q₀, hα₀, hq₀, htail⟩

end Algebra
