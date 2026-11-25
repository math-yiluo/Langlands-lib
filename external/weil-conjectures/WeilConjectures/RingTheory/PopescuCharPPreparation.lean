/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.RingTheory.PopescuCharPPreparationCore
import WeilConjectures.RingTheory.PopescuCharPPreparationQuotient

/-!
# The auxiliary eighth-power problem in positive characteristic

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, items item-power
through item-eighth-resolve (blueprint: lem-weil-pbc-popescu-char-p-preparation).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Construct the auxiliary polynomial base and standardized algebra, together with an
essentially smooth factorization of the local eighth-power quotient problem. This is the
construction part of 07FJ; the statement does not assert a resolution of the original map.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ, items item-power
through item-eighth-resolve
(blueprint: lem-weil-pbc-popescu-char-p-preparation).

Proof:
1. Minimality and Noetherianity give a positive N with q^N in the localized singular
ideal. Choose generators a_j of the singular ideal and d = dim Lambda_q.
2. Form B = A[x_i,z_ij]/(x_i^(2N)-sum_j z_ij a_j). Its a_j and x_i localizations are
smooth over k[x]. Improve its presentation to a retract C with free differentials on
these opens. Choose c positive with x_i^c strictly standard; put e=8c and n=N+de.
3. Apply 07FH with the images of generators of A in Lambda_q/q^n to obtain the
polynomial localization P and its essentially smooth Artinian factor D. Flatness and
the height formula give parameters pi_i in the polynomial ring generating both
maximal ideals. Ogoma's lemma scales them to give the annihilator equalities for
pi_i t_i on the successive eighth-power quotients of R=k[y,t].
4. Inductively enlarge D using 07FI and use Ogoma again to obtain units delta_i and
coefficients lambda_ij with (delta_i pi_i)^(2N)=sum_j a_j lambda_ij, the annihilator
conditions in Lambda, and all their images in the enlarged D'. Clearing denominators
first and raising the clearing units to powers ensures these are identities in Lambda.
5. Map C to Lambda via its retraction to B, x_i to delta_i pi_i, and z_ij to lambda_ij.
Base change C along k[x] to R with x_i mapping to pi_i t_i, and set the lifting
parameters to (pi_i t_i)^c. Strict standardness survives base change. The annihilator
conditions survive positive powers by induction on the power. Smoothness of the a_j
localizations puts the original extended singular ideal in the new one.
6. Modulo the eighth powers of these parameters, the localization of Lambda at q
has dimension zero: the parameters generate its maximal ideal and a sufficiently
high power is in their power ideal. The reduced singular ideal is either outside the
prime, or that prime is minimal over it. These give the two alternatives below.
7. In the second alternative, t_i become units after localizing at the inverse-image
prime. Replace (pi_i t_i)^e by pi_i^e. The choice n=N+de puts both maximal-ideal
n-th powers in this ideal. Pass from C to B using the retraction. Over
R_0=P/p^n the map from B factors through D'[t], sending
z_ij to bar(lambda_ij) t_i^(2N) bar(delta_i)^(-2N). The defining relation follows
from step 4 and injectivity of the flat local map D' to Lambda_q/q^n. Quotient by
the pi_i^e and localize at the inverse-image prime. Essential smoothness survives
these base changes, giving E and the two maps in the statement.
8. When d=0, pad the parameter list by one zero. Its annihilator condition is
automatic and zero is strictly standard (all minor coefficients zero; a lift of zero
is in the relation ideal). The eighth-power ideal is unchanged. The same padding is
harmless in positive dimension. Finitely presented algebras and essentially smooth
algebras have representatives in max u v: use their finite polynomial presentations
and localization constructions. All the maps are transported to these representatives.
-/
theorem exists_popescu_char_p_preparation
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes) :
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin m) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin m) k) C)
      (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ),
      (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ ∧
      ∃ (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k),
        1 ≤ r ∧
        (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
        (∀ (i : Fin r)
          (x : MvPolynomial (Fin m) k ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ (i : Fin r)
          (x : Λ ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧
              y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ i, IsStrictlyStandardElement
          (R := MvPolynomial (Fin m) k) (algebraMap (MvPolynomial (Fin m) k) C (π i))) ∧
        let R := MvPolynomial (Fin m) k
        let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
        let J_C := J.map (algebraMap R C)
        let J_Λ := J.map (algebraMap R Λ)
        let R₀ := R ⧸ J
        let C₀ := C ⧸ J_C
        let Λ₀ := Λ ⧸ J_Λ
        ∃ (_ : FinitePresentation R₀ C₀) (γ₀ : C₀ →ₐ[R₀] Λ₀)
          (q₀ : PrimeSpectrum Λ₀),
          γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
            (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
          PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
          (¬ popescuIdeal γ₀ ≤ q₀.asIdeal ∨
            q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes ∧
            ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
            let P := Localization.AtPrime (q₀.asIdeal.under R₀)
            let L := Localization.AtPrime q₀.asIdeal
            letI := Localization.AtPrime.algebraOfLiesOver
              (q₀.asIdeal.under R₀) q₀.asIdeal
            ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
              EssentiallySmooth P E ∧
              ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L),
                g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L)
                  ((IsScalarTower.toAlgHom R₀ Λ₀ L).comp γ₀)
                  (fun _ _ ↦ Commute.all _ _)) := by
  obtain ⟨m, instΛ, towerΛ, C, instC, algC, algRC, towerC, fpC, β, γ,
    hcomp, hideal, r, π, hparam⟩ :=
    exists_popescu_char_p_preparation_core p hp α q hreg hminimal
  let _ := instΛ
  let _ := towerΛ
  let _ := instC
  let _ := algC
  let _ := algRC
  let _ := towerC
  let _ := fpC
  refine ⟨m, inferInstance, inferInstance, C, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, β, γ, hcomp, hideal, r, π, ?_⟩
  obtain ⟨hr, hπq, hR, hΛ, hstandard, hconstruction⟩ := hparam
  refine ⟨hr, hπq, hR, hΛ, hstandard, ?_⟩
  exact popescu_char_p_preparation_quotient p hp α q m C β γ r π
    ⟨hcomp, hideal⟩ ⟨hr, hπq, hR, hΛ, hstandard⟩ hconstruction


end Algebra
