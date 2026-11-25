/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.PolynomialResidueFiniteCoefficientModel
import WeilConjectures.RingTheory.PolynomialCompletedFibreCompatibleProduct
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct

/-!
# Finite product presentation of extended polynomial formal fibres

Source: Stacks Project, More on Algebra, proof of Lemma 07PU, first paragraph.
(blueprint: lem-weil-pbc-polynomial-formal-fibre-finite-reduction)
-/

@[expose] public section

universe u

namespace Polynomial

set_option linter.unusedVariables false in
/-- A finite purely inseparable base change of a nonzero polynomial formal fibre above
zero is a finite product of linear-residue formal fibres over complete local domains.
This is a ring presentation, with no regularity assertion.
Source: Stacks Project, More on Algebra, proof of Lemma 07PU, first paragraph.
(blueprint: lem-weil-pbc-polynomial-formal-fibre-finite-reduction)

Proof:
Fix L/κ(r) as in the statement. Since r is nonzero and above zero, its extension to
K[X] is a nonzero maximal ideal, where K is the fraction field of A. Thus κ(r), and
hence L, is finite over K. Choose finitely many generators of L/K. Multiply them by
a common nonzero coefficient denominator to make them integral over A, by clearing
the coefficients of their monic equations with successive powers of the denominator.
Their generated A-subalgebra B inside L is finite over A, a domain, and has fraction
field L. Tag 0325 makes it Noetherian, local and complete, with its unique maximal
ideal above that of A. Evaluation B[X] → L sends X to its image in κ(r). Its prime
kernel s contracts to zero in B; it is nonzero because a nonzero element of r remains
nonzero under the injective coefficient extension A[X] → B[X]. The image B[X]/s
contains B inside L, so its fraction field, hence κ(s), is L. The canonical B-algebra
structure on κ(s) therefore makes it a fraction field of B.
Apply Tag 07N9 to the finite extension A[X] → B[X] at q. Its completion base change
is a finite product of the completions at primes qᵢ above q. Each qᵢ is maximal by
integrality. Its contraction to B is the unique prime above the maximal ideal of A,
hence the maximal ideal of B. Tensor with L and use associativity and finite-product
distributivity to identify L ⊗[κ(r)] r.Fiber C with the product of the s-fibres of
these completions. If s is not contained in qᵢ, an element of s outside qᵢ is both
zero and invertible in the fibre, so that factor is zero. Removing zero factors from
a product is a ring isomorphism, with the unique zero coordinate supplied by its
inverse. Index the remaining finitely many qᵢ by Fin n; for each let Bᵢ be a copy of
B, sᵢ a copy of s, and retain the indicated qᵢ. All requested structures and ideal
relations follow from the construction. No factors is permitted: the empty product
is the zero ring. All rings Bᵢ lie in the universe of L, as subalgebras of L. -/
theorem formalFiber_finiteExtension_reduction
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) (hp : p.Prime) [CharP (Localization.AtPrime (⊥ : Ideal A)) p]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime] (hrq : r ≤ q) (hr : r ≠ ⊥)
    (hrA : r.comap (Polynomial.C : A →+* Polynomial A) = ⊥)
    (L : Type u) [Field L] [Algebra r.ResidueField L]
    [Module.Finite r.ResidueField L] [IsPurelyInseparable r.ResidueField L] :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∃ (n : ℕ) (B : Fin n → Type u) (rings : ∀ i, CommRing (B i)),
      letI := rings
      ∃ (domains : ∀ i, IsDomain (B i)) (noeth : ∀ i, IsNoetherianRing (B i))
        (locals : ∀ i, IsLocalRing (B i)),
        letI := domains
        letI := noeth
        letI := locals
        ∃ (complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i))
          (q' : ∀ i, Ideal (Polynomial (B i))) (qmax : ∀ i, (q' i).IsMaximal)
          (s : ∀ i, Ideal (Polynomial (B i))) (sprime : ∀ i, (s i).IsPrime),
          letI := qmax
          letI := sprime
          (∀ i, IsFractionRing (B i) (s i).ResidueField) ∧
          (∀ i, (q' i).comap (Polynomial.C : B i →+* Polynomial (B i)) =
            IsLocalRing.maximalIdeal (B i)) ∧
          (∀ i, s i ≤ q' i) ∧ (∀ i, s i ≠ ⊥) ∧
          (∀ i, (s i).comap (Polynomial.C : B i →+* Polynomial (B i)) = ⊥) ∧
          Nonempty ((TensorProduct r.ResidueField L (r.Fiber C)) ≃+*
            (∀ i, (s i).Fiber
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (q' i)))
                (Localization.AtPrime (q' i))))) := by
  classical
  let : Algebra A L :=
    ((algebraMap r.ResidueField L).comp
      ((algebraMap (Polynomial A) r.ResidueField).comp Polynomial.C)).toAlgebra
  obtain ⟨B, hfin, s, hs, hsne, hsB, hfrac, e, he⟩ :=
    exists_finite_coefficient_model A r hr hrA L
  have : Module.Finite A B := hfin
  have : s.IsPrime := hs
  obtain ⟨hnoeth, hlocal, hcomplete, _⟩ :=
    (Algebra.finite_over_complete_local_product A B).2.2.2
      (inferInstance : IsDomain B)
  have : IsNoetherianRing B := hnoeth
  have : IsLocalRing B := hlocal
  have : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hcomplete
  obtain ⟨n, q', qmax, hqB, hsq, hiso⟩ :=
    completed_fibre_compatible_product A B q hq r L s e he
  have : ∀ i, (q' i).IsMaximal := qmax
  refine ⟨n, fun _ ↦ B, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ hnoeth, fun _ ↦ hlocal, fun _ ↦ hcomplete,
    q', qmax, fun _ ↦ s, fun _ ↦ hs, ?_⟩
  exact ⟨fun _ ↦ hfrac, hqB, hsq, fun _ ↦ hsne, fun _ ↦ hsB, hiso⟩

end Polynomial
