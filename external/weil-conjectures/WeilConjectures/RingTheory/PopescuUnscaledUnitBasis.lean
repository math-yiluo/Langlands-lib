/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuAdmissibleSubalgebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Nilpotent.Defs

import WeilConjectures.RingTheory.PopescuUnitResidueExtension
import WeilConjectures.RingTheory.SimpleTranscendentalDifferentialDecomposition
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis

/-!
# Unscaled residue differential basis after adjoining a unit

Source: Stacks Project, Tags 07FH and 07FI; the geometric construction in
steps 1 and 3–10 of lem-weil-pbc-popescu-denominator-basis-enlargement.
-/

@[expose] public section

set_option autoImplicit false
universe u v

namespace Algebra

private theorem exists_basis_of_differential_decomposition
    (k : Type u) (F₀ : Type v) (F : Type v) [Field k] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra k F] [Algebra F₀ F] [IsScalarTower k F₀ F]
    (t m : ℕ) (c : Fin t → F₀) (d : Fin m → F)
    (b₀ : Module.Basis (Fin t) F₀ (KaehlerDifferential k F₀))
    (hb₀ : ∀ j, b₀ j = KaehlerDifferential.D k F₀ (c j))
    (E : ((TensorProduct F₀ F (KaehlerDifferential k F₀)) × (Fin m → F)) ≃ₗ[F]
      KaehlerDifferential k F)
    (hE : ∀ x a, E (x, a) = KaehlerDifferential.mapBaseChange k F₀ F x +
      ∑ j, a j • KaehlerDifferential.D k F (d j)) :
    ∃ b : Module.Basis (Fin t ⊕ Fin m) F (KaehlerDifferential k F),
      (∀ j, b (Sum.inl j) = KaehlerDifferential.D k F (algebraMap F₀ F (c j))) ∧
      (∀ j, b (Sum.inr j) = KaehlerDifferential.D k F (d j)) := by
  classical
  let b := ((b₀.baseChange F).prod (Pi.basisFun F (Fin m))).map E
  refine ⟨b, ?_, ?_⟩
  · intro j
    change E ((b₀.baseChange F).prod (Pi.basisFun F (Fin m)) (Sum.inl j)) = _
    have hpair : (b₀.baseChange F).prod (Pi.basisFun F (Fin m)) (Sum.inl j) =
        (TensorProduct.tmul F₀ (1 : F) (b₀ j), 0) := by
      apply Prod.ext
      · rw [Module.Basis.prod_apply_inl_fst, Module.Basis.baseChange_apply]
      · exact Module.Basis.prod_apply_inl_snd _ _ j
    rw [hpair, hE]
    simp [hb₀, KaehlerDifferential.map_D]
  · intro j
    change E ((b₀.baseChange F).prod (Pi.basisFun F (Fin m)) (Sum.inr j)) = _
    have hpair : (b₀.baseChange F).prod (Pi.basisFun F (Fin m)) (Sum.inr j) =
        (0, Pi.basisFun F (Fin m) j) := by
      apply Prod.ext
      · exact Module.Basis.prod_apply_inr_fst _ _ j
      · exact Module.Basis.prod_apply_inr_snd _ _ j
    rw [hpair, hE]
    simp [Pi.basisFun_apply]

/-- Enlarge an admissible subalgebra by one unit on the residue-field level.
This is the geometric part of the denominator argument, before using any numerator
or clearing denominators. The additional basis vectors, if present, are lifted by `s`.
Source: Stacks Project, Tags 07FH and 07FI, and the geometric construction in
steps 1 and 3–10 of lem-weil-pbc-popescu-denominator-basis-enlargement.
(blueprint: lem-weil-pbc-popescu-unscaled-unit-basis).

Proof: Put L = Λ_q, J = qL, B = L/J^n, x = π(s), K = B/m_B and F₀ = A₀/m₀.
The ring B is Artinian local with m_B = JB and m_B^n = 0. Admissibility makes
A₀ → B local and embeds F₀ in K. The element x is a unit; write α for its nonzero
residue. Write c_j for the residues of a₀ j.

If α is transcendental over F₀, evaluate A₀[T] in B at x and localize at the
inverse image of m_B. That prime is m₀[T]: reduction is the injective evaluation
F₀[T] → K. The localized ring D is Noetherian with nilpotent maximal ideal m₀D
and residue F₀(T), hence Artinian local. Evaluation extends to a local map D → B.
The fibre criterion for A₀ → D → B makes this map flat, since B is flat over A₀
and the closed fibre is a vector space over F₀(T). A flat local map is faithfully
flat and injective. Its image A contains A₀ and x and satisfies m_A B = m_B.
Its residue field is F₀(α), essentially of finite type over k; the Artinian local
residue criterion makes A essentially of finite type over k, so A is admissible.
The polynomial and localization differential formulas give the basis dc_j, dα.
Take m = 1, y₀ = x, Q = 1 and z = x⁻¹, a unit of A: then z x - 1 = 0
is nilpotent. No Frobenius powering or denominator calculation is needed here.

If α is algebraic, choose Q = p^e with β = α^Q separable over F₀. Lift the finite
separable extension F₀(β)/F₀ to a finite étale local A₀-algebra D by the henselian
finite étale equivalence. Both A₀ and B have nilpotent maximal ideals, so
`henselianLocalRing_of_maximalIdeal_le_nilradical` makes them henselian.
Base change D to B; the residue embedding F₀(β) → K determines a prime with residue
K, and henselian étale retraction gives a local map D → B inducing that embedding.
The fibre flatness criterion again makes this map injective and flat. Its image A
is admissible by the same Artinian local residue criterion. Mathlib's canonical
`tensorKaehlerEquivOfFormallyEtale` for the finite separable residue extension transports
the basis dc_j to the residue field of A. Take m = 0 and the empty family y.
Lift β⁻¹ to a unit z of A. Then z x^Q - 1 belongs to m_B and is nilpotent
because m_B^n = 0. Retain Q = p^e ≥ 1 and this unit z. This is only a residue
inverse: obtaining an actual power of x in A is a separate Frobenius argument.

In each case use inclusion A₀ → A for the original lifts. The basis is indexed
by Fin t₀ ⊕ Fin m; the left part consists of their residue differentials and the
right part of the residue differentials of y. Empty initial bases cause no exception.
No choice from these existential conclusions is used to define library data. -/
theorem exists_popescu_unscaled_unit_basis
    (k : Type u) (Λ : Type v) [Field k] [CommRing Λ] [Algebra k Λ]
    [IsNoetherianRing Λ] (p : ℕ) [CharP k p] (hp : 0 < p)
    (q : Ideal Λ) [q.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (A₀ : Subalgebra k (Localization.AtPrime q ⧸
      (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) [IsLocalRing A₀]
    (hA₀ : A₀.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
      (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))))
    (t₀ : ℕ) (a₀ : Fin t₀ → A₀)
    (b₀ : Module.Basis (Fin t₀) (IsLocalRing.ResidueField A₀)
      (KaehlerDifferential k (IsLocalRing.ResidueField A₀)))
    (hb₀ : ∀ j, b₀ j = KaehlerDifferential.D k (IsLocalRing.ResidueField A₀)
      (IsLocalRing.residue A₀ (a₀ j)))
    (s : Λ) (hs : s ∉ q) :
    ∃ (A : Subalgebra k (Localization.AtPrime q ⧸
        (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)) (_ : IsLocalRing A),
      ∃ hle : A₀ ≤ A,
      A.IsPopescuAdmissible ((q.map (algebraMap Λ (Localization.AtPrime q))).map
        (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n))) ∧
      ∃ (Q : ℕ) (_ : 1 ≤ Q) (z : Aˣ),
        IsNilpotent (((z : A) : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) *
          (Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
            (algebraMap Λ (Localization.AtPrime q) s)) ^ Q - 1) ∧
        ∃ (m : ℕ) (y : Fin m → A),
          (∀ j, (y j : Localization.AtPrime q ⧸
            (q.map (algebraMap Λ (Localization.AtPrime q))) ^ n) =
            Ideal.Quotient.mk ((q.map (algebraMap Λ (Localization.AtPrime q))) ^ n)
              (algebraMap Λ (Localization.AtPrime q) s)) ∧
          ∃ b : Module.Basis (Fin t₀ ⊕ Fin m) (IsLocalRing.ResidueField A)
              (KaehlerDifferential k (IsLocalRing.ResidueField A)),
            (∀ j, b (Sum.inl j) = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (Subalgebra.inclusion hle (a₀ j)))) ∧
            (∀ j, b (Sum.inr j) = KaehlerDifferential.D k (IsLocalRing.ResidueField A)
              (IsLocalRing.residue A (y j))) := by
  classical
  obtain ⟨A, hlocal, hle, hA, Q, hQ, z, hz, m, y, hy, alg, htower, hres, hcase⟩ :=
    exists_popescu_unit_residue_extension k Λ p hp q n hn A₀ hA₀ s hs
  let := hlocal
  let := alg
  have := htower
  let F₀ := IsLocalRing.ResidueField A₀
  let F := IsLocalRing.ResidueField A
  let yF : Fin m → F := fun j ↦ IsLocalRing.residue A (y j)
  have hE : ∃ E : ((TensorProduct F₀ F (KaehlerDifferential k F₀)) × (Fin m → F)) ≃ₗ[F]
      KaehlerDifferential k F,
      ∀ x c, E (x, c) = KaehlerDifferential.mapBaseChange k F₀ F x +
        ∑ j, c j • KaehlerDifferential.D k F (yF j) := by
    rcases hcase with ⟨hm, hetale⟩ | ⟨hm, htrans, hgen⟩
    · have := hetale
      have : IsEmpty (Fin m) := hm ▸ inferInstance
      let E := (LinearEquiv.prodUnique (R := F)
        (M := TensorProduct F₀ F (KaehlerDifferential k F₀)) (M₂ := Fin m → F)).trans
          (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k F₀ F)
      exact ⟨E, by intro x c; simp [E]⟩
    · exact KaehlerDifferential.exists_simple_transcendental_differential_decomposition
        k F₀ F m yF hm htrans hgen
  obtain ⟨E, hE⟩ := hE
  obtain ⟨b, hbL, hbR⟩ := exists_basis_of_differential_decomposition
    k F₀ F t₀ m (fun j ↦ IsLocalRing.residue A₀ (a₀ j)) yF b₀ hb₀ E hE
  refine ⟨A, hlocal, hle, hA, Q, hQ, z, hz, m, y, hy, b, ?_, hbR⟩
  intro j
  exact (hbL j).trans (congrArg (KaehlerDifferential.D k F) (hres (a₀ j)))

end Algebra
