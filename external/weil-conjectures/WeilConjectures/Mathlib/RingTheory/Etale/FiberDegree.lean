/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The fibre degree of an algebra at a prime

For an `R`-algebra `S` and a prime `p` of `R`, the fibre degree `p.fiberDegree S` is the
dimension of the fibre `κ(p) ⊗[R] S` over the residue field `κ(p)`. For an étale algebra this
is the number of geometric points of `Spec S` over `p`.

## Main results

- `Ideal.fiberDegree_self`: the fibre degree of `R` over itself is `1`.
- `Ideal.fiberDegree_prod`: fibre degrees are additive in products.
- `Ideal.fiberDegree_tensorProduct`: fibre degrees are invariant under base change.
- `Ideal.subsingleton_of_forall_fiberDegree_eq_zero`: an étale algebra whose fibres all vanish
  is the zero ring.
- `StandardEtalePresentation.fiberDegree_le`,
  `Algebra.IsStandardEtale.exists_forall_fiberDegree_le`: the fibre degrees of a standard
  étale algebra are bounded by the degree of its defining polynomial.
-/

@[expose] public section

open TensorProduct

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
variable (S : Type*) [CommRing S] [Algebra R S]

/-- The fibre degree of an `R`-algebra `S` at a prime `p` of `R`: the dimension of the fibre
`κ(p) ⊗[R] S` over `κ(p)`. -/
noncomputable def fiberDegree : ℕ :=
  Module.finrank p.ResidueField (p.Fiber S)

/-- The fibre of an étale algebra is finite over the residue field. -/
instance Fiber.finite_of_etale [Algebra.Etale R S] : Module.Finite p.ResidueField (p.Fiber S) :=
  Algebra.FormallyUnramified.finite_of_free p.ResidueField (p.Fiber S)

/-- The fibre of a finite algebra is finite over the residue field. -/
instance Fiber.finite_of_finite [Module.Finite R S] : Module.Finite p.ResidueField (p.Fiber S) :=
  inferInstanceAs <| Module.Finite p.ResidueField (p.ResidueField ⊗[R] S)

variable {S}

/-- Fibre degrees are invariant under isomorphisms of algebras. -/
lemma fiberDegree_congr {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    p.fiberDegree S = p.fiberDegree T :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := p.ResidueField) (A₁ := p.ResidueField))
    e).toLinearEquiv.finrank_eq


/-- The fibre degree of `R` over itself is `1`. -/
@[simp]
lemma fiberDegree_self : p.fiberDegree R = 1 := by
  rw [fiberDegree,
    (Algebra.TensorProduct.rid R p.ResidueField p.ResidueField).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- Fibre degrees are additive in products. -/
lemma fiberDegree_prod {T : Type*} [CommRing T] [Algebra R T]
    [Module.Finite p.ResidueField (p.Fiber S)] [Module.Finite p.ResidueField (p.Fiber T)] :
    p.fiberDegree (S × T) = p.fiberDegree S + p.fiberDegree T := by
  rw [fiberDegree,
    (Algebra.TensorProduct.prodRight R p.ResidueField p.ResidueField S T).toLinearEquiv.finrank_eq,
    Module.finrank_prod]
  rfl


section BaseChange

variable {R' : Type*} [CommRing R'] [Algebra R R'] (q : Ideal R') [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]

/-- Fibre degrees are invariant under base change: the fibre degree of `R' ⊗[R] S` at a prime
`q` of `R'` lying over `p` is the fibre degree of `S` at `p`. -/
lemma fiberDegree_tensorProduct (S : Type*) [CommRing S] [Algebra R S] :
    q.fiberDegree (R' ⊗[R] S) = p.fiberDegree S := by
  let e₁ : q.Fiber (R' ⊗[R] S) ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] S :=
    AlgebraTensorModule.cancelBaseChange R R' q.ResidueField q.ResidueField S
  let e₂ : q.ResidueField ⊗[p.ResidueField] p.Fiber S ≃ₗ[q.ResidueField] q.ResidueField ⊗[R] S :=
    AlgebraTensorModule.cancelBaseChange R p.ResidueField q.ResidueField q.ResidueField S
  rw [fiberDegree, fiberDegree, e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]


end BaseChange

/-- An étale algebra all of whose fibre degrees vanish is the zero ring. -/
lemma subsingleton_of_forall_fiberDegree_eq_zero (S : Type*) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (h : ∀ (p : Ideal R) [p.IsPrime], p.fiberDegree S = 0) :
    Subsingleton S := by
  by_contra hS
  rw [not_subsingleton_iff_nontrivial] at hS
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) ⟨q, hq.isPrime⟩
  let Q : PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageEquivFiber R S p ⟨⟨q, hq.isPrime⟩, rfl⟩
  have := h p.asIdeal
  rw [fiberDegree, Module.finrank_zero_iff] at this
  exact Q.isPrime.ne_top (Subsingleton.elim _ _)


end Ideal

section StandardEtale

open Polynomial

/-- A standard étale algebra over a field has dimension at most the degree of its defining
polynomial. -/
lemma StandardEtalePair.finrank_ring_le {K : Type*} [Field K] (P : StandardEtalePair K) :
    Module.finrank K P.Ring ≤ P.f.natDegree := by
  rw [P.equivAwayAdjoinRoot.toLinearEquiv.finrank_eq]
  have hfin : Module.Finite K (AdjoinRoot P.f) := (AdjoinRoot.powerBasis' P.monic_f).finite
  have : IsArtinianRing (AdjoinRoot P.f) := isArtinian_of_tower K inferInstance
  have hsurj := IsArtinianRing.localization_surjective (Submonoid.powers (AdjoinRoot.mk P.f P.g))
    (Localization.Away (AdjoinRoot.mk P.f P.g))
  let φ : AdjoinRoot P.f →ₗ[K] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsScalarTower.toAlgHom K (AdjoinRoot P.f) _).toLinearMap
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  calc Module.finrank K (Localization.Away (AdjoinRoot.mk P.f P.g))
      = Module.finrank K (LinearMap.range φ) := by rw [hrange, finrank_top]
    _ ≤ Module.finrank K (AdjoinRoot P.f) := φ.finrank_range_le
    _ = P.f.natDegree := by
      rw [(AdjoinRoot.powerBasis' P.monic_f).finrank, AdjoinRoot.powerBasis'_dim]

/-- The fibre degrees of a standard étale algebra are bounded by the degree of the monic
polynomial of the presentation. -/
lemma StandardEtalePresentation.fiberDegree_le {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : StandardEtalePresentation R S) (p : Ideal R) [p.IsPrime] :
    p.fiberDegree S ≤ P.f.natDegree := by
  let Q : StandardEtalePresentation p.ResidueField (p.Fiber S) := P.baseChange
  have h₁ : p.fiberDegree S = Module.finrank p.ResidueField Q.Ring :=
    Q.equivRing.toLinearEquiv.finrank_eq
  have h₂ : Q.f.natDegree = P.f.natDegree := by
    change (P.f.map (algebraMap R p.ResidueField)).natDegree = _
    exact P.monic_f.natDegree_map _
  rw [h₁, ← h₂]
  exact Q.P.finrank_ring_le

/-- The fibre degrees of a standard étale algebra are uniformly bounded. -/
lemma Algebra.IsStandardEtale.exists_forall_fiberDegree_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsStandardEtale R S] :
    ∃ n : ℕ, ∀ (p : Ideal R) [p.IsPrime], p.fiberDegree S ≤ n :=
  let P : StandardEtalePresentation R S := Nonempty.some inferInstance
  ⟨P.f.natDegree, fun p _ ↦ P.fiberDegree_le p⟩

end StandardEtale
