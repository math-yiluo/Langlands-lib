/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.RegularLocalFibreFinrankComparison
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

/-- The cotangent dimension formula at a finite type algebra prime with separable residue field.
Source: Stacks Project, Algebra, proof of Lemma Tag 00TV, lines 38754--38778.
(blueprint: lem-weil-pbc-regular-local-fibre-finrank).
Proof:
1. Set R = S_q, m its maximal ideal, and K = kappa(q). Finite type over the field k
   makes S and R Noetherian, and K is finitely generated as a field over k by the
   residue classes of algebra generators of S. The prime hypothesis makes K a field.
2. The quotient conormal sequence for R -> K is right exact. Separability and finite
   field generation give injectivity of m/m^2 -> K tensor_R Omega[R/k] by Tag 00TU.
   Identify the quotient conormal module with the local cotangent space using
   ker(R -> K) = m. Thus this sequence is short exact over K.
3. The cotangent space is finite dimensional since m is finitely generated. The
   separably generated differentials theorem makes Omega[K/k] finite dimensional,
   with dimension t = trdeg_k K. Additivity of dimensions in the short exact sequence
   gives finrank_K(K tensor_R Omega[R/k]) = e + t, where e = dim_K(m/m^2).
4. Localization of differentials identifies Omega[R/k] with R tensor_S Omega[S/k].
   Tensor associativity and cancellation of base change identify its K fibre with
   K tensor_S Omega[S/k], preserving the finite dimension e + t.
5. The dimension-at-point theorem gives finite natural numbers d and t with
   ringKrullDim R = d and topologicalKrullDimAt q = d + t. The regular-local
   cotangent criterion says R is regular if and only if e = d.
6. All dimensions are finite, so equality of their casts in WithBot ENat is equality
   of natural numbers. Cancel t in e + t = d + t to obtain e = d, in both directions.
-/
theorem regularLocal_iff_fibre_finrank_eq_dimension
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    (hsep : Algebra.IsSeparableExtension k q.ResidueField) :
    IsRegularLocalRing (Localization.AtPrime q) ↔
      (Module.finrank q.ResidueField
        (q.ResidueField ⊗[S] KaehlerDifferential k S) : WithBot ℕ∞) =
        topologicalKrullDimAt (⟨q, inferInstance⟩ : PrimeSpectrum S) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  obtain ⟨d, r, hd, hr, hpoint⟩ :=
    AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) q
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hd,
    fibre_finrank_eq_cotangent_finrank_add k S q hsep r hr, hpoint]
  simp only [Nat.cast_inj, Nat.add_right_cancel_iff]

end Algebra
