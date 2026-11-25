/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximum
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.FieldTheory.FinTrdeg

/-!
# Dimension at a point of a finite type algebra over a field

Source: Stacks Project, Algebra, Lemma 00P1
(`lemma-dimension-at-a-point-finite-type-field`)
(blueprint: lem-weil-pbc-dimension-at-point-local-ring-trdeg).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma 00P1
(`lemma-dimension-at-a-point-finite-type-field`).
(blueprint: lem-weil-pbc-dimension-at-point-local-ring-trdeg).
The local topological dimension, local-ring dimension, and residue-field transcendence degree
are finite, and the first is the sum of the other two. Natural-number witnesses express
finiteness without losing the cardinal-valued meaning of `Algebra.trdeg`.

Proof:
1. Set r = trdeg_k κ(p). The spectrum of S/p is V(p), and its fraction field is κ(p).
   By `lem-weil-pbc-finite-type-domain-dimension-trdeg`, its dimension is r and is finite.
   By `lem-weil-pbc-finite-type-domain-dimension-local-ring`, a maximal chain above p
   has length r.
2. By `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-noetherian-finitely-many-minimal-primes`, S has finitely many minimal primes.
   Those q_j below p form a nonempty list by `lem-weil-pbc-prime-contains-minimal-prime`.
   By the prime correspondence for localizations, they correspond to the minimal primes of S_p.
3. Choose maximal chains from each q_j to p, of lengths s(j). By
   `lem-weil-pbc-localization-dimension-chains-below-prime` and the prime correspondence,
   dim S_p = max_j s(j), which is finite.
4. By `lem-weil-pbc-dimension-at-point-components`, dim_p Spec S = max_j dim(S/q_j).
   Concatenate each chain below p with the chain above p. By
   `lem-weil-pbc-finite-type-domain-dimension-local-ring`, dim(S/q_j) = s(j) + r.
   Taking maxima gives dim_p Spec S = dim S_p + r, also finite. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_add_trdeg
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) [p.IsPrime] :
    ∃ d r : ℕ,
      ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞) ∧
      Algebra.trdeg k p.ResidueField = (r : Cardinal.{v}) ∧
      topologicalKrullDimAt (⟨p, inferInstance⟩ : Spec (CommRingCat.of S)) =
        ((d + r : ℕ) : WithBot ℕ∞) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := Localization.AtPrime p))
  have hat : a ≠ ⊤ := by
    intro h
    apply ringKrullDim_ne_top (R := Localization.AtPrime p)
    rw [← ha, h]
    rfl
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hat
  have hdim : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞) :=
    ha.symm.trans (congrArg (fun a : ℕ∞ ↦ (a : WithBot ℕ∞)) hd.symm)
  have : Algebra.EssFiniteType k p.ResidueField := .comp k S p.ResidueField
  obtain ⟨r, htrdeg⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0 k p.ResidueField)
  obtain ⟨hbound, q, hq, hqp, hminimal, hqeq⟩ :=
    minimal_component_dimension_maximum (k := k) p d r hdim htrdeg
  obtain ⟨qs, hqs, _, n, hn, _, _, hquot, hquot', _⟩ :=
    dimension_at_point_components (k := k) p
  obtain ⟨q', hq', hq'eq⟩ := hquot'
  have hle : (n : WithBot ℕ∞) ≤ ((d + r : ℕ) : WithBot ℕ∞) := by
    obtain ⟨hprime, hbelow, hmin⟩ := (hqs q').mp hq'
    rw [← hq'eq]
    exact hbound q' hprime hbelow hmin
  have hge : ((d + r : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← hqeq]
    exact hquot q ((hqs q).mpr ⟨hq, hqp, hminimal⟩)
  exact ⟨d, r, hdim, htrdeg, hn.trans (le_antisymm hle hge)⟩

end AlgebraicGeometry
