/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.FlatFiberLocalDepth
import WeilConjectures.RingTheory.FlatFiberPrimeHeight

/-!
# Ascent of Serre's condition (S_k) along flat maps

Source: Stacks Project, Algebra, Lemma Tag 0339 (lemma-Sk-goes-up)
(blueprint: lem-weil-pbc-serre-sk-goes-up).

## Main statements

- `RingHom.isSerreS_of_flat`: property (S_k) ascends along a flat map with
  Noetherian source and target and (S_k) fibres.
-/

@[expose] public section

universe u v

namespace RingHom

private theorem min_add_le_add_min (k a b : ℕ∞) :
    min k (a + b) ≤ min k a + min k b := by
  by_cases ha : k ≤ a
  · rw [min_eq_left ha]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right zero_le)
  · by_cases hb : k ≤ b
    · rw [min_eq_left hb]
      exact (min_le_left _ _).trans (le_add_of_nonneg_left zero_le)
    · rw [min_eq_right (le_of_not_ge ha), min_eq_right (le_of_not_ge hb)]
      exact min_le_right _ _

/-- Property `(S_k)` ascends along a flat map with `(S_k)` fibres.
Source: Stacks Project, Algebra, Lemma Tag 0339 (lemma-Sk-goes-up),
(blueprint: lem-weil-pbc-serre-sk-goes-up).

Proof:
1. Fix a prime `q` of `S` and set `p = φ⁻¹(q)`, where `φ = algebraMap R S`.
   The induced map `Rₚ → S_q` is flat and local, with Noetherian source and target
   (`lem-weil-pbc-flat-local-ring-maps`). By the Serre definition we must prove
   `depth(S_q) ≥ min(k, dim(S_q))` (`def-weil-pbc-serre-conditions-rk-sk`).
2. The maximal ideal of `Rₚ` is `p Rₚ`; its extension to `S_q` is `p S_q`, since
   denominators outside `p` map to units. Thus the closed fibre is `S_q / p S_q`
   (`def-weil-pbc-localization-at-prime`).
3. The flat local depth formula gives
   `depth(S_q) = depth(Rₚ) + depth(S_q / p S_q)`
   (`lem-weil-pbc-flat-local-depth-formula`, Stacks Tag 0337).
4. The dimension formula gives `dim(S_q) ≤ dim(Rₚ) + dim(S_q / p S_q)`
   (`lem-weil-pbc-flat-height-formula`, Tags 00OM and 00ON).
5. The fibre `C = p.Fiber S` is Noetherian (`lem-weil-pbc-fibre-ring-noetherian`).
   The prime of `C` corresponding to `q` (`lem-weil-pbc-fibre-ring-primes-bijection`)
   has localization isomorphic to `S_q / p S_q`
   (`lem-weil-pbc-fibre-ring-local-ring-iso`). The fibre hypothesis and invariance
   of depth and dimension under ring isomorphism yield
   `depth(S_q / p S_q) ≥ min(k, dim(S_q / p S_q))`
   (`def-weil-pbc-serre-conditions-rk-sk`, `def-weil-pbc-depth`).
6. The base hypothesis yields `depth(Rₚ) ≥ min(k, dim(Rₚ))`
   (`def-weil-pbc-serre-conditions-rk-sk`).
7. For `a = dim(Rₚ)` and `b = dim(S_q / p S_q)`, we have
   `min(k, a) + min(k, b) ≥ min(k, a + b)`: if either summand's dimension is at
   least `k`, the left side is at least `k`; otherwise it equals `a + b`.
   Combining steps 3--6 proves the required bound at every `q`, hence `(S_k)`.

The arbitrary ring map is encoded by `[Algebra R S]` and `algebraMap R S`.
Every ring homomorphism gives such an algebra structure via `RingHom.toAlgebra`.
The existential Noetherian witness makes the fibre predicate well-typed and
asserts its existence, rather than making the predicate conditional on it.
-/
theorem isSerreS_of_flat {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] (k : ℕ) (hflat : (algebraMap R S).Flat)
    (hfibres : ∀ (p : Ideal R) [p.IsPrime],
      ∃ (_ : IsNoetherianRing (p.Fiber S)), Ring.IsSerreS (p.Fiber S) k)
    (hR : Ring.IsSerreS R k) :
    Ring.IsSerreS S k := by
  intro q hq
  let p : Ideal R := q.comap (algebraMap R S)
  have hp : p.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  obtain ⟨hnoeth, hfibre⟩ := hfibres p
  let e := PrimeSpectrum.preimageEquivFiber R S (⟨p, hp⟩ : PrimeSpectrum R)
  let Q := e ⟨⟨q, hq⟩, rfl⟩
  have hQ : Q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
    exact congrArg (fun t ↦ t.val.asIdeal) (e.left_inv ⟨⟨q, hq⟩, rfl⟩)
  have hd := depth_eq_add_of_flat_fiber hflat p Q.asIdeal
  have hh := height_eq_add_of_flat_fiber hflat p Q.asIdeal
  have hspec : Q.comap Algebra.TensorProduct.includeRight.toRingHom = ⟨q, hq⟩ := by
    exact congrArg Subtype.val (e.left_inv ⟨⟨q, hq⟩, rfl⟩)
  have hdepth := congrArg (fun t : PrimeSpectrum S ↦
    IsLocalRing.depth (R := Localization.AtPrime t.asIdeal)
      (Localization.AtPrime t.asIdeal)) hspec
  have hd' := hdepth.symm.trans hd
  rw [hQ] at hh
  rw [hh, hd']
  exact (min_add_le_add_min (k : ℕ∞) p.height Q.asIdeal.height).trans
    (add_le_add (hR p) (hfibre Q.asIdeal))

end RingHom
