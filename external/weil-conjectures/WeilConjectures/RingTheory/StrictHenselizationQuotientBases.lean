/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.FlatAlgebraPowerBasis

/-!
# Fixed bases for strict henselization quotients

Source: Stacks Project, More on Algebra, Tag 07QM(4) and the proof of Tag 06LJ(c)
(blueprint: lem-sc-strict-henselization-quotient-bases).
-/

@[expose] public section

universe u

namespace Algebra

/-- Fixed residue-field lifts are bases of every positive-power quotient.
Source: Stacks Project, Tag 07QM(4), using Tag 051F and flat base change Tag 00HI.
(blueprint: lem-sc-strict-henselization-quotient-bases).

Proof: Use the existing triples-presentation theorem to present C as a ring colimit
with its original structural A-map. Faithful flatness of this colimit makes C flat
as an A-module. The quotient C/nC is a vector space over the field A/n; choose any
basis and lift its vectors through the surjective quotient map C -> C/nC. There is
no need to identify this vector space with K. For each positive r, the generic
flat-algebra power-basis lemma applies the nilpotent local basis criterion over
A/n^r to these same lifts. Invert each basis representation and restrict scalars
to A. Ideal.map_pow identifies n^r C with (nC)^r, so the quotient equivalence sends
each standard generator to the class of its fixed lift. No completion comparison
is asserted here.
-/
theorem strictHenselization_quotient_bases
    (A K C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C) :
    ∃ (X : Type u) (x : X → C)
      (e : ∀ (r : ℕ), 1 ≤ r →
        (X →₀ A ⧸ (IsLocalRing.maximalIdeal A) ^ r) ≃ₗ[A]
          C ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r),
      (∀ (r : ℕ) (hr : 1 ≤ r) (i : X),
        e r hr (Finsupp.single i 1) =
          Ideal.Quotient.mk (((IsLocalRing.maximalIdeal A).map (algebraMap A C)) ^ r)
            (x i)) := by
  classical
  obtain ⟨p, hp, a, hsep, ι, ⟨hc⟩, hι⟩ := hC.triples_presentation A K C
  let := a
  have := hsep
  have hflat := AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
    (CommRingCat.of A) p hp K _ hc (CommRingCat.ofHom (algebraMap A C)) hι
  have : Module.Flat A C := RingHom.flat_algebraMap_iff.mp hflat.flat
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  let b := Module.Free.chooseBasis (A ⧸ IsLocalRing.maximalIdeal A)
    (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C))
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (b i)
  have hb := fun r hr ↦ flatAlgebra_power_basis A C b x hx r hr
  choose B hB using hb
  let e := fun r hr ↦ ((B r hr).repr.symm.restrictScalars A).trans
    (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (algebraMap A C) (IsLocalRing.maximalIdeal A) r)).toLinearEquiv
  refine ⟨_, x, e, ?_⟩
  intro r hr i
  change Ideal.quotientEquivAlgOfEq A
    (Ideal.map_pow (algebraMap A C) (IsLocalRing.maximalIdeal A) r)
    ((B r hr).repr.symm (Finsupp.single i 1)) = _
  rw [Module.Basis.repr_symm_single_one, hB r hr i]
  rfl

end Algebra
