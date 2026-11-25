/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.RingTheory.KoszulConormalVectorBasisData

/-!
# Conormal basis of a Koszul-regular sequence

Source: Stacks Project, More on Algebra, Tag 062I, lemma-H1-regular-quasi-regular,
first paragraph of the proof (blueprint: lem-sc-koszul-conormal-basis).
-/

@[expose] public section

universe u

namespace ExteriorAlgebra

/-- The generating conormal classes of a Koszul-regular sequence form a basis.
Source: Stacks Project, More on Algebra, Tags 0CEM and 062I,
lemma-koszul-regular-H1-regular and lemma-H1-regular-quasi-regular, first paragraph.
(blueprint: lem-sc-koszul-conormal-basis).

Proof: Koszul-regularity gives zero first homology. Write E = A^r and B = A/I.
The map E to I sends the standard basis to the generators. It is surjective since
these generate I. Its kernel is the image of the second Koszul differential,
because H_1 vanishes. Thus the sequence exterior^2 E -> E -> I -> 0 is exact.
Tensor with B. Right exactness identifies I/I^2 with the cokernel of the map
B tensor exterior^2 E -> B tensor E. The former map is zero: every coefficient
of the second Koszul differential is one of the generators, hence belongs to I.
Consequently B^r -> I/I^2 is an isomorphism sending its standard basis to the
classes of the generators. Transport that basis across this isomorphism.
For r = 0 both modules are zero; for I = A the quotient ring and modules are zero,
and the same construction still gives a basis indexed by Fin r. -/
theorem exists_koszul_conormal_basis
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ b : Module.Basis (Fin r) (A ⧸ I) I.Cotangent,
      ∀ i, b i = koszulConormalVector A I r f hf (Finsupp.single i 1) := by
  obtain ⟨hli, hsp⟩ := koszulConormalVector_linearIndependent_and_span A I r f hreg hf
  let b := Module.Basis.mk hli hsp
  refine ⟨b, ?_⟩
  intro i
  exact Module.Basis.mk_apply hli hsp i

end ExteriorAlgebra
