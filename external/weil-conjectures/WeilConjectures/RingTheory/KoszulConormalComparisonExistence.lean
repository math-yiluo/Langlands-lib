/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalComparisonMap
import WeilConjectures.RingTheory.KoszulConormalComparisonQuasiIso

/-!
# Existence of the determinant-normalized dual Koszul comparison

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local Koszul computation.
(blueprint: lem-sc-koszul-conormal-comparison-existence).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- There is a determinant-normalized quasi-isomorphism from the dual Koszul complex
to the normal determinant in degree `r`.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local Koszul computation.
(blueprint: lem-sc-koszul-conormal-comparison-existence).

Proof: Put E = A^r, B = A/I, and let c_i be the basis of I/I^2 supplied by
lem-sc-koszul-conormal-basis. Write c_i^* for its dual basis, e_top for the ordered
standard top wedge of E, and s = (-1)^(r*(r-1)/2). Define the top component by
x ↦ s * (x(e_top) mod I) times the ordered wedge of the c_i^*, and set every other
component to zero. This is an A-linear map. The preceding dual differential is signed
precomposition with d_r, whose coefficients are the generators f_i. Its top evaluation
therefore lies in I, so the displayed map annihilates this differential and defines a
cochain map. The determinant evaluation formula gives precisely the required
normalization on all wedges: both sides are s times the determinant of the generator
coordinates times x(e_top) mod I.

For the quasi-isomorphism, the perfect complementary-wedge pairing identifies the
degree-n dual term with the degree-(r-n) Koszul term. Computing on standard basis
wedges gives the Koszul differential with degree signs; rescale the degree components
recursively by units +1 or -1 to obtain a complex isomorphism. Terms beyond r vanish.
Koszul-regularity then gives exactness away from r. The image of the differential into
the top dual term is I times its rank-one generator (the generators f_i occur by
contraction of e_top), so the top cokernel is B. The displayed top map is the quotient
map followed by multiplication by the unit s and the basis isomorphism to the normal
determinant. It induces an isomorphism on top cohomology, proving QuasiIso.
For r = 0 this is the identity quotient with I = 0; when I = A all target modules
are zero and the same cokernel and exactness argument applies. -/
theorem exists_koszul_conormal_comparison
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ φ : koszulDualComplex A r f ⟶
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
          (koszulNormalDeterminant A I r),
      IsKoszulConormalComparison A I r f hf φ ∧ QuasiIso φ := by
  obtain ⟨φ, hφ⟩ := exists_koszul_conormal_comparison_map A I r f hreg hf
  exact ⟨φ, hφ, koszul_conormal_comparison_is_quasiIso A I r f hreg hf φ hφ⟩

end ExteriorAlgebra
