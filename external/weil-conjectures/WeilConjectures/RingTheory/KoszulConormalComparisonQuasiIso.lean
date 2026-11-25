/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.RingTheory.KoszulDualBelowTopHomology
import WeilConjectures.RingTheory.KoszulConormalTopHomology
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Quasi-isomorphism of a normalized dual Koszul comparison

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, local Koszul computation.
(blueprint: new-s3-koszul-conormal-comparison-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

private theorem koszulDual_isZero_homology_above_top
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (n : ℕ) (hn : r < n) :
    CategoryTheory.Limits.IsZero ((koszulDualComplex A r f).homology n) := by
  classical
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n
  have : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s ↦ by
    have hcard : s.val.card ≤ r := by simpa using Finset.card_le_univ s.val
    exact (Nat.not_le_of_lt hn) (s.property ▸ hcard)⟩
  have : Subsingleton (⋀[A]^n (Fin r →₀ A)) := b.repr.injective.subsingleton
  have : Subsingleton ((koszulComplex A r f).X n ⟶ ModuleCat.of A A) := by
    change Subsingleton (ModuleCat.of A (⋀[A]^n (Fin r →₀ A)) ⟶ ModuleCat.of A A)
    refine ⟨fun x y ↦ ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  have hX : CategoryTheory.Limits.IsZero ((koszulDualComplex A r f).X n) := by
    change CategoryTheory.Limits.IsZero
      (ModuleCat.of A ((koszulComplex A r f).X n ⟶ ModuleCat.of A A))
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology

/-- Every determinant-normalized comparison is a quasi-isomorphism.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, complementary
Koszul pairing and top cohomology calculation; Tag 062I for the conormal basis.
(blueprint: new-s3-koszul-conormal-comparison-quasi-iso).

Proof: Write E = A^r, B = A/I, and D = wedge^r_B Hom_B(I/I^2,B).
In degree n <= r, the complementary-wedge pairing gives an A-linear
isomorphism Hom_A(wedge^n E,A) to wedge^(r-n) E: the functional dual to an
ordered basis wedge maps to its complementary wedge with the permutation sign.
On basis wedges, signed precomposition with the Koszul contraction becomes
the reversed Koszul differential times a degree-dependent sign. Multiply these
isomorphisms recursively by units +1 or -1 to make the differentials commute.
For n > r both exterior terms and their duals are zero. Consequently the dual
complex has zero cohomology outside degree r by Koszul-regularity. In degree r
its term is A times the functional dual to e_top, and the incoming image is
I times this generator: contraction of e_top has coefficients +f_i or -f_i,
and the coordinate functionals on the complementary wedges give all f_i.
Thus its top cohomology is B (also for r = 0, when the incoming image is zero).

The conormal basis from `exists_koszul_conormal_basis` makes D free of rank one,
with generator the ordered wedge of the dual conormal basis. In the
normalization equation take v to be the standard basis of E. Determinant
evaluation then forces phi's top component to send x to
(-1)^(r*(r-1)/2) times (x(e_top) mod I) times this generator. It therefore
induces a B-linear isomorphism B to D on top cohomology, since the sign is a
unit. The target single complex has zero cohomology elsewhere, so all homology
maps are isomorphisms, which is QuasiIso phi. For I = A both top cohomologies
are zero; for r = 0 the normalization forces the identity quotient A to A. -/
theorem koszul_conormal_comparison_is_quasiIso
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ) : QuasiIso φ := by
  obtain ⟨b, hb⟩ := exists_koszul_conormal_basis A I r f hreg hf
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hn : n = r
  · subst n
    exact koszul_conormal_comparison_isIso_top_homology A I r f hf b hb φ hφ
  · have hsource : CategoryTheory.Limits.IsZero ((koszulDualComplex A r f).homology n) := by
      rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
      · exact koszulDual_isZero_homology_below_top A r f hreg n hlt
      · exact koszulDual_isZero_homology_above_top A r f n hgt
    have htarget := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℕ) r (koszulNormalDeterminant A I r) n hn
    exact hsource.isIso htarget (HomologicalComplex.homologyMap φ n)

end ExteriorAlgebra
