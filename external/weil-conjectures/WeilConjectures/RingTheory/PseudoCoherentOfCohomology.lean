/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.PseudoCoherentIffAllM

/-!
# Pseudo-coherence from pseudo-coherent cohomology

Source: Stacks Project, More on Algebra, Tag 066B, lemma-cohomology-pseudo-coherent,
pseudo-coherent clause
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private theorem pseudoCoherent_of_iso
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L)
    (h : IsPseudoCoherent K) : IsPseudoCoherent L := by
  obtain ⟨E, b, hb, hfree, ⟨f⟩⟩ := h
  exact ⟨E, b, hb, hfree, ⟨f ≪≫ e⟩⟩

private theorem mPseudoCoherent_of_iso
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (m : ℤ) {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L)
    (h : IsMPseudoCoherent m K) : IsMPseudoCoherent m L := by
  obtain ⟨E, a, b, ha, hb, hfree, f, hf, hepi⟩ := h
  refine ⟨E, a, b, ha, hb, hfree, f ≫ e.hom, ?_, ?_⟩
  · intro i hi
    have := hf i hi
    rw [Functor.map_comp]
    infer_instance
  · have := hepi
    rw [Functor.map_comp]
    infer_instance

private theorem pseudoCoherent_shift
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (n : ℤ) {K : DerivedCategory (ModuleCat.{v} R)}
    (h : IsPseudoCoherent K) : IsPseudoCoherent (K⟦n⟧) := by
  obtain ⟨E, b, hb, hfree, ⟨e⟩⟩ := h
  have := hb
  refine ⟨E⟦n⟧, b - n,
    CochainComplex.isStrictlyLE_shift E b n (b - n) (by omega), ?_,
    ⟨(Q.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso e⟩⟩
  intro i
  have := (hfree (n + i)).1
  have := (hfree (n + i)).2
  let e := (E.shiftFunctorObjXIso n i (n + i) (by omega)).symm.toLinearEquiv
  exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- A cohomologically bounded-above object whose cohomology modules, placed in degree zero,
are pseudo-coherent is pseudo-coherent.

Source: Stacks Project, More on Algebra, Tag 066B, lemma-cohomology-pseudo-coherent,
pseudo-coherent clause
(auxiliary; not a blueprint node).

Proof: choose a representative complex C and put T_q = τ≤q C. Its cohomology equals that
of K through q and vanishes above q; hence Q(T_q) ≅ K for q ≥ b. Fix an integer m.
Shift a bounded-above finite-free representative of H^q(K)[0] by -q. Its terms
remain finite free, so H^q(K)[-q] is pseudo-coherent, hence m-pseudo-coherent by
lem-pc-ring-pseudo-coherent-iff-all-m. Put B = max(b,m-1). At q = m-1, T_q has zero
cohomology in every degree ≥ m, so lem-pc-ring-m-pseudo-coherent-vanishing-base applies.
Induct for q = m,...,B using theorem-pbc-injective-acyclicity: its outer vertices are
T_(q-1) and H^q(K)[-q]. The second clause of
lem-pc-ring-pseudo-coherent-distinguished-triangle gives m-pseudo-coherence of T_q.
At B ≥ b, transport the finite-free approximation across Q(T_B) ≅ K; cohomology
functors preserve its isomorphisms and the degree-m surjection, as required by
def-pc-ring-m-pseudo-coherent. Since m was arbitrary, apply the converse of
lem-pc-ring-pseudo-coherent-iff-all-m to C to obtain a bounded-above finite-free model.
This finite induction also covers b < m, zero cohomology, and arbitrary lower tails. -/
theorem isPseudoCoherent_of_homology
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj K))
    (hcoh : ∀ i : ℤ, IsPseudoCoherent
      (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj
        ((homologyFunctor (ModuleCat.{v} R) i).obj K)))) :
    IsPseudoCoherent K := by
  classical
  let C : CochainComplex (ModuleCat.{v} R) ℤ := Q.objPreimage K
  let e : Q.obj C ≅ K := Q.objObjPreimageIso K
  have hsingle (q : ℤ) : IsPseudoCoherent
      (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) q).obj (C.homology q))) := by
    let eh : (homologyFunctor (ModuleCat.{v} R) q).obj K ≅ C.homology q :=
      (homologyFunctor (ModuleCat.{v} R) q).mapIso e.symm ≪≫
        (homologyFunctorFactors (ModuleCat.{v} R) q).app C
    have hzero := pseudoCoherent_of_iso
      (Q.mapIso ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).mapIso eh)) (hcoh q)
    exact pseudoCoherent_of_iso
      (((singleFunctors (ModuleCat.{v} R)).shiftIso (-q) q 0 (by omega)).app _)
      (pseudoCoherent_shift (-q) hzero)
  obtain ⟨b, hb⟩ := hbounded
  have hC : C.IsLE b := by
    rw [← isLE_Q_obj_iff, isLE_iff]
    intro i hi
    exact (hb i hi).of_iso ((homologyFunctor (ModuleCat.{v} R) i).mapIso e)
  apply pseudoCoherent_of_iso e
  apply (isPseudoCoherent_iff_forall_isMPseudoCoherent R C).mpr
  intro m
  have htrunc : ∀ q : ℤ, m - 1 ≤ q → IsMPseudoCoherent m (Q.obj (C.truncLE q)) := by
    intro q hq
    induction q, hq using Int.leInduction with
    | base =>
      apply isMPseudoCoherent_of_homology_vanishes
      intro i hi
      exact (Q.obj (C.truncLE (m - 1))).isZero_of_isLE (m - 1) i (by omega)
    | succ q hq ih =>
      obtain ⟨i, j, _, _, k, hk, _⟩ := (truncation_triangle (ModuleCat.{v} R) (q + 1)).1 C
      have hleft : IsMPseudoCoherent m (Q.obj (C.truncLE (q + 1 - 1))) := by
        simpa using ih
      exact (isMPseudoCoherent_of_distinguished_triangle R m
        (Pretriangulated.Triangle.mk (Q.map i) (Q.map j) k) hk).2.1 hleft
        ((isPseudoCoherent_iff_forall_isMPseudoCoherent R _).mp (hsingle (q + 1)) m)
  let B : ℤ := max b (m - 1)
  have hCB : C.IsLE B := CochainComplex.isLE_of_le C b B (le_max_left _ _)
  have : QuasiIso (C.ιTruncLE B) := (CochainComplex.quasiIso_ιTruncLE_iff C B).mpr hCB
  exact mPseudoCoherent_of_iso m (asIso (Q.map (C.ιTruncLE B)))
    (htrunc B (le_max_right _ _))

end DerivedCategory
