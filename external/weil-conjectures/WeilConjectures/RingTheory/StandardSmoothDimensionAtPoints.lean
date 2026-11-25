/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Dimension at points of a standard smooth algebra over a field

Source: Stacks Project, Algebra, Tags 00T7 (7), 00SC and 00OT
(blueprint: lem-weil-pbc-standard-smooth-over-field-dimension-at-points).
-/

@[expose] public section

universe u v

namespace Algebra.SubmersivePresentation

/-- Pulling back open neighbourhoods along a homeomorphism gives the local-dimension bound.
This uses the definition of dimension at a point and invariance of Krull dimension. -/
private theorem dimAt_homeomorph_le {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)

/-- A standard smooth presentation over a field with `n` variables and `c` relations has
scheme dimension `n - c` at every prime. The map condition selects the first `c` variables
for the invertible Jacobian minor, as in Stacks, Tag 00T6.

Source: Stacks Project, Algebra, Tag 00T7 (7), last paragraph of the proof; Tags 00SC and 00OT
(blueprint: lem-weil-pbc-standard-smooth-over-field-dimension-at-points).

Proof:
1. Let `S = k[x_1, ..., x_n]/(f_1, ..., f_c)`. The presentation isomorphism gives a
homeomorphism `Spec B ≃ Spec S`, preserving dimension at a point, since it preserves open
neighbourhoods and chains of irreducible closed subsets (`def-weil-affine-spectrum`,
`def-kun-dimension`, `def-kun-topological-dimension-at-point`). Reduce to the corresponding
prime of `S` (`def-weil-pbc-standard-smooth-algebra`).
2. The algebra `S` is smooth (`lem-weil-pbc-standard-smooth-is-smooth`,
`def-weil-pbc-smooth-ring-map`), and its conormal module `I/I²` is free on the `c` relations
(`lem-weil-pbc-standard-smooth-conormal-basis`).
3. Smoothness over a field makes `S` a local complete intersection. Choose a principal
neighbourhood of the prime which is a global complete intersection
(`lem-weil-pbc-smooth-over-field-local-complete-intersection`,
`def-weil-pbc-complete-intersection-over-field`).
4. If `d` is dimension at the prime, the localized conormal module is free of rank `n - d`,
with `0 ≤ d ≤ n` (`lem-weil-pbc-lci-conormal-free-rank-codimension`,
`def-weil-pbc-module-localization`).
5. Localization also makes the conormal module free of rank `c`. Tensor the two free-module
presentations with the residue field of the nonzero local ring at the prime. Equality of
vector-space dimensions gives `c = n - d`, hence `d = n - c`
(`def-weil-pbc-module-localization`, `def-weil-pbc-localization-at-prime`). Transfer back to B.
-/
theorem topologicalKrullDimAt_spec_eq {k : Type u} [Field k]
    {B : Type v} [CommRing B] [Algebra k B] {n c : ℕ} (hnc : c ≤ n)
    (P : Algebra.SubmersivePresentation k B (Fin n) (Fin c))
    (hmap : P.map = Fin.castLE hnc) (Q : PrimeSpectrum B) :
    topologicalKrullDimAt (X := AlgebraicGeometry.Spec (CommRingCat.of B)) Q =
      (n - c : ℕ) := by
  have _ := hmap
  have hdim : P.dimension = n - c := by
    simp [Algebra.Presentation.dimension]
  have : Algebra.IsStandardSmoothOfRelativeDimension (n - c) k B :=
    P.isStandardSmoothOfRelativeDimension hdim
  let f : ULift.{v} k →+* ULift.{u} B :=
    ULift.ringEquiv.symm.toRingHom.comp ((algebraMap k B).comp ULift.ringEquiv.toRingHom)
  have hf : f.IsStandardSmoothOfRelativeDimension (n - c) := by
    have hbase := (RingHom.isStandardSmoothOfRelativeDimension_algebraMap
      (n := n - c) (R := k) (S := B)).mpr inferInstance
    have hright := hbase.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (ULift.ringEquiv : ULift.{v} k ≃+* k))
    have hleft := (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (ULift.ringEquiv : ULift.{u} B ≃+* B).symm).comp hright
    simpa only [f, zero_add, add_zero, RingEquiv.toRingHom_eq_coe] using hleft
  have : AlgebraicGeometry.SmoothOfRelativeDimension (n - c)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) := by
    rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.SmoothOfRelativeDimension (n - c))]
    exact RingHom.locally_of
      (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n - c)) f hf
  let e := PrimeSpectrum.homeomorphOfRingEquiv (ULift.ringEquiv : ULift.{u} B ≃+* B)
  have hd := AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension
    (K := ULift.{v} k) (X := AlgebraicGeometry.Spec (.of (ULift.{u} B)))
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) (n - c) (e.symm Q)
  apply le_antisymm
  · exact (dimAt_homeomorph_le e.symm Q).trans hd.le
  · simpa using hd.ge.trans (dimAt_homeomorph_le e (e.symm Q))

end Algebra.SubmersivePresentation
