/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DeformationSpacePow
public import WeilConjectures.TraceFormula.Specialization.ThickOriginPowModel

/-!

# The power model of the thick origin

For `m ≥ 1`, the thick origin `V(x^m) ⊆ 𝔸¹_k` is the `m`-th power of the origin `V(x)`, so the
power map of deformation spaces `D_{(x)} 𝔸¹ ⟶ D_{(x^m)} 𝔸¹` (`t ↦ t^m`,
`IdealSheafData.deformationSpacePowMap`) and the power map of the trait give a morphism of models
`𝒲 ⟶ 𝒟_{(x^m)}` over the identity of `𝔸¹_k` (`ProEtale.CondensedRing.thickOriginPowModelHom`),
where `𝒲` is the deformation `𝒟_{(x)} ≅ 𝔸¹ × S` of the origin with the thickened special fibre
`t^m = 0`. Its morphism of total spaces is finite and its squares of special fibres and of
identifications are cartesian, so the proper exchange applies to it.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] {m : ℕ} (hm : m ≠ 0)

/-- The coordinate `t` of the trait intertwines the power maps of the trait and of the affine
line. -/
@[reassoc]
lemma traitPowMap_traitToAffineLine :
    traitPowMap k' m hm ≫ traitToAffineLine k k' =
      traitToAffineLine k k' ≫ affineLinePowMap k m := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [Category.assoc, Category.assoc, traitToAffineLine_over, AffineSpace.linePowMap_over,
      traitToAffineLine_over, traitPowMap_traitToBase]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, AffineSpace.linePowMap_appTop_coord, map_pow, traitToAffineLine,
      AffineSpace.homOfVector_appTop_coord, traitPowMap, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso (.of (PowerSeries k'))).inv (PowerSeries.expand m hm PowerSeries.X) = _
    rw [PowerSeries.expand_X, map_pow]

end AlgebraicGeometry
