/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.PowMap
public import WeilConjectures.TraceFormula.Specialization.ThickOriginCentre

/-!
# The power map of deformation spaces over a field

For a `k`-scheme `X` and ideal sheaves `I, J` on `X` with `J ⊆ I^m`, the power map
`D_I X ⟶ D_J X` of deformation spaces (`Scheme.IdealSheafData.deformationSpacePowMap`) covers the
power map `t ↦ t^m` of the affine line `𝔸¹_k` (`AlgebraicGeometry.affineLinePowMap`).

We apply this to the thick origins `V(x) ⊆ V(x^m)` of the affine line `𝔸¹_k = Spec k[x]`
(`AlgebraicGeometry.polyAffineThickOrigin`): the ideal of `V(x^m)` is the `m`-th power of that of
`V(x)`, and both are finitely generated.

## Main statements

- `ProEtale.CondensedRing.deformationSpacePowMap_deformationSpaceToAffineLine`
- `AlgebraicGeometry.siteIdeal_polyAffineThickOrigin`: `(x^m) = (x)^m` on affine opens.
- `AlgebraicGeometry.isFinite_deformationSpacePowMap_polyAffineThickOrigin`: the power map
  `D_{V(x)} 𝔸¹_k ⟶ D_{V(x^m)} 𝔸¹_k` is finite for `m > 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (k : Type u) [Field k]

/-- The power map `t ↦ t^m` of the affine line `𝔸¹_k`. -/
noncomputable abbrev affineLinePowMap (m : ℕ) :
    𝔸(ULift.{u} (Fin 1); Spec (.of k)) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
  AffineSpace.linePowMap (Spec (.of k)) m

/-- The ideal of the thick origin `V(x^m)` is the `m`-th power of the ideal of the origin `V(x)`,
on every affine open. -/
lemma siteIdeal_polyAffineThickOrigin (m : ℕ) (U : (polyAffine k 1).left.AffineZariskiSite) :
    (polyAffineThickOrigin k m).siteIdeal U = (polyAffineThickOrigin k 1).siteIdeal U ^ m := by
  rw [polyAffineThickOrigin, polyAffineThickOrigin, pow_one,
    IdealSheafData.siteIdeal_ofIdealTop_span_pow]

lemma fg_siteIdeal_polyAffineThickOrigin (m : ℕ) (U : (polyAffine k 1).left.AffineZariskiSite) :
    ((polyAffineThickOrigin k m).siteIdeal U).FG :=
  IdealSheafData.fg_siteIdeal_ofIdealTop (Submodule.fg_span_singleton _) U

/-- The power map `D_{V(x)} 𝔸¹_k ⟶ D_{V(x^m)} 𝔸¹_k` of the deformation spaces of the thick
origins is finite for `m > 0`. -/
lemma isFinite_deformationSpacePowMap_polyAffineThickOrigin {m : ℕ} (hm : 0 < m) :
    IsFinite (IdealSheafData.deformationSpacePowMap m
      fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).le) :=
  IdealSheafData.isFinite_deformationSpacePowMap _ hm
    (fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).ge) (fg_siteIdeal_polyAffineThickOrigin k 1)

namespace ProEtale.CondensedRing

variable {k} {X : Over (Spec (.of k))} {I J : X.left.IdealSheafData} {m : ℕ}
  (hJ : ∀ U : X.left.AffineZariskiSite, J.siteIdeal U ≤ I.siteIdeal U ^ m)

/-- The power map `D_I X ⟶ D_J X` covers the power map `t ↦ t^m` of the affine line `𝔸¹_k`. -/
@[reassoc]
lemma deformationSpacePowMap_deformationSpaceToAffineLine :
    IdealSheafData.deformationSpacePowMap m hJ ≫ deformationSpaceToAffineLine X J =
      deformationSpaceToAffineLine X I ≫ affineLinePowMap k m := by
  rw [deformationSpaceToAffineLine, deformationSpaceToAffineLine,
    IdealSheafData.deformationSpacePowMap_toAffineSpace_assoc, Category.assoc,
    ← AffineSpace.map_linePowMap]
  simp only [Category.assoc]

end ProEtale.CondensedRing

end AlgebraicGeometry
