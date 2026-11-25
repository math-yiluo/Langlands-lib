/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateBoundaryGeometricPullback

/-! # Site transport of the normalized coordinate boundary

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4, Example 9.5 and
Proposition 9.6; current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
rank-one coordinate normalization and finite etale-origin transport paragraphs
(blueprint: lem-pur-coordinate-localization-splice-site-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- The normalized site transport carries the etale coordinate boundary to the
pro-etale coordinate boundary: the normalized pro-etale supported-Hom class of
`-M.alphaPro` is the transport by `v` of the normalized etale class of `-M.alphaEtale`.

Source: Milne, Section 9, Theorem 9.4 and Example 9.5; current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md, finite etale-origin transport
(blueprint: lem-pur-coordinate-localization-splice-site-comparison).

Proof: compare the etale and pro-etale injective snake models through the canonical
comparison unit. The comparison is exact and preserves the constant unit, the root
pullback and the restriction to the complement; hence the derived support map of `v`,
fixed by `v.supportUnit_spec` through the kernel inclusion, sends the snake boundary
`M.alphaEtale` (normalized by `M.etale_normalized`) to the snake boundary `M.alphaPro`
(normalized by `M.pro_normalized`), the open Kummer class going to `M.openProClass`.
The fields `constantIso_spec` and `closedIso_spec` of `v` fix the representable Hom
transport, and the cocycle normalizations of `M.chiEtale` and `M.chiPro` (evaluation of
the supported cocycle on one) agree on injective representatives under it; naturality
carries the equality to the coefficient object. Negation is preserved because every map
is additive. -/
theorem coordinateLocalization_spliceSupportClass_site (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (M : CoordinateBoundaryModel P T)
    (v : siteSupportHomTransport P (zeroSection T)) :
    M.chiPro.chi (P.coordinateProInput h (Line T)) 2
        (-M.alphaPro P h aT) =
      v.homMap (hB := Scheme.isContinuous_toProEt (Line T))
        (P.coordinateEtaleInput h (Line T)) 2
        (M.chiEtale.chi (P.coordinateEtaleInput h (Line T)) 2
          (-M.alphaEtale P h aT)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
