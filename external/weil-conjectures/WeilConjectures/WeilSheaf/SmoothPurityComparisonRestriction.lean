/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-! # Identifying the two canonical comparison-site pullback isomorphisms -/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (D : Type v) [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] {X Y : Scheme.{u}} (g : X ⟶ Y)

omit [Abelian D] [IsGrothendieckAbelian.{u + 1} D] in
/-- The comparison of direct images is the identity on sections over the same
chosen fibre product, for either of the two upstream constructions. -/
lemma purity_lowerStarCompComparisonLowerStarIso_eq :
    lowerStarCompComparisonLowerStarIso g D = lowerStarComparisonLowerStarIso D g := by
  ext G U
  simp only [lowerStarCompComparisonLowerStarIso, lowerStarComparisonLowerStarIso,
    Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, toProEtCompOverPullbackIso,
    ObjectProperty.ι_obj, Iso.refl_symm, Iso.trans_hom, Iso.refl_hom,
    NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Functor.whiskerRight_app,
    Functor.op_obj, NatTrans.op_app, NatIso.ofComponents_inv_app, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp]
  rfl

/-- The finite-reading inverse-image comparison is the inverse of the usual
comparison-site pullback isomorphism. -/
lemma purity_comparisonCoefficientPullbackIso_eq :
    comparisonCoefficientPullbackIso D g = (comparisonUpperStarUpperStarIso D g).symm := by
  unfold comparisonCoefficientPullbackIso comparisonUpperStarUpperStarIso
  rw [purity_lowerStarCompComparisonLowerStarIso_eq]
  rfl

end AlgebraicGeometry.ProEtale
