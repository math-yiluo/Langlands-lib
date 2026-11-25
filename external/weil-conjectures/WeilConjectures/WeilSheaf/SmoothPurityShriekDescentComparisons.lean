/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenDescentNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityDescentPasting
public import WeilConjectures.WeilSheaf.SmoothPurityShriekWeilUniversality

/-! # Composite comparisons for descended compact support -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)
  (hi : UpperStarWeilCompatible Λ c.i (c.i_comp_g_comp h))
  (hg : UpperStarWeilCompatible Λ c.g (rfl : c.g ≫ t = c.g ≫ t))

/-- Geometric compact-support base change is the paste of its open and proper parts. -/
lemma rightDerivedLowerShriekGeometricFiberIso_eq_compForgetIso :
    rightDerivedLowerShriekGeometricFiberIso Λ c h =
      Adjunction.compForgetIso
        (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ
          (Scheme.Hom.isPullback_geometricFiberMap c.i (c.i_comp_g_comp h)))
        (rightDerivedLowerStarBaseChangeIso Λ
          (Scheme.Hom.isPullback_geometricFiberMap c.g rfl).flip) := rfl

/-- Weil descent of compact support is the paste of its open and proper descent squares. -/
lemma geometricFiberWeilRightDerivedLowerShriekIso_eq_traceCompDescentIso :
    geometricFiberWeilRightDerivedLowerShriekIso c h hi hg =
      Functor.traceCompDescentIso
        (geometricFiberWeilExtensionByZeroMapDerivedCategoryIso hi)
        (geometricFiberWeilRightDerivedLowerStarIso hg) := rfl

/-- Forgetting compact support pastes the exact open and derived proper comparisons. -/
lemma weilRightDerivedLowerShriekCompForgetIso_eq_compForgetIso :
    weilRightDerivedLowerShriekCompForgetIso Λ c h =
      Adjunction.compForgetIso
        (Functor.mapDerivedCategoryCompForgetIso (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
          (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h))))
        (Endofunctor.IsoAlgebra.derivedForgetCommIso
          (lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g rfl)) := rfl

end AlgebraicGeometry.ProEtale.CondensedRing
