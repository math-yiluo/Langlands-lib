/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityShriekFreeComparison
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedProperUniversality

/-! # Universality of a compact-support trace from its geometric carrier -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Endofunctor.IsoAlgebra

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)

/-- Forgetting the Weil structure of compact support gives the compact support
attached to the base-changed compactification. -/
noncomputable def weilRightDerivedLowerShriekCompForgetIso :
    weilRightDerivedLowerShriek Λ c h ⋙
        (Endofunctor.IsoAlgebra.forget
          (lowerStar Λ t.geometricGaloisFrobenius.asIso.inv)).mapDerivedCategory ≅
      (Endofunctor.IsoAlgebra.forget
        (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h) :=
  exactRightDerivedForgetIso
    (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h))
    (lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g rfl)

/-- The free Weil resolution lifts universality for compact support, without a
properness assumption on the original morphism. -/
theorem bijective_map_comp_weilRightDerivedLowerShriek_of_bounded
    {P : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv))}
    {N : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar Λ t.geometricGaloisFrobenius.asIso.inv))}
    (ε : (weilRightDerivedLowerShriek Λ c h).obj P ⟶ N)
    (K : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv)))
    (hK : DerivedCategory.TStructure.t.bounded
      ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K))
    (hε : ∀ n : ℤ,
      (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).TraceUniversalAt
        ((shiftFunctor _ n).obj ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K))
        ((weilRightDerivedLowerShriekCompForgetIso Λ c h).inv.app P ≫
          (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map ε)) :
    (weilRightDerivedLowerShriek Λ c h).TraceUniversalAt K ε := by
  have : PreservesColimitsOfSize.{0, 0}
      (openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap c.i (c.i_comp_g_comp h))) :=
    (openImmersionLowerShriekUpperStarAdjunction Λ
      (Scheme.Hom.geometricFiberMap c.i (c.i_comp_g_comp h))).leftAdjoint_preservesColimits
  exact bijective_map_comp_exact_rightDerived_of_bounded
    (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h))
    (lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g rfl)
    (condensed_trace_preservesCoproduct Λ (Scheme.Hom.geometricFiberMap c.g rfl))
    ε K hK hε

end AlgebraicGeometry.ProEtale.CondensedRing
