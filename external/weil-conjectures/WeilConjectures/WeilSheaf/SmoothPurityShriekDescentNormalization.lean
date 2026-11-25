/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenDescentNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityDescentPasting
public import WeilConjectures.WeilSheaf.SmoothPurityShriekWeilUniversality
public import WeilConjectures.WeilSheaf.SmoothPurityShriekDescentComparisons

/-! # The geometric carrier of descended compact support -/

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

/-- The descent comparison for compact support forgets to the specified geometric
base change for the same compactification. -/
lemma geometricFiberWeilRightDerivedLowerShriekIso_forget
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekGeometricFiberIso Λ c h).hom.app K =
      (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
        (Endofunctor.IsoAlgebra.forget _)).inv.app
          ((rightDerivedLowerShriekOfCompactification Λ c).obj K) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        ((geometricFiberWeilRightDerivedLowerShriekIso c h hi hg).inv.app K) ≫
      (weilRightDerivedLowerShriekCompForgetIso Λ c h).hom.app
        ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).map
        ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
          (Endofunctor.IsoAlgebra.forget _)).hom.app K) := by
  have he := Functor.traceCompDescentIso_forget
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
      (Endofunctor.IsoAlgebra.forget _))
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ (c.g ≫ t))
      (Endofunctor.IsoAlgebra.forget _))
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
      (Endofunctor.IsoAlgebra.forget _))
    (geometricFiberWeilExtensionByZeroMapDerivedCategoryIso hi)
    (geometricFiberWeilRightDerivedLowerStarIso hg)
    (Functor.mapDerivedCategoryCompForgetIso (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
      (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h))))
    (Endofunctor.IsoAlgebra.derivedForgetCommIso
      (lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g rfl))
    (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap c.i (c.i_comp_g_comp h)))
    (rightDerivedLowerStarBaseChangeIso Λ (Scheme.Hom.isPullback_geometricFiberMap c.g rfl).flip)
    (geometricFiberWeilExtensionByZeroMapDerivedCategoryIso_forget Λ hi)
    (geometricFiberWeilRightDerivedLowerStarIso_forget Λ hg) K
  rw [rightDerivedLowerShriekGeometricFiberIso_eq_compForgetIso,
    geometricFiberWeilRightDerivedLowerShriekIso_eq_traceCompDescentIso,
    weilRightDerivedLowerShriekCompForgetIso_eq_compForgetIso]
  dsimp +instances only [rightDerivedLowerShriekOfCompactification, weilRightDerivedLowerShriek,
    Functor.comp_obj, Functor.comp_map, Iso.symm_hom, Iso.symm_inv] at he ⊢
  exact_mod_proofs he

variable
  {P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
  {N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
  (ε : (rightDerivedLowerShriekOfCompactification Λ c).obj P ⟶ N)

/-- Descend a compact-support trace defined over the finite base field. -/
noncomputable def geometricFiberWeilShriekTrace :
    (weilRightDerivedLowerShriek Λ c h).obj
      ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj P) ⟶
      (geometricFiberWeilLowerStar Λ t).mapDerivedCategory.obj N :=
  (geometricFiberWeilRightDerivedLowerShriekIso c h hi hg).hom.app P ≫
    (geometricFiberWeilLowerStar Λ t).mapDerivedCategory.map ε

/-- The geometric carrier of the descended compact-support trace is its ordinary
base change. -/
lemma geometricFiberWeilShriekTrace_forget :
    (weilRightDerivedLowerShriekCompForgetIso Λ c h).inv.app
        ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj P) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        (geometricFiberWeilShriekTrace Λ c h hi hg ε) =
      (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).map
        ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
          (Endofunctor.IsoAlgebra.forget _)).hom.app P) ≫
      (rightDerivedLowerShriekGeometricFiberIso Λ c h).inv.app P ≫
      (upperStar Λ t.geometricFiberProj).mapDerivedCategory.map ε ≫
      (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
        (Endofunctor.IsoAlgebra.forget _)).inv.app N := by
  exact Functor.descendedTrace_forget
    (rightDerivedLowerShriekOfCompactification Λ c)
    (geometricFiberWeilLowerStar Λ s).mapDerivedCategory
    (geometricFiberWeilLowerStar Λ t).mapDerivedCategory
    (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory
    (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory
    (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h))
    (weilRightDerivedLowerShriek Λ c h)
    (upperStar Λ s.geometricFiberProj).mapDerivedCategory
    (upperStar Λ t.geometricFiberProj).mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
      (Endofunctor.IsoAlgebra.forget _))
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
      (Endofunctor.IsoAlgebra.forget _))
    (geometricFiberWeilRightDerivedLowerShriekIso c h hi hg)
    (weilRightDerivedLowerShriekCompForgetIso Λ c h)
    (rightDerivedLowerShriekGeometricFiberIso Λ c h)
    (geometricFiberWeilRightDerivedLowerShriekIso_forget Λ c h hi hg) ε

end AlgebraicGeometry.ProEtale.CondensedRing
