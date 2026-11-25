/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeSite
public import WeilConjectures.WeilSheaf.SmoothPurityComparisonRestriction

/-! # Free-sheaf site comparison and geometric pullback -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

private lemma purity_forward_square_of_two_inverses {C : Type*} [Category C]
    {A B C' D E : C} (a : A ≅ B) (b : B ≅ C') (d : D ≅ E)
    (u : C' ⟶ E) (v : A ⟶ D)
    (h : u ≫ d.inv = b.inv ≫ a.inv ≫ v) :
    a.hom ≫ b.hom ≫ u = v ≫ d.hom := by
  apply (cancel_mono d.inv).mp
  simp only [Category.assoc, h, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The free pro-étale sheaf on the inverse image of an étale abelian sheaf
commutes with geometric pullback. -/
noncomputable def purityComparisonFreePullbackIso :
    (ν^*(Y)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T Y) ⋙
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      Etale.upperStar Ab.{u + 1} g ⋙ (ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T X) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (purityFiniteFreeSheafPullbackIso T g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (comparisonUpperStarUpperStarIso Ab.{u + 1} g) _ ≪≫
    Functor.associator _ _ _

omit [TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
lemma purityComparisonFreePullbackIso_conjugate :
    conjugateIsoEquiv
      ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X)))
      (((comparisonAdjunction Ab.{u + 1} Y).comp (purityFiniteFreeSheafAdjunction T Y)).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g))
      (purityComparisonFreePullbackIso T g) = Iso.refl _ := by
  unfold purityComparisonFreePullbackIso
  rw [conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} Y).comp
      ((purityFiniteFreeSheafAdjunction T Y).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g))),
    conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} Y).comp
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (purityFiniteFreeSheafAdjunction T X))),
    conjugateIsoEquiv_trans _ (((comparisonAdjunction Ab.{u + 1} Y).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} g)).comp
        (purityFiniteFreeSheafAdjunction T X)),
    conjugateIsoEquiv_trans _ (((Etale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (comparisonAdjunction Ab.{u + 1} X)).comp (purityFiniteFreeSheafAdjunction T X)),
    conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator]
  simp only [purityFiniteFreeSheafPullbackIso, comparisonUpperStarUpperStarIso,
    lowerStarComparisonLowerStarIso, Equiv.apply_symm_apply]
  ext N
  simp
  rfl

omit [TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- The site comparison respects the free-sheaf geometric datum. -/
lemma purity_comparisonFreeSheaf_pullback
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((Etale.upperStarExtendScalarsIso (ULift.{u + 1} T) g).hom.app M) ≫
        (purityComparisonFreeSheafIso T X).inv.app ((Etale.upperStar Ab.{u + 1} g).obj M) =
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).inv.app
          ((Etale.extendScalars (ULift.{u + 1} T) Y).obj M) ≫
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((purityComparisonFreeSheafIso T Y).inv.app M) ≫
        (purityComparisonFreePullbackIso T g).hom.app M := by
  apply purity_free_pullback_cube
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Etale.extendScalarsAdjunction (ULift.{u + 1} T) Y)
    (Etale.extendScalarsAdjunction (ULift.{u + 1} T) X)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)
    (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y)
    (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) X)
    ((comparisonAdjunction Ab.{u + 1} Y).comp (purityFiniteFreeSheafAdjunction T Y))
    ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)
    (Etale.upperStarExtendScalarsIso (ULift.{u + 1} T) g)
    (purityComparisonFreePullbackIso T g)
    (purityComparisonFreeSheafIso T Y).symm
    (purityComparisonFreeSheafIso T X).symm
    (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).symm
  intro N
  rw [purityComparisonFreePullbackIso_conjugate]
  simp only [purityComparisonFreeSheafIso, comparisonUpperStarUpperStarIso,
    Etale.upperStarExtendScalarsIso, purity_leftAdjointUniq_ofNatIsoRight,
    Adjunction.symm_conjugateIsoEquiv_symm_apply, Equiv.apply_symm_apply,
    lowerStarComparisonLowerStarIso, Iso.refl_symm, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

omit [TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- Forward form of the free-sheaf site comparison square. -/
lemma purity_comparisonFreeSheaf_pullback_forward
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((purityComparisonFreeSheafIso T Y).hom.app M) ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).hom.app
          ((Etale.extendScalars (ULift.{u + 1} T) Y).obj M) ≫
        ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((Etale.upperStarExtendScalarsIso (ULift.{u + 1} T) g).hom.app M) =
      (purityComparisonFreePullbackIso T g).hom.app M ≫
        (purityComparisonFreeSheafIso T X).hom.app ((Etale.upperStar Ab.{u + 1} g).obj M) := by
  exact purity_forward_square_of_two_inverses
    ((g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].mapIso
      ((purityComparisonFreeSheafIso T Y).app M))
    ((comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).app
      ((Etale.extendScalars (ULift.{u + 1} T) Y).obj M))
    ((purityComparisonFreeSheafIso T X).app ((Etale.upperStar Ab.{u + 1} g).obj M))
    _ _ (purity_comparisonFreeSheaf_pullback T g M)

end AlgebraicGeometry.ProEtale
