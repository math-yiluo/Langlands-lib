/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeReading
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteRootReading
public import WeilConjectures.WeilSheaf.SmoothPurityComparisonRestriction

/-! # Geometric compatibility of the finite free-root comparison -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] (N : ℕ) (hN : 0 < N) (hT : (N : T) = 0)
  {X Y : Scheme.{u}} (g : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
  (hX : IsUnit (N : Γ(X, ⊤)))

include T hT

omit [TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] in
/-- Inverse-coordinate form of the root comparison square. -/
lemma purity_comparisonUpperStarRootsOfUnityIso_pullback_inv :
    upperStarRootsOfUnitySheafHom g N ≫
        (comparisonUpperStarRootsOfUnityIso X N hN hX).inv =
      (g)^*[Ab.{u + 1}].map (comparisonUpperStarRootsOfUnityIso Y N hN hY).inv ≫
        (comparisonUpperStarUpperStarIso Ab.{u + 1} g).hom.app (Y.rootsOfUnitySheaf N) ≫
        ν^*(X)[Ab.{u + 1}].map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g) := by
  have hNT : (N : ULift.{u + 1} T) = 0 := by
    apply ULift.ext
    exact hT
  have h := purity_comparisonUpperStarRootsOfUnityIso_pullback
    (ULift.{u + 1} T) N hN hNT g hY hX
  rw [purity_comparisonCoefficientPullbackIso_eq, Iso.symm_inv] at h
  apply (cancel_epi ((g)^*[Ab.{u + 1}].map
    (comparisonUpperStarRootsOfUnityIso Y N hN hY).hom)).mp
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Functor.map_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The finite reading of the free module on roots of unity carries its actual
geometric datum to the canonical étale root datum. -/
lemma purity_finiteCoefficientModEquivalenceFreeRootsOfUnityIso_pullback :
    (finiteCoefficientModEquivalence X T).functor.map
          ((CondensedRing.freeFunctorCompUpperStarIso
            (Profinite.continuousMapRingObj T) g).hom.app (rootsOfUnitySheaf Y N)) ≫
        (finiteCoefficientModEquivalence X T).functor.map
          ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) X)).map
            (upperStarRootsOfUnitySheafHom g N)) ≫
        (finiteCoefficientModEquivalenceFreeRootsOfUnityIso X N T hN hX).hom =
      (upperStarFiniteCoefficientModEquivalenceIso g T).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) Y)).obj
            (rootsOfUnitySheaf Y N)) ≫
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          (finiteCoefficientModEquivalenceFreeRootsOfUnityIso Y N T hN hY).hom ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).hom.app
          ((Etale.extendScalars (ULift.{u + 1} T) Y).obj (Y.rootsOfUnitySheaf N)) ≫
        ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((Etale.upperStarExtendScalarsIso (ULift.{u + 1} T) g).hom.app
              (Y.rootsOfUnitySheaf N) ≫
            (Etale.extendScalars (ULift.{u + 1} T) X).map
              (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g)) := by
  have hroot := purity_comparisonUpperStarRootsOfUnityIso_pullback_inv T N hN hT g hY hX
  have hfree := (CondensedRing.freeFunctorCompUpperStarIso
    (Profinite.continuousMapRingObj T) g).hom.naturality
    (comparisonUpperStarRootsOfUnityIso Y N hN hY).inv
  have hread := (comparisonUpperStarFreeIso T X).hom.naturality
    (upperStarRootsOfUnitySheafToRootsOfUnitySheaf N g)
  have hcoeff := (upperStarFiniteCoefficientModEquivalenceIso g T).hom.naturality
    ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) Y)).map
      (comparisonUpperStarRootsOfUnityIso Y N hN hY).inv)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hfree hread hcoeff
  simp only [finiteCoefficientModEquivalenceFreeRootsOfUnityIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  conv_lhs =>
    rhs; rw [← Functor.map_comp_assoc, ← Functor.map_comp, hroot]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hfree, Functor.map_comp, Category.assoc]
  rw [hread]
  rw [reassoc_of% (purity_comparisonUpperStarFreeIso_pullback T g
    (Y.rootsOfUnitySheaf N))]
  rw [reassoc_of% hcoeff]

end AlgebraicGeometry.ProEtale
