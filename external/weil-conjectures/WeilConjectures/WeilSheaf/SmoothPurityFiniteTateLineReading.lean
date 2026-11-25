/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeRootsReading
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf

/-! # Reading the finite Tate line with its canonical geometric datum -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] (N : ℕ) (hN : 0 < N)
  (hchar : ringChar (ULift.{u + 1} T) = N)

/-- The free root line, read as the usual étale Tate sheaf. -/
noncomputable def purityFiniteRootTateReadingIso
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence X T).functor.obj
        ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) X)).obj
          (rootsOfUnitySheaf X N)) ≅
      ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
        (Etale.tateSheaf (ULift.{u + 1} T) X) :=
  finiteCoefficientModEquivalenceFreeRootsOfUnityIso X N T hN hX ≪≫
    ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].mapIso
      ((Etale.extendScalars _ X).mapIso
        (eqToIso (congrArg (X.rootsOfUnitySheaf) hchar.symm)))

/-- The reading carries the actual free-root pullback to the usual étale Tate
pullback, including the change from the root exponent to the coefficient characteristic. -/
lemma purityFiniteRootTateReadingIso_pullback
    (hT : (N : T) = 0) {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence X T).functor.map
          ((CondensedRing.freeFunctorCompUpperStarIso
            (Profinite.continuousMapRingObj T) g).hom.app (rootsOfUnitySheaf Y N)) ≫
        (finiteCoefficientModEquivalence X T).functor.map
          ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) X)).map
            (upperStarRootsOfUnitySheafHom g N)) ≫
        (purityFiniteRootTateReadingIso T N hN hchar X hX).hom =
      (upperStarFiniteCoefficientModEquivalenceIso g T).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) Y)).obj
            (rootsOfUnitySheaf Y N)) ≫
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          (purityFiniteRootTateReadingIso T N hN hchar Y hY).hom ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).hom.app
          (Etale.tateSheaf (ULift.{u + 1} T) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          (Etale.upperStarTateSheafToTateSheaf (ULift.{u + 1} T) g) := by
  subst N
  simpa only [purityFiniteRootTateReadingIso, eqToIso_refl, Functor.mapIso_refl,
    Iso.trans_refl, Etale.tateSheaf, Etale.upperStarTateSheafToTateSheaf] using
    purity_finiteCoefficientModEquivalenceFreeRootsOfUnityIso_pullback
      T (ringChar (ULift.{u + 1} T)) hN hT g hY hX

end AlgebraicGeometry.ProEtale
