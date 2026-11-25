/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityShriekDescentNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedTrace

/-! # Geometric universality of the descended compact-support trace -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Coefficients

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)
  (hi : UpperStarWeilCompatible Λ c.i (c.i_comp_g_comp h))
  (hg : UpperStarWeilCompatible Λ c.g (rfl : c.g ≫ t = c.g ≫ t))
  {P : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
  {N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
  (ε : (rightDerivedLowerShriekOfCompactification Λ c).obj P ⟶ N)

/-- The ordinary base-changed trace tests the geometric carrier of the actual
descended trace. -/
theorem geometricFiberWeilShriekTrace_universal
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology s.geometricFiber) Ab.{u + 1})
      (condensedRingObj Λ s.geometricFiber)))
    (hε : (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).TraceUniversalAt K
      ((rightDerivedLowerShriekGeometricFiberIso Λ c h).inv.app P ≫
        (upperStar Λ t.geometricFiberProj).mapDerivedCategory.map ε)) :
    (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).TraceUniversalAt K
      ((weilRightDerivedLowerShriekCompForgetIso Λ c h).inv.app
        ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj P) ≫
        (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
          (geometricFiberWeilShriekTrace Λ c h hi hg ε)) := by
  exact Functor.bijective_map_comp_of_trace_coordinates
    (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h))
    ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
      (Endofunctor.IsoAlgebra.forget _)).app P)
    ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
      (Endofunctor.IsoAlgebra.forget _)).symm.app N)
    ((rightDerivedLowerShriekGeometricFiberIso Λ c h).inv.app P)
    ((upperStar Λ t.geometricFiberProj).mapDerivedCategory.map ε) _
    (geometricFiberWeilShriekTrace_forget Λ c h hi hg ε) hε

end Coefficients

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (d : ℕ)

/-- Read the bounded-constructible smooth trace on the ambient compactification. -/
noncomputable def ambientSmoothTrace :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
      (compactificationOverField f)).obj (boundedConstructibleTateTwist l X d (2 * d)).obj ⟶
      (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧)).obj :=
  (boundedConstructibleLowerShriekOfCompactificationCompatibility l
    (compactificationOverField f)).inv.app (boundedConstructibleTateTwist l X d (2 * d)) ≫
    (smoothTrace l f d).hom

/-- The existing descended smooth trace agrees with descent of its ambient trace. -/
lemma geometricFiberWeilSmoothTrace_eq_shriekTrace :
    geometricFiberWeilSmoothTrace l f d =
      geometricFiberWeilShriekTrace (Profinite.padicAlgClRingObj l)
        (compactificationOverField f) (Over.w f)
        (upperStarWeilCompatible _ _ _) (upperStarWeilCompatible _ _ _)
        (ambientSmoothTrace l f d) := by
  simp [geometricFiberWeilSmoothTrace, geometricFiberWeilShriekTrace, ambientSmoothTrace,
    boundedConstructibleLowerShriekGeometricFiberWeilIso,
    boundedConstructibleLowerShriekOfCompactificationGeometricFiberWeilIso,
    geometricFiberWeilRightDerivedLowerShriekIso', Functor.map_comp, Category.assoc]

/-- Universality of the specified ordinary geometric trace lifts to the actual
Weil smooth trace for an arbitrary, possibly non-proper, smooth morphism. -/
theorem geometricFiberWeilSmoothTrace_weilUniversal
    (K : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar (Profinite.padicAlgClRingObj l) X.hom.geometricGaloisFrobenius.asIso.inv)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      X.hom.geometricFiber) ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K))
    (hε : ∀ Q : Dᵇc(X.hom.geometricFiber)⟦Profinite.padicAlgClRingObj l⟧,
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
        ((compactificationOverField f).geometricFiber (Over.w f))).TraceUniversalAt Q.obj
        ((rightDerivedLowerShriekGeometricFiberIso (Profinite.padicAlgClRingObj l)
          (compactificationOverField f) (Over.w f)).inv.app
            (boundedConstructibleTateTwist l X d (2 * d)).obj ≫
          (upperStar (Profinite.padicAlgClRingObj l)
            Y.hom.geometricFiberProj).mapDerivedCategory.map
            (ambientSmoothTrace l f d))) :
    (weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l)
      (compactificationOverField f) (Over.w f)).TraceUniversalAt K
        (geometricFiberWeilSmoothTrace l f d) := by
  rw [geometricFiberWeilSmoothTrace_eq_shriekTrace]
  apply bijective_map_comp_weilRightDerivedLowerShriek_of_bounded _ _ _ _ K hK.1
  intro n
  apply geometricFiberWeilShriekTrace_universal
  exact hε ⟨_, ObjectProperty.le_shift (P := boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj l) X.hom.geometricFiber)) n _ hK⟩

end AlgebraicGeometry.ProEtale.CondensedRing
