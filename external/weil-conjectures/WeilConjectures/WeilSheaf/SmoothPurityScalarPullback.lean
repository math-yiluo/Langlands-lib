/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.TateTwist.TateModuleTrivialization
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal

/-! # Coefficient-parametric pullback comparisons for Tate descent -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (g : U ⟶ X)

/-- The coefficient extension unit, with the coefficient object left abstract. -/
noncomputable def purityPullbackUnit
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (g)^*[Ab.{u + 1}].obj M.X ⟶ ((g)^*⟦Λ⟧.obj M).X :=
  CondensedRing.upperStarUnitHom Λ g M

/-- Extension of an isomorphism of modules over the pulled-back coefficient ring. -/
noncomputable def purityExtendPullbackIso
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    (g)^*⟦Λ⟧.obj M ≅ (g)^*⟦Λ⟧.obj N :=
  (Mod.extendScalars (condensedPullbackHom Λ g)).mapIso e

/-- The scalar-extension comparison respects the extension units. -/
@[reassoc]
lemma purityExtendPullbackIso_unit
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    purityPullbackUnit Λ g M ≫ (purityExtendPullbackIso Λ g M N e).hom.hom =
      e.hom.hom ≫ purityPullbackUnit Λ g N :=
  Mod.extendUnitHom_extendScalarsMap (condensedPullbackHom Λ g) e.hom

variable [WeaklyEtale g]

attribute [local instance 20000] ProEtale.laxBraided_upperStar_of_weaklyEtale

/-- Extend a comparison formed using the weakly étale monoidal pullback. -/
noncomputable def purityExtendWeakPullbackIso
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    (g)^*⟦Λ⟧.obj M ≅ (g)^*⟦Λ⟧.obj N :=
  (Mod.extendScalars (condensedPullbackHom Λ g)).mapIso e

/-- The weakly étale comparison is normalized by the coefficient-extension units. -/
@[reassoc]
lemma purityExtendWeakPullbackIso_unit
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    purityPullbackUnit Λ g M ≫ (purityExtendWeakPullbackIso Λ g M N e).hom.hom =
      e.hom.hom ≫ purityPullbackUnit Λ g N :=
  Mod.extendUnitHom_extendScalarsMap (condensedPullbackHom Λ g) e.hom

omit [WeaklyEtale g] in
/-- The unit comparison for mapped modules is the identity on underlying objects. -/
@[simp]
lemma purityMapModUnitIso_hom_hom :
    ((g)^*[Ab.{u + 1}].mapModUnitIso (R := condensedRingObj Λ X)).hom.hom =
      𝟙 ((g)^*[Ab.{u + 1}].obj (condensedRingObj Λ X)) :=
  rfl

/-- The pullback unit for a variable commutative topological coefficient ring. -/
noncomputable def purityContinuousPullbackUnit (T : Type) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (g)^*[Ab.{u + 1}].obj M.X ⟶
      ((g)^*⟦Profinite.continuousMapRingObj T⟧.obj M).X :=
  purityPullbackUnit (Profinite.continuousMapRingObj T) g M

/-- Extend a weakly étale comparison before specializing the topological ring. -/
noncomputable def purityExtendContinuousWeakPullbackIso (T : Type) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    (g)^*⟦Profinite.continuousMapRingObj T⟧.obj M ≅
      (g)^*⟦Profinite.continuousMapRingObj T⟧.obj N :=
  purityExtendWeakPullbackIso (Profinite.continuousMapRingObj T) g M N e

end AlgebraicGeometry.ProEtale
