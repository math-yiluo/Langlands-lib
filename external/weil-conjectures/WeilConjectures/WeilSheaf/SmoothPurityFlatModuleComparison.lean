/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleModuleComparison

/-! # Named isomorphisms for flat coefficient extension in degree zero -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- Flat coefficient extension computed on a single complex. -/
noncomputable def purityExtendScalarsFlatSingleIso
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : ObjectProperty.flat M) :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorSingleFunctorIsoOfFlat hM

/-- Exact geometric pullback computed on a single complex. -/
noncomputable def purityPullbackSingleIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ g).app
      ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    (((g)^*⟦Λ⟧).mapDerivedCategorySingleFunctor 0).app M

lemma purityExtendScalarsSingleComparison_app_eq_flatSingleIso
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : ObjectProperty.flat M) :
    (purityExtendScalarsSingleComparison a X).app M =
      (purityExtendScalarsFlatSingleIso a X hM).hom :=
  purityExtendScalarsSingleComparison_app_eq_of_flat a X hM

lemma purityPullbackSingleComparison_app_eq_singleIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (purityPullbackSingleComparison Λ g).app M =
      (purityPullbackSingleIso Λ g M).hom :=
  purityPullbackSingleComparison_app_eq_exact Λ g M

end AlgebraicGeometry.ProEtale.CondensedRing
