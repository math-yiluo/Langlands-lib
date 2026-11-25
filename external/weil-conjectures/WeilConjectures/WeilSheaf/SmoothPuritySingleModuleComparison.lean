/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySingleExactNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull

/-! # Named degree-zero comparisons for coefficient extension and geometric pullback -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- Derived coefficient extension, with its instances fixed at this definition. -/
noncomputable def purityDerivedCoefficientExtension (a : Λ ⟶ Λ') [IsMonHom a]
    (X : Scheme.{u}) := L(Mod.extendScalars (coefficientMap a X))

/-- Derived geometric pullback, with its instances fixed at this definition. -/
noncomputable def purityDerivedPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) := L((g)^*⟦Λ⟧)

/-- The counit defining derived coefficient extension. -/
noncomputable def purityCoefficientHomotopyCounit (a : Λ ⟶ Λ') [IsMonHom a]
    (X : Scheme.{u}) := (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit

/-- The counit defining derived geometric pullback. -/
noncomputable def purityPullbackHomotopyCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  ((g)^*⟦Λ⟧).leftDerivedFunctorCounit

/-- The degree-zero comparison for coefficient extension. -/
noncomputable def purityExtendScalarsSingleComparison (a : Λ ⟶ Λ') [IsMonHom a]
    (X : Scheme.{u}) := (Mod.extendScalars (coefficientMap a X)).puritySingleComparison

/-- The degree-zero comparison for geometric pullback. -/
noncomputable def purityPullbackSingleComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y) := ((g)^*⟦Λ⟧).puritySingleComparison

lemma purityExtendScalarsSingleComparison_app_eq_of_flat
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : ObjectProperty.flat M) :
    (purityExtendScalarsSingleComparison a X).app M =
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorSingleFunctorIsoOfFlat hM).hom :=
  Functor.puritySingleComparison_app_eq_of_flat _ hM

lemma purityPullbackSingleComparison_app_eq_exact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (purityPullbackSingleComparison Λ g).app M =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        (((g)^*⟦Λ⟧).mapDerivedCategorySingleFunctor 0).hom.app M :=
  Functor.puritySingleComparison_app_eq_exact _ M

end AlgebraicGeometry.ProEtale.CondensedRing
