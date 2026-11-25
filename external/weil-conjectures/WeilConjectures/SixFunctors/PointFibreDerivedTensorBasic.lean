/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import Mathlib.Algebra.CharP.CharAndCard

/-! # Derived tensor and the geometric-point fibre

Source: Stacks Project, Tag 07A4, `lemma-pullback-tensor-product`;
(blueprint: def-sf-point-fibre-tensor-system).

The definitions record genuine strong symmetric monoidal data for all four
coefficient stages, with prescribed tensor bifunctors and coefficient objects.
Canonical representative normalizations and coefficient-change diagrams are
specified by the other helper definitions; this data alone asserts no canonicity.
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-! The following named functors encapsulate the four displayed stage constructions
while retaining their definitions. This avoids repeatedly unfolding
the large coefficient-category terms while elaborating the theorem below. -/

/-- A strong symmetric monoidal fibre functor on the specified tensor subcategory.
The source tensor and coefficient unit are fixed by `tensor_eq` and `unit_eq`.
`strong` includes the actual associator and both unitor diagrams, and `symmetry`
is the braiding square. Canonical representative normalizations are imposed below;
this structure alone does not claim canonicity.
Source: Stacks 07A4 and the tensor constraints in the node's final sentence
(blueprint: def-sf-point-fibre-tensor-system). -/
structure PointFibreDerivedTensorComparisonData
    {C : Type c} {A : Type e} {B : Type d}
    [Category.{hc} C] [Category.{he} A] [Category.{hd} B]
    (I : C ⥤ A) (F : A ⥤ B) (T : C × C ⥤ A) (unit : A)
    [MonoidalCategory B] (β : BraidedCategory B) where
  /-- The derived tensor constraints on the source subcategory. -/
  monoidal : MonoidalCategory C
  /-- Its tensor is exactly the recorded derived tensor after inclusion. -/
  tensor_eq : @MonoidalCategory.tensor C _ monoidal ⋙ I = T
  /-- Its unit is the coefficient object specified by the coefficient construction. -/
  unit_eq : I.obj monoidal.tensorUnit = unit
  /-- Strong monoidality includes naturality, associativity and both unit diagrams. -/
  strong : @Functor.Monoidal C _ monoidal B _ _ (I ⋙ F)
  /-- The source has symmetric derived tensor, including the hexagon and involution. -/
  symmetric : @SymmetricCategory C _ monoidal
  /-- The comparison intertwines the actual source and target braidings. -/
  symmetry : ∀ X Y : C,
    (@Functor.LaxMonoidal.μ C _ monoidal B _ _ (I ⋙ F) strong.toLaxMonoidal X Y) ≫
        (I ⋙ F).map (symmetric.toBraidedCategory.braiding X Y).hom =
      (β.braiding ((I ⋙ F).obj X) ((I ⋙ F).obj Y)).hom ≫
        (@Functor.LaxMonoidal.μ C _ monoidal B _ _ (I ⋙ F) strong.toLaxMonoidal Y X)

/-- The tensor comparison extracted from the strong structure, in the node's direction.
Source: Stacks 07A4 (blueprint: def-sf-point-fibre-tensor-system). -/
def PointFibreDerivedTensorComparisonData.tensorIso
    {C : Type c} {A : Type e} {B : Type d}
    [Category.{hc} C] [Category.{he} A] [Category.{hd} B]
    [MonoidalCategory B] {β : BraidedCategory B}
    {I : C ⥤ A} {F : A ⥤ B} {T : C × C ⥤ A} {unit : A}
    (S : PointFibreDerivedTensorComparisonData I F T unit β) (X Y : C) :
    F.obj (T.obj (X, Y)) ≅ F.obj (I.obj X) ⊗ F.obj (I.obj Y) :=
  F.mapIso (eqToIso (congrArg (fun G : C × C ⥤ A ↦ G.obj (X, Y)) S.tensor_eq).symm) ≪≫
    (@Functor.Monoidal.μIso C _ S.monoidal B _ _ (I ⋙ F) S.strong X Y).symm

end WeilConjectures
