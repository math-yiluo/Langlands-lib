/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedComparisonTensorAdjunction
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions

/-! # Data for scalar adjunction and tensor realization in the coefficient square

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 07A6; blueprint
main-20261015, proper-base-change-rational.proof.md (3)
(blueprint: lem-sfb-coefficient-scalar-tensor-realization).

The section realization retains the ordinary balanced generators, the derived Hom
bijection, and the signed total representative equation. The pullback path comparison
is constructed by localization of the ordinary coefficient square, independently of
the derived direct-image mate. All categories are ordinary unbounded derived categories.

## Main definitions

* `coefficientScalarPathIso`: the localized ordinary coefficient-square comparison.
* `CoefficientScalarSectionRealization`: the normalized scalar adjunction and tensor realization.

The realization theorem remains in `CoefficientScalarTensorRealization`. These
constructions are shared with its independent section-realization and derived tensor-square lemmas.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]

/-- The section-ring map of the actual coefficient morphism.
Source: Stacks 03EK, 07A6
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
abbrev coefficientSectionScalarMap (Z : Scheme.{u}) :
    ModuleRingedComparison.ring R Z ⟶ ModuleRingedComparison.ring S Z :=
  InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Z) (coefficientMap a Z)

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

/-- The canonical scalar/pullback path comparison, obtained by total left derivation
of the ordinary ring-compatible coefficient square. Thus its direction is P_S T_Y → T_X P_R.
Source: Stacks 0D6D, 07A4
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientScalarPathIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalScalarExtension a Y ⋙ moduleObjectDerivedPullback S f ≅
      moduleObjectDerivedPullback R f ⋙ internalScalarExtension a X :=
  letI := internalScalarMonoidal a X
  letI := internalScalarMonoidal a Y
  Functor.leftDerivedFunctorCompNatIso (upperStar R f)
    (Mod.extendScalars (coefficientMap a X)) (Mod.extendScalars (coefficientMap a Y))
    (upperStar S f) (pullIso a f).symm

/-- The actual geometric derived tensor comparison, with its pointwise type displayed.
This is the comparison used in the module-object projection morphism, without replacing it
by an unspecified monoidal structure.
Source: blueprint main-20261015, six-functors basics, module derived push/pull
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientGeometricTensorComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory (ModuleRingedComparison.internalModules Λ Y)) :
    (moduleObjectDerivedPullback Λ f).obj (((derivedTensor Λ Y).obj A).obj B) ⟶
      ((derivedTensor Λ X).obj ((moduleObjectDerivedPullback Λ f).obj A)).obj
        ((moduleObjectDerivedPullback Λ f).obj B) :=
  ((leftDerivedUpperStarTensor Λ f).app A).app B

/-- The actual sheafification image of s tensor x, in a normalized section scalar pair.
The equality transport identifies its extension object with the existing changeOfRings.
Source: Stacks 03EK
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientSectionScalarPure (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (M : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
    (s : (ModuleRingedComparison.ring S Z).obj.obj V) (x : M.val.obj V) :
    (b.extension.obj M).val.obj V :=
  (eqToHom (b.extension_obj M).symm).val.app V
    ((toSheafify (Scheme.ProEt.topology Z)
      (SheafOfModules.changeOfRingsPresheaf (coefficientSectionScalarMap a Z) M).presheaf).app V
        (s ⊗ₜ[_, ((coefficientSectionScalarMap a Z).hom.app V).hom] x))

/-- The canonical exact scalar-extension comparison on a complex. Its two factors
are the universal derived-to-exact comparison and the exact localization comparison.
Source: Stacks 06YY, 07A6
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientInternalScalarComplex (Z : Scheme.{u})
    (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ) :
    (internalScalarExtension a Z).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) :=
  (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj P) ≫
    (Mod.extendScalars (coefficientMap a Z)).mapDerivedCategoryFactors.hom.app P

/-- Signed direct-sum totalization of the ordinary scalar tensorator.
Source: Stacks 07A4, constituent maps of 03EL
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def coefficientSectionScalarTotal (Z : Scheme.{u})
    (b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z))
    (m : b.extension.Monoidal)
    (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ) :
    (b.extension.mapHomologicalComplex (.up ℤ)).obj
        ((ModuleRingedComparison.totalTensor R Z).obj (P, Q)) ⟶
      (ModuleRingedComparison.totalTensor S Z).obj
        ((b.extension.mapHomologicalComplex (.up ℤ)).obj P,
          (b.extension.mapHomologicalComplex (.up ℤ)).obj Q) :=
  letI := m
  letI : PreservesColimitsOfSize.{0, 0} b.extension :=
    b.ordinaryAdjunction.leftAdjoint_preservesColimits
  (b.extension.mapHomologicalComplex (.up ℤ)).map
      (eqToHom (ModuleRingedComparison.totalTensor_obj R Z P Q)) ≫
    HomologicalComplex.mapBifunctorComparison
      (F := curriedTensor (ModuleRingedComparison.modules R Z))
      (F' := curriedTensor (ModuleRingedComparison.modules S Z))
      (G := b.extension) (G₁ := b.extension) (G₂ := b.extension)
      (Functor.OplaxMonoidal.δNatTrans b.extension) (.up ℤ) P Q ≫
    eqToHom (ModuleRingedComparison.totalTensor_obj S Z
      ((b.extension.mapHomologicalComplex (.up ℤ)).obj P)
      ((b.extension.mapHomologicalComplex (.up ℤ)).obj Q)).symm

/-- The scalar realization clauses, with every operation tied to the actual coefficient
map. The section pair has the existing universal left-derived and adjunction normalization.
The ordinary tensorator is pinned on all generalized balanced generators. The derived
one is pinned separately by its flat-term K-flat representative square, and is then
identified with the specified internal tensorator. No existence witness is chosen as data.
Source: Stacks 03EK, 03EL, 06YY, 07A4, 07A6
(blueprint: lem-sfb-coefficient-scalar-tensor-realization). -/
def CoefficientScalarSectionRealization (Z : Scheme.{u}) : Prop :=
  ∃ b : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (coefficientSectionScalarMap a Z),
  ∃ o : Mod.extendScalars (coefficientMap a Z) ⋙
      (ModuleRingedComparison.equivalence S Z).functor ≅
    (ModuleRingedComparison.equivalence R Z).functor ⋙ b.extension,
  ∃ r : Mod.comap (coefficientMap a Z) ⋙
      (ModuleRingedComparison.equivalence R Z).functor ≅
    (ModuleRingedComparison.equivalence S Z).functor ⋙
      SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
      (coefficientSectionScalarMap a Z),
  (∀ (M : ModuleRingedComparison.internalModules R Z) (V : Z.ProEtᵒᵖ)
      (s : (condensedRingObj S Z).obj.obj V) (x : M.X.obj.obj V),
    (o.hom.app M).val.app V
        (InternalAbelianSheafModule.internalScalarGenerator.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Z)
          (coefficientMap a Z) M V s x) =
      coefficientSectionScalarPure a Z b
        ((ModuleRingedComparison.equivalence R Z).functor.obj M) V s x) ∧
  (∀ (N : ModuleRingedComparison.internalModules S Z) (V : Z.ProEtᵒᵖ)
      (x : N.X.obj.obj V), (r.hom.app N).val.app V x = x) ∧
  (∀ (M : ModuleRingedComparison.internalModules R Z)
      (N : ModuleRingedComparison.internalModules S Z)
      (g : (Mod.extendScalars (coefficientMap a Z)).obj M ⟶ N),
    (ModuleRingedComparison.equivalence R Z).functor.map
        ((Mod.extendRestrictAdjunction (coefficientMap a Z)).homEquiv M N g) ≫
          r.hom.app N =
      b.ordinaryAdjunction.homEquiv _ _
        (o.inv.app M ≫ (ModuleRingedComparison.equivalence S Z).functor.map g)) ∧
  ∃ p : internalScalarExtension a Z ⋙
      (ModuleRingedComparison.derivedEquivalence S Z).functor ≅
    (ModuleRingedComparison.derivedEquivalence R Z).functor ⋙ b.derived,
  ∃ q : (Mod.comap (coefficientMap a Z)).mapDerivedCategory ⋙
      (ModuleRingedComparison.derivedEquivalence R Z).functor ≅
    (ModuleRingedComparison.derivedEquivalence S Z).functor ⋙
      SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
      (coefficientSectionScalarMap a Z),
  (q = Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap a Z))
      (ModuleRingedComparison.equivalence R Z).functor ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
    (Functor.mapDerivedCategoryCompIso (ModuleRingedComparison.equivalence S Z).functor
      (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
      (coefficientSectionScalarMap a Z))).symm) ∧
  (∀ (P : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
      (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
        (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z)
      ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
    (ModuleRingedComparison.derivedEquivalence S Z).functor.map
        (coefficientInternalScalarComplex a Z P) ≫
      (ModuleRingedComparison.equivalence S Z).functor.mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars (coefficientMap a Z)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) =
    p.hom.app (DerivedCategory.Q.obj P) ≫
      b.derived.map
        ((ModuleRingedComparison.equivalence R Z).functor.mapDerivedCategoryFactors.hom.app P) ≫
      SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
        b.counit (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P)) ∧
  (∀ (M : DerivedCategory (ModuleRingedComparison.internalModules R Z))
      (N : DerivedCategory (ModuleRingedComparison.internalModules S Z))
      (g : (internalScalarExtension a Z).obj M ⟶ N),
    (ModuleRingedComparison.derivedEquivalence R Z).functor.map
        ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Z)).homEquiv M N g) ≫
      q.hom.app N =
    b.adjunction.homEquiv _ _
      (p.inv.app M ≫ (ModuleRingedComparison.derivedEquivalence S Z).functor.map g)) ∧
  ∃ m : b.extension.Monoidal,
  (∀ (M N : ModuleRingedComparison.modules R Z) (V : Z.ProEtᵒᵖ)
      (s : (ModuleRingedComparison.ring S Z).obj.obj V)
      (x : M.val.obj V) (y : N.val.obj V),
    (m.toOplaxMonoidal.δ M N).val.app V
        (coefficientSectionScalarPure a Z b (M ⊗ N) V s
          (ModuleRingedComparison.sectionPureTensor R Z M N V x y)) =
      ModuleRingedComparison.sectionPureTensor S Z (b.extension.obj M) (b.extension.obj N) V
        (coefficientSectionScalarPure a Z b M V s x)
        (coefficientSectionScalarPure a Z b N V 1 y)) ∧
  ∃ t : ModuleRingedComparison.tensor R Z ⋙ b.derived ≅
      b.derived.prod b.derived ⋙ ModuleRingedComparison.tensor S Z,
  (∀ (P Q : CochainComplex (ModuleRingedComparison.modules R Z) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z) P →
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z) (R := ModuleRingedComparison.ring R Z) Q →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (P.X n)) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (Q.X n)) →
    b.derived.map ((ModuleRingedComparison.qTensor R Z).app (P, Q)) ≫
      SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
        b.counit ((ModuleRingedComparison.totalTensor R Z).obj (P, Q)) ≫
      DerivedCategory.Q.map (coefficientSectionScalarTotal a Z b m P Q) =
    t.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (ModuleRingedComparison.tensor S Z).map (Prod.mkHom
        (SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
          b.counit P)
        (SheafOfModules.scalarPairComplexComparison
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z) (S := ModuleRingedComparison.ring S Z)
        b.extension b.extension_additive b.derived
          b.counit Q)) ≫
      (ModuleRingedComparison.qTensor S Z).app
        ((b.extension.mapHomologicalComplex (.up ℤ)).obj P,
          (b.extension.mapHomologicalComplex (.up ℤ)).obj Q)) ∧
  ∀ M N : DerivedCategory (ModuleRingedComparison.internalModules R Z),
    (ModuleRingedComparison.derivedEquivalence S Z).functor.map
        (((internalScalarTensorComparison a Z).app M).app N) ≫
      (ModuleRingedComparison.tensorComparison S Z).hom.app
        ((internalScalarExtension a Z).obj M, (internalScalarExtension a Z).obj N) ≫
      (ModuleRingedComparison.tensor S Z).map (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
    p.hom.app (((derivedTensor R Z).obj M).obj N) ≫
      b.derived.map ((ModuleRingedComparison.tensorComparison R Z).hom.app (M, N)) ≫
      t.hom.app ((ModuleRingedComparison.derivedEquivalence R Z).functor.obj M,
        (ModuleRingedComparison.derivedEquivalence R Z).functor.obj N)

end AlgebraicGeometry.ProEtale.CondensedRing
