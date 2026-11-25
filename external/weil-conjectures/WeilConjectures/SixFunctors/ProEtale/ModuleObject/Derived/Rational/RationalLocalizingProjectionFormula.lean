/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperProjectionFormula
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Proper projection formula on rational localizing categories

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-pf-field,
sk-thm-sf-pf-field-localizing.md and its proof
(blueprint: proposition-projection-formula-rational-coefficients--2).

Membership of both endpoints and invertibility in the ambient category express
invertibility in the full localizing subcategory. The generators are exactly Dbc,
with finite constant scalar models; no derived completeness condition is imposed.
The five helpers below define the actual projection map on internal module objects,
including the unique representative-normalized tensor comparison. They belong to this
projection formula; the general ringed projection-mate dependency remains unchanged.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local instance 30000] instCategoryDerivedCategory CategoryTheory.Mod.instCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local instance 1]
  AlgebraicGeometry.ProEtale.CondensedRing.ProjectionMorphismData.category

-- Match the cached structures used by the published module-object projection interface.
attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.derivedTensorLeftDerivedCounit Functor.leftDerivedDerivedTensorCounit
  Functor.leftDerivedFunctorCounit Functor.leftDerivedTensorComparison
  leftDerivedUpperStarTensor derivedUpperStarLowerStarAdjunction
  Adjunction.rightAdjointProjectionMap
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private local instance rational_siteColimits (T : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  ⟨fun _ _ ↦ Sheaf.instHasColimitsOfShape⟩

private local instance rational_siteBigColimits (T : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasColimits _

private local instance rational_modulePreadditive (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    MonoidalPreadditive (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  inferInstance

private local instance rational_exactSequential (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    HasExactColimitsOfShape ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :=
  inferInstance

private local instance rational_tensorLeftSequential (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := inferInstance

private local instance rational_tensorRightSequential (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) := inferInstance

-- Cache proof-valued site-colimit assumptions used by the relative tensor structure.
private local instance rational_sheafCoequalizersShortcut (Z : Scheme.{u}) :
    HasCoequalizers (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

private local instance rational_sheafTensorLeftColimitsShortcut (Z : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance

private local instance rational_sheafTensorRightColimitsShortcut (Z : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) := inferInstance

-- Resolve the colimit obligations before matching expanded graded tensor expressions.
private local instance rational_moduleColimit (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {J : Type} [SmallCategory J] (D : J ⥤ Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R) :
    HasColimit D := inferInstance

private local instance rational_tensorLeftColimit (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R)
    {J : Type} [SmallCategory J] (D : J ⥤ Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R) :
    PreservesColimit D ((curriedTensor _).obj M) := inferInstance

private local instance rational_tensorRightColimit (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R)
    {J : Type} [SmallCategory J] (D : J ⥤ Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R) :
    PreservesColimit D ((curriedTensor _).flip.obj M) := inferInstance

attribute [local instance 1000000] rational_moduleColimit
  rational_tensorLeftColimit rational_tensorRightColimit

-- Cache the ambient existence properties used by every derived functor in the file.
attribute [local instance 50000] grothendieckModulesShortcut

attribute [local instance 50000] flatResolutionModulesShortcut

-- Give tensor-colimit inference a direct path in the internal module category.
attribute [local instance 50000] preservesColimitsTensorLeftShortcut

attribute [local instance 50000] preservesColimitsTensorRightShortcut

-- Cache the colimit compatibility proofs used repeatedly by total tensor products.
attribute [local instance 50000] hasTensorGradedShortcut

attribute [local instance 50000] hasGoodTensorLeftShortcut

attribute [local instance 50000] hasGoodTensorRightShortcut

attribute [local instance 50000] hasTensorFourShortcut

-- Share existence proofs for the total tensors of concrete complexes.
private local instance rational_cochainTensorShortcut (Z : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    HomologicalComplex.HasTensor A B := inferInstance

-- The derived tensor structure depends only on this proof-valued localization property.
private local instance rational_derivedMonoidalShortcut (Z : Scheme.{u}) :
    (DerivedCategory.Qh (C := Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso
        (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) (.up ℤ)) :=
  inferInstance

attribute [local instance 500000] rational_derivedMonoidalShortcut

-- Cache the functor-specific existence proof before elaborating derived pullbacks.
private local instance rational_upperStarKFlat {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (upperStar Λ p).PreservesKFlatQuasiIso := preservesKFlatQuasiIso_upperStar Λ p

attribute [local instance 50000] rational_upperStarKFlat upperStarAdditiveShortcut
  upperStarFiniteLimitsShortcut upperStarFiniteColimitsShortcut upperStarLeftAdjointShortcut

section ProjectionMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Reuse the already available pullback properties throughout these concrete constructions.
attribute [local instance] upperStarAdditiveShortcut

attribute [local instance] upperStarFiniteLimitsShortcut

attribute [local instance] upperStarFiniteColimitsShortcut

attribute [local instance] upperStarLeftAdjointShortcut

section AbstractComparison

variable {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : ∀ M N : C, (F.obj (M ⊗ N) ⟶ F.obj M ⊗ F.obj N) → Prop)

-- Cache the underlying obligations before the graded tensor aliases expand them.
private local instance genericSourceColimit {J : Type} [SmallCategory J] (V : J ⥤ C) :
    HasColimit V := inferInstance

private local instance genericSourceTensorLeftColimit (M : C)
    {J : Type} [SmallCategory J] (V : J ⥤ C) :
    PreservesColimit V ((curriedTensor C).obj M) := inferInstance

private local instance genericSourceTensorRightColimit (M : C)
    {J : Type} [SmallCategory J] (V : J ⥤ C) :
    PreservesColimit V ((curriedTensor C).flip.obj M) := inferInstance

attribute [local instance 1000000] genericSourceColimit
  genericSourceTensorLeftColimit genericSourceTensorRightColimit

private local instance genericColimit {J : Type} [SmallCategory J] (V : J ⥤ D) :
    HasColimit V := inferInstance

private local instance genericTensorLeftColimit (M : D)
    {J : Type} [SmallCategory J] (V : J ⥤ D) :
    PreservesColimit V ((curriedTensor D).obj M) := inferInstance

private local instance genericTensorRightColimit (M : D)
    {J : Type} [SmallCategory J] (V : J ⥤ D) :
    PreservesColimit V ((curriedTensor D).flip.obj M) := inferInstance

attribute [local instance 1000000] genericColimit
  genericTensorLeftColimit genericTensorRightColimit

private local instance genericSourceTensor (A B : GradedObject ℤ C) :
    A.HasTensor B := inferInstance
private local instance genericSourceGoodLeft (A B D : GradedObject ℤ C) :
    GradedObject.HasGoodTensor₁₂Tensor A B D := inferInstance
private local instance genericSourceGoodRight (A B D : GradedObject ℤ C) :
    GradedObject.HasGoodTensorTensor₂₃ A B D := inferInstance
private local instance genericSourceFour (A B D E : GradedObject ℤ C) :
    GradedObject.HasTensor₄ObjExt A B D E := inferInstance
private local instance genericSourceCochainTensor (A B : CochainComplex C ℤ) :
    HomologicalComplex.HasTensor A B := inferInstance

private local instance genericTensor (A B : GradedObject ℤ D) : A.HasTensor B := inferInstance
private local instance genericGoodLeft (A B C : GradedObject ℤ D) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance
private local instance genericGoodRight (A B C : GradedObject ℤ D) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance
private local instance genericFour (A B C E : GradedObject ℤ D) :
    GradedObject.HasTensor₄ObjExt A B C E := inferInstance
private local instance genericCochainTensor (A B : CochainComplex D ℤ) :
    HomologicalComplex.HasTensor A B := inferInstance

/-- The representative normalization of a derived tensor comparison for an additive
monoidal functor. Source: Stacks Tags 06YU, 07A4 and 0B56
(blueprint: def-sfb-proetale-rational-localizing-projection-helpers). -/
@[irreducible, no_expose]
def tensorRepresentativeFormula
    (μ : Functor.leftDerivedDerivedTensor F ⟶ Functor.derivedTensorLeftDerived F) : Prop :=
  ∀ K P : CochainComplex C ℤ,
    letI : HomologicalComplex.HasTensor K P := inferInstance
    letI : HomologicalComplex.HasTensor
        ((F.mapHomologicalComplex (.up ℤ)).obj K)
        ((F.mapHomologicalComplex (.up ℤ)).obj P) := inferInstance
    ∃ q : (F.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj K P) ⟶
        HomologicalComplex.tensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (i j n : ℤ) (h : i + j = n),
        ∃ b : F.obj (K.X i ⊗ P.X j) ⟶ F.obj (K.X i) ⊗ F.obj (P.X j),
          G (K.X i) (P.X j) b ∧
          F.map (HomologicalComplex.ιTensorObj K P i j n h) ≫ q.f n =
            b ≫ HomologicalComplex.ιTensorObj
              ((F.mapHomologicalComplex (.up ℤ)).obj K)
              ((F.mapHomologicalComplex (.up ℤ)).obj P) i j n h) ∧
      (μ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj P) ≫
          ((Functor.derivedTensorLeftDerivedCounit F).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        ((Functor.leftDerivedDerivedTensorCounit F).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj K)).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫ DerivedCategory.Q.map q

end AbstractComparison

/-- The generator formula for the ordinary pullback tensor comparison. The maps into
extension of scalars are the actual extension units; `tensorObjπ` is the relative
balanced coequalizer projection. Thus this is the map sending a pulled-back pure tensor
to the tensor of the pulled-back factors, not an arbitrary tensor isomorphism.
Source: Stacks Tag 0B56, canonical tensor comparison
(blueprint: proposition-projection-formula-rational-coefficients--2). -/
def ModuleObjectTensorGeneratorFormula
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (b : (upperStar Λ f).obj (M ⊗ N) ⟶
      (upperStar Λ f).obj M ⊗ (upperStar Λ f).obj N) : Prop :=
  (ProEtale.upperStar Ab.{u + 1} f).map (Mod.tensorObjπ M N) ≫
      Mod.extendUnitHom (condensedPullbackHom Λ f)
        (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj (M ⊗ N)) ≫ b.hom =
    Functor.OplaxMonoidal.δ (ProEtale.upperStar Ab.{u + 1} f) M.X N.X ≫
      (Mod.extendUnitHom (condensedPullbackHom Λ f)
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj M) ⊗ₘ
        Mod.extendUnitHom (condensedPullbackHom Λ f)
          (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj N)) ≫
      Mod.tensorObjπ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)

/-- Characterization of the derived tensor comparison by its signed direct-sum total
map and the derived-functor counits. Each component of the total map is specified on every
summand by the ordinary balanced tensor formula. The condition is imposed on all complexes,
so it retains the unbounded comparison, with no boundedness or completeness condition.
Source: Stacks Tags 06YU, 07A4 and 0B56
(blueprint: proposition-projection-formula-rational-coefficients--2). -/
def ModuleObjectDerivedTensorFormula
    (μ : Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f)) : Prop :=
  tensorRepresentativeFormula (upperStar Λ f) (ModuleObjectTensorGeneratorFormula Λ f) μ

private theorem pullback_preservesFlat : (upperStar Λ f).PreservesFlat :=
  upperStar_preservesFlat Λ f

private theorem extend_delta_normalized
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [HasCoequalizers C]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (M N : Mod C R) :
    Mod.tensorObjπ M N ≫ Mod.extendUnitHom φ (M ⊗ N) ≫
        (Functor.OplaxMonoidal.δ (Mod.extendScalars φ) M N).hom =
      (Mod.extendUnitHom φ M ⊗ₘ Mod.extendUnitHom φ N) ≫
        Mod.tensorObjπ ((Mod.extendScalars φ).obj M)
          ((Mod.extendScalars φ).obj N) := by
  rw [Functor.Monoidal.transport_δ]
  simp only [Iso.symm_inv, Iso.symm_hom, Mod.comp_hom']
  rw [Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app_assoc]
  change Mod.tensorObjπ M N ≫ (Mod.comapTensorIso (asIso φ).inv M N).inv.hom ≫ _ = _
  have hπ : Mod.tensorObjπ M N ≫ (Mod.comapTensorIso (asIso φ).inv M N).inv.hom =
      Mod.tensorObjπ ((Mod.comap (asIso φ).inv).obj M)
        ((Mod.comap (asIso φ).inv).obj N) := by
    apply (cancel_mono (Mod.comapTensorIso (asIso φ).inv M N).hom.hom).mp
    rw [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id]
    change Mod.tensorObjπ M N ≫ 𝟙 _ = _
    rw [Category.comp_id, Mod.tensorπ_comapTensorIso_hom_hom]
  erw [reassoc_of% hπ]
  have h (A : Mod C R) : ((Mod.extendScalarsIsoComapInv φ).inv.app A).hom =
      Mod.extendUnitHom φ A := by
    apply (cancel_mono ((Mod.extendScalarsIsoComapInv φ).hom.app A).hom).mp
    rw [← Mod.comp_hom', Iso.inv_hom_id_app]
    exact (Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app φ A).symm
  rw [MonoidalCategory.tensorHom_def]
  simp only [Mod.comp_hom']
  erw [Mod.tensorObjπ_whiskerRight_assoc, Mod.tensorObjπ_whiskerLeft]
  rw [h, h]
  erw [← tensorHom_def_assoc]

private theorem map_extend_delta_normalized
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] [HasCoequalizers C]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    [MonoidalCategory D] [BraidedCategory D] [HasCoequalizers D]
    [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
    [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
    (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
    {R : C} [MonObj R] [IsCommMonObj R]
    {S : D} [MonObj S] [IsCommMonObj S]
    (φ : F.obj R ⟶ S) [IsMonHom φ] [IsIso φ] (M N : Mod C R) :
    let T := F.mapMod R
    let H := T ⋙ Mod.extendScalars φ
    F.map (Mod.tensorObjπ M N) ≫ Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
        (Functor.OplaxMonoidal.δ H M N).hom =
      Functor.OplaxMonoidal.δ F M.X N.X ≫
        (Mod.extendUnitHom φ (T.obj M) ⊗ₘ Mod.extendUnitHom φ (T.obj N)) ≫
        Mod.tensorObjπ (H.obj M) (H.obj N) := by
  let T := F.mapMod R
  dsimp only
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction φ).unit.naturality
      (Functor.OplaxMonoidal.δ T M N))
  simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
    Mod.extendRestrictAdjunction_unit_app_hom] at hn
  change F.map (Mod.tensorObjπ M N) ≫ Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
    (((Mod.extendScalars φ).map (Functor.OplaxMonoidal.δ T M N)) ≫
      Functor.OplaxMonoidal.δ (Mod.extendScalars φ) (T.obj M) (T.obj N)).hom = _
  rw [Mod.comp_hom', ← Category.assoc, ← Category.assoc]
  change (Functor.OplaxMonoidal.δ T M N).hom ≫
    Mod.extendUnitHom φ (T.obj M ⊗ T.obj N) =
    Mod.extendUnitHom φ (T.obj (M ⊗ N)) ≫
    ((Mod.extendScalars φ).map (Functor.OplaxMonoidal.δ T M N)).hom at hn
  rw [Category.assoc (F.map (Mod.tensorObjπ M N)), ← hn]
  have ht : F.map (Mod.tensorObjπ M N) ≫
      (Functor.OplaxMonoidal.δ T M N).hom =
        Functor.OplaxMonoidal.δ F M.X N.X ≫ Mod.tensorObjπ (T.obj M) (T.obj N) := by
    apply (cancel_mono (F.mapModTensorIso M N).hom.hom).mp
    change (F.map (Mod.tensorObjπ M N) ≫ (F.mapModTensorIso M N).inv.hom) ≫ _ = _
    have hi := congrArg Mod.Hom.hom (F.mapModTensorIso M N).inv_hom_id
    simp only [Mod.comp_hom', Mod.id_hom'] at hi
    rw [Category.assoc, hi]
    erw [Category.comp_id]
    erw [Category.assoc, Functor.tensorπ_mapModTensorIso_hom_hom,
      Functor.Monoidal.δ_μ_assoc]
  rw [← Category.assoc (F.map (Mod.tensorObjπ M N)), ht]
  erw [Category.assoc, Category.assoc,
    extend_delta_normalized φ (T.obj M) (T.obj N)]
  rfl

private theorem tensor_generator_delta
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ModuleObjectTensorGeneratorFormula Λ f M N
      (Functor.OplaxMonoidal.δ (upperStar Λ f) M N) :=
  map_extend_delta_normalized (ProEtale.upperStar Ab.{u + 1} f)
    (condensedPullbackHom Λ f) M N

section AbstractComparison

variable {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : ∀ M N : C, (F.obj (M ⊗ N) ⟶ F.obj M ⊗ F.obj N) → Prop)

attribute [local instance] genericTensor genericGoodLeft genericGoodRight genericFour
  genericCochainTensor
attribute [local instance 1000000] genericColimit
  genericTensorLeftColimit genericTensorRightColimit genericSourceColimit
  genericSourceTensorLeftColimit genericSourceTensorRightColimit
attribute [local instance] genericSourceTensor genericSourceGoodLeft
  genericSourceGoodRight genericSourceFour genericSourceCochainTensor

private theorem abstractTensorComparison_formula
    (hδ : ∀ M N, G M N (Functor.OplaxMonoidal.δ F M N)) :
    tensorRepresentativeFormula F G F.leftDerivedTensorComparison := by
  unfold tensorRepresentativeFormula
  intro K P
  let q := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app P
  refine ⟨q, ?_, ?_⟩
  · intro i j n h
    exact ⟨Functor.OplaxMonoidal.δ F (K.X i) (P.X j), hδ _ _,
      HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
        (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) K P i j n h⟩
  · exact F.leftDerivedTensorComparison_app_app_comp_counit
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

end AbstractComparison

/-- The unique representative-normalized tensor comparison. Its data are determined by
`ModuleObjectDerivedTensorFormula`, not by a mere existence of an isomorphism.
Source: Stacks Tag 0B56 (blueprint: proposition-projection-formula-rational-coefficients--2). -/
noncomputable def moduleObjectDerivedTensorComparison :
    Functor.leftDerivedDerivedTensor (upperStar Λ f) ⟶
      Functor.derivedTensorLeftDerived (upperStar Λ f) :=
  leftDerivedUpperStarTensor Λ f

/-- The explicitly constructed comparison has the original total-complex normalization.
Source: Stacks Tags 07A4 and 0B56
(blueprint: def-sfb-proetale-rational-localizing-projection-helpers).
Proof: identify the adopted comparison with the generic left-derived tensor comparison;
its counit equation and its maps on every total-complex summand are the generic formulas.
The previously proved generator formula supplies the ordinary normalization. -/
theorem moduleObjectDerivedTensorComparison_normalized :
    ModuleObjectDerivedTensorFormula Λ f (moduleObjectDerivedTensorComparison Λ f) ∧
      IsIso (moduleObjectDerivedTensorComparison Λ f) := by
  constructor
  · let := pullback_preservesFlat Λ f
    unfold moduleObjectDerivedTensorComparison
    rw [leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f]
    exact abstractTensorComparison_formula (upperStar Λ f)
      (ModuleObjectTensorGeneratorFormula Λ f) (tensor_generator_delta Λ f)
  · unfold moduleObjectDerivedTensorComparison
    infer_instance

/-- The actual counit mate `(Rf_* A) ⊗ B ⟶ Rf_*(A ⊗ Lf^* B)` on internal module objects.
The existing derived adjunction and the normalized comparison determine this map.
Source: Stacks Tag 0B56 (blueprint: proposition-projection-formula-rational-coefficients--2). -/
noncomputable def moduleObjectProjectionMate
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (lowerStar Λ f).rightDerivedFunctor.obj A ⊗ B ⟶
      (lowerStar Λ f).rightDerivedFunctor.obj
        (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ f)
            (upperStarAdditiveShortcut Λ f)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ f)).obj B) :=
  (((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (moduleObjectDerivedTensorComparison Λ f)).app A).app B

attribute [local irreducible] moduleObjectProjectionMate moduleObjectProjectionData
  moduleObjectDerivedTensorComparison moduleObjectProjectionMap projectionMap derivedTensor

private theorem normalizedMate_eq_published
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    moduleObjectProjectionMate Λ f A B = ((projectionMap Λ f).app A).app B := by
  unfold moduleObjectProjectionMate projectionMap moduleObjectDerivedTensorComparison
  rfl

end ProjectionMap

-- The concrete normalization is complete; keep the published tensor API compact below.
attribute [local irreducible] CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Mod.monoidalCategory DerivedCategory.Qh upperStar

private theorem projection_localizing_of_interfaces
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hbcX : constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X))
    (hbcY : constantModelBoundedConstructible Λ Y = boundedConstructible (condensedRingObj Λ Y))
    (hctfX : (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ X)
    (hctfY : (constantModelBoundedConstructible Λ Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible Λ Y)
    (hp : ProperLocalizingHypotheses Λ p)
    (hpull : ∀ K, constantModelBoundedConstructible Λ Y K →
      constantModelBoundedConstructible Λ X ((@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ p)
            (upperStarAdditiveShortcut Λ p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ p)).obj K))
    (htensor : ∀ K M, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X M → constantModelBoundedConstructible Λ X (K ⊗ M))
    (htensorY : ∀ K M, constantModelBoundedConstructible Λ Y K →
      constantModelBoundedConstructible Λ Y M → constantModelBoundedConstructible Λ Y (K ⊗ M))
    (hPF : ∀ K M, boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ Y) M →
      IsIso (((projectionMap Λ p).app K).app M))
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hA : localizingClosure (constantModelBoundedConstructible Λ X) A)
    (hB : localizingClosure (constantModelBoundedConstructible Λ Y) B) :
    localizingClosure (constantModelBoundedConstructible Λ Y)
        ((lowerStar Λ p).rightDerivedFunctor.obj A ⊗ B) ∧
      localizingClosure (constantModelBoundedConstructible Λ Y)
        ((lowerStar Λ p).rightDerivedFunctor.obj
          (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ p)
            (upperStarAdditiveShortcut Λ p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ p)).obj B)) ∧
      IsIso (moduleObjectProjectionMate Λ p A B) := by
  have heqX : localizingBoundedConstructible Λ X =
      localizingClosure (constantModelBoundedConstructible Λ X) := by
    change (boundedConstructible (condensedRingObj Λ X)).localizingClosure = _
    rw [← hbcX]
    apply le_antisymm
    · let := (isLocalizingSubcategory_iff_isLocalizing _).1
        (localizingClosure_exists Λ X (constantModelBoundedConstructible Λ X)).2.2.2.1
      exact ObjectProperty.localizingClosure_le (fun K hK P _ hSP ↦ hSP K hK)
    · intro K hK
      exact hK _ ((isLocalizingSubcategory_iff_isLocalizing _).2 inferInstance)
        (ObjectProperty.le_localizingClosure _)
  have heqY : localizingBoundedConstructible Λ Y =
      localizingClosure (constantModelBoundedConstructible Λ Y) := by
    change (boundedConstructible (condensedRingObj Λ Y)).localizingClosure = _
    rw [← hbcY]
    apply le_antisymm
    · let := (isLocalizingSubcategory_iff_isLocalizing _).1
        (localizingClosure_exists Λ Y (constantModelBoundedConstructible Λ Y)).2.2.2.1
      exact ObjectProperty.localizingClosure_le (fun K hK P _ hSP ↦ hSP K hK)
    · intro K hK
      exact hK _ ((isLocalizingSubcategory_iff_isLocalizing _).2 inferInstance)
        (ObjectProperty.le_localizingClosure _)
  have hpush : ∀ K, localizingBoundedConstructible Λ X K →
      localizingBoundedConstructible Λ Y ((lowerStar Λ p).rightDerivedFunctor.obj K) := by
    intro K hK
    rw [heqX] at hK
    rw [heqY]
    have h := localizingClosure_map
      (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      (constantModelBoundedConstructible Λ Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      (lowerStar Λ p).rightDerivedFunctor (fun K hK ↦ hp.1 ⟨K, hK⟩)
      (preservesColimit_of_properLocalizingHypotheses Λ p hp)
    rw [hctfX, hctfY] at h
    exact h K hK
  have hsum : (lowerStar Λ p).rightDerivedFunctor.PreservesCoproductsOn.{u + 1}
      (localizingBoundedConstructible Λ X) := by
    intro I G c hc hG
    let J := ULift.{u + 2} I
    let e : Discrete J ≌ Discrete I := Discrete.equivalence Equiv.ulift
    let H := (localizingClosureProEtale Λ X).lift (e.functor ⋙ G) (fun i ↦ by
      change localizingClosure (_ ⊓ _) _
      rw [hctfX, ← heqX]
      exact hG (e.functor.obj i))
    have : PreservesColimit (e.functor ⋙ G) (lowerStar Λ p).rightDerivedFunctor := hp.2 J H
    refine ⟨IsColimit.ofWhiskerEquivalence e ?_⟩
    exact IsColimit.ofIsoColimit
      (isColimitOfPreserves (lowerStar Λ p).rightDerivedFunctor (hc.whiskerEquivalence e))
      (Functor.mapCoconeWhisker _)
  have hpull' : ∀ K, boundedConstructible (condensedRingObj Λ Y) K →
      boundedConstructible (condensedRingObj Λ X) ((@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ p)
            (upperStarAdditiveShortcut Λ p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ p)).obj K) := by
    rw [← hbcX, ← hbcY]
    exact hpull
  have htensor' : ∀ K M, boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ X) M →
      boundedConstructible (condensedRingObj Λ X) (K ⊗ M) := by
    rw [← hbcX]
    exact htensor
  have hA' := (congrFun heqX A).mpr hA
  have hB' := (congrFun heqY B).mpr hB
  have hi := isIso_projectionMap_of_localizingBoundedConstructible Λ p
    hpush hsum hpull' htensor' hPF hA' hB'
  have htensorY' : ∀ K M, boundedConstructible (condensedRingObj Λ Y) K →
      boundedConstructible (condensedRingObj Λ Y) M →
      boundedConstructible (condensedRingObj Λ Y) (K ⊗ M) := by
    rw [← hbcY]
    exact htensorY
  refine ⟨?_, ?_, ?_⟩
  · exact (congrFun heqY _).mp
      (localizingBoundedConstructible_tensor Λ htensorY' (hpush A hA') hB')
  · exact (congrFun heqY _).mp (hpush _
      (localizingBoundedConstructible_tensor Λ htensor' hA'
        (localizingBoundedConstructible_leftDerivedUpperStar Λ p hpull' hB')))
  · rwa [normalizedMate_eq_published]

-- Realize an arbitrary universe-sized finite coefficient field in the fixed closure.
-- Source: the embedding and spectral-norm argument of normed_coefficient_realization
-- (Bhatt--Scholze, Definition 6.8.1 and Remark 6.8.15), across coefficient universes.
-- The two presentations use exactly the same continuous-function sections.
private theorem finite_coefficient_iso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj E) ≅
        Mon.mk (Profinite.continuousMapRingObj F)) := by
  obtain ⟨F, ⟨σ⟩⟩ : ∃ F : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      Nonempty (E ≃ₐ[ℚ_[ℓ]] F) := by
    let i : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
    exact ⟨i.fieldRange, ⟨i.equivFieldRange⟩⟩
  have hfin : FiniteDimensional ℚ_[ℓ] F := σ.toLinearEquiv.finiteDimensional
  let v : AbsoluteValue E ℝ :=
    { toFun := fun x ↦ ‖σ x‖
      map_mul' := fun x y ↦ by simp only [map_mul, norm_mul]
      nonneg' := fun _ ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero]
      add_le' := fun x y ↦ by simpa only [map_add] using norm_add_le (σ x) (σ y) }
  have hn (x : E) : ‖σ x‖ = ‖x‖ := by
    exact (spectralNorm_unique_field_norm_ext (f := v)
      (fun a ↦ by
        change ‖σ (algebraMap ℚ_[ℓ] E a)‖ = ‖a‖
        rw [σ.commutes]
        exact PadicAlgCl.norm_extends ℓ a) x).trans
      (spectralNorm_unique_field_norm_ext (f := NormedField.toAbsoluteValue E)
        (norm_algebraMap' E) x).symm
  have hσ : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hn
  have hσi : Isometry σ.symm := by
    intro x y
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm x) (σ.symm y)).symm
  let e : Profinite.continuousCoefficientRingSheaf E ≅
      Profinite.continuousMapRingSheaf.{u} F :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((σ.toRingHom.compLeftContinuous S.unop hσ.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((σ.symm.toRingHom.compLeftContinuous S.unop hσi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact σ.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact σ.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso e
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ e.hom
  exact ⟨⟨F, hfin⟩, ⟨Mon.mkIso' ea⟩⟩

/-- Proper projection formula on Loc(Dbc) for a finite extension E of the ell-adic field.
Source: blueprint main-20261015, sk-thm-sf-pf-field-localizing, both paragraphs
(blueprint: proposition-projection-formula-rational-coefficients--2).

Proof:
1. The standing separated finite-type schemes are qcqs. By
   det-def-localizing-closure-ctf-equals-bc the rational Dctf and Dbc categories and their
   localizing closures coincide.
2. Apply proposition-proper-base-change-localizing-categories--1 and
proposition-proper-direct-image-extension-zero--1.
   Both restricted functors are exact and preserve sums. Tensor closure from
   proposition-projection-formula-rational-coefficients--1 puts both endpoints in the target
   localizing category.
3. The closed tensor structure of sk-def-sfb-derived-tensor-hom makes tensor preserve sums;
   its exactness follows from lem-weil-pbc-ringed-projection-mate-exact.
4. By prose-03-02 and lemma-inverse-image-coefficient-sheaves, module pullback is
   the exact inverse image, hence its total left derived functor is p*.
5. The projection map is the counit mate of the canonical tensor comparison. Use
   lem-weil-pbc-ringed-projection-mate-exact for its naturality and tensor shift compatibility.
6. The canonical adjoint shifts of lem-weil-pbc-adjunction-shift-compatibility-unique make
   the counit commute with shifts. Apply lem-sf-triangulated-right-adjoint for exactness of R.
7. These counit and comparison shift equations make the canonical mate commute with shifts
   in each variable and give the connecting square on distinguished triangles.
8. proposition-proper-direct-image-constructible-complexes gives invertibility for bounded
constructible A,B.
9. Fix bounded B and apply lemma-checking-isomorphisms-constructible-complexes--1 to the two exact
sum-preserving functors
   of A, giving invertibility for arbitrary A in Loc(Dbc).
10. Fix this arbitrary A and apply the same determination lemma in B. Since the localizing
    category is full and both endpoints belong to it, this is invertibility there.
-/
theorem isIso_projectionMate_localizing_finiteExtension
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.continuousCoefficientRingObj E) Y)
        ((lowerStar (Profinite.continuousCoefficientRingObj E) p).rightDerivedFunctor.obj
          (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (hasGoodTensorLeftShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (hasGoodTensorRightShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (upperStar (Profinite.continuousCoefficientRingObj E) p)
            (upperStarAdditiveShortcut (Profinite.continuousCoefficientRingObj E) p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut
                (Profinite.continuousCoefficientRingObj E) Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut
                (Profinite.continuousCoefficientRingObj E) Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut (Profinite.continuousCoefficientRingObj E) Y)
            (projectionModuleHasDerived (Profinite.continuousCoefficientRingObj E) Y)
            (projectionModuleHasDerived (Profinite.continuousCoefficientRingObj E) X)
            (preservesKFlatQuasiIso_upperStar
              (Profinite.continuousCoefficientRingObj E) p)).obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.continuousCoefficientRingObj E) p A B) := by
  let Λ := Profinite.continuousCoefficientRingObj E
  obtain ⟨F, ⟨e⟩⟩ := finite_coefficient_iso ℓ E
  let Λ' := Profinite.continuousMapRingObj.{u} F
  have hφ : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have hψ : IsIso e.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.hom))
  have hbc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) := by
    have heq :=
      constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType k ℓ F T
    funext K
    apply propext
    exact (constantModel_derived_comap_iff e.inv.hom T K).symm.trans
      ((congrFun heq _).to_iff.trans
        (NormedCoefficientRealization.bounded_comap_iff (coefficientMap e.inv.hom T) K))
  have hctf (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      (constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T := by
    have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
    have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated (T ↘ Spec (.of k))
    exact (localizingClosure_ctf_equals_bc ℓ T Λ
      (Or.inr (Or.inr (Or.inl ⟨F, Or.inr ⟨e⟩⟩)))).1.2.2.1
  have hp := properHypotheses_coefficientIso e p
    (proper_image_localizing_proper_coefficients ℓ F (ZMod ℓ)
      ⟨1, by simp⟩ (Mon.mk Λ')
      (by exact .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _) k p)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hpull : ∀ K, constantModelBoundedConstructible Λ Y K →
      constantModelBoundedConstructible Λ X ((@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ p)
            (upperStarAdditiveShortcut Λ p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ p)).obj K) :=
    pullback_bounded_constructible Λ p (pullback_constructible Λ p)
  have htensor (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      ∀ K M, constantModelBoundedConstructible Λ T K →
        constantModelBoundedConstructible Λ T M →
        constantModelBoundedConstructible Λ T (K ⊗ M) := by
    intro K M hK hM
    simpa only [derivedTensor, curriedTensor_obj_obj] using
      (constantModelBoundedConstructible_derivedTensor ℓ (ringChar k)
        Fact.out (T ↘ Spec (.of k)) Λ (Or.inl ⟨F, ⟨e⟩⟩)).1 K M hK hM
  apply projection_localizing_of_interfaces Λ p (hbc X) (hbc Y) (hctf X) (hctf Y)
    hp hpull (htensor X) (htensor Y) ?_ A B hA hB
  intro K M hK hM
  have : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have : LocallyOfFiniteType (Y.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
  have : QuasiCompact (Y.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  have : IsSeparated (Y.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  have : IsProper (p.asOver (Spec (.of k))).left := inferInstanceAs (IsProper p)
  apply (canonical_projection_isIso Λ p K M).mp
  apply projection_isIso_of_coefficientIso e.hom.hom ℓ k (p.asOver (Spec (.of k))) K M
  exact isIso_properProjectionMap_boundedConstructible_rational ℓ
    (p.asOver (Spec (.of k))) (Mon.mk Λ') (Or.inl ⟨F, rfl⟩) _ _
    (bounded_scalar e X K hK) (bounded_scalar e Y M hM)

section QbarInstances

variable (ℓ : ℕ) [Fact ℓ.Prime]

private local instance qbarGrothendieck (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)) :=
  grothendieckModulesShortcut _ T

private local instance qbarFlatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)) :=
  flatResolutionModulesShortcut _ T

private local instance qbarFour (T : Scheme.{u})
    (A B C D : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T))) :
    GradedObject.HasTensor₄ObjExt A B C D := hasTensorFourShortcut _ T A B C D

end QbarInstances

/-- Proper projection formula on Loc(Dbc) for finite-subextension-valued condensed Qlbar.
Source: blueprint main-20261015, sk-thm-sf-pf-field-localizing, both paragraphs
(blueprint: proposition-projection-formula-rational-coefficients--2).

Proof:
1. Use the standing qcqs hypotheses and det-def-localizing-closure-ctf-equals-bc to identify
   Dctf, Dbc and their localizing closures for Qlbar.
2. proposition-proper-base-change-localizing-categories--1 and
proposition-proper-direct-image-extension-zero--1 restrict
   p* and Rp* to exact sum-preserving functors;
   proposition-projection-formula-rational-coefficients--1 gives membership of both endpoints in the
   target localizing category.
3. The closed structure sk-def-sfb-derived-tensor-hom gives tensor preservation of sums;
   lem-weil-pbc-ringed-projection-mate-exact gives exactness in both variables.
4. prose-03-02 and lemma-inverse-image-coefficient-sheaves identify Lp* with p*.
5. Use the normalized canonical tensor comparison and its counit mate as supplied by
   lem-weil-pbc-ringed-projection-mate-exact, natural in both variables.
6. lem-weil-pbc-adjunction-shift-compatibility-unique gives the counit-compatible adjoint
   shifts, and lem-sf-triangulated-right-adjoint supplies exactness of Rp* for these shifts.
7. The comparison and counit shift identities make the mate compatible with shifts in both
   variables and give its connecting square on distinguished triangles.
8. proposition-proper-direct-image-constructible-complexes gives invertibility on bounded
constructible A,B.
9. For bounded B, apply lemma-checking-isomorphisms-constructible-complexes--1 in A to obtain all A
in Loc(Dbc).
10. Fix arbitrary A and apply determination in B, giving all B in Loc(Dbc). Fullness and
    the membership of both endpoints give the asserted isomorphism in Loc(Dbc).
-/
theorem isIso_projectionMate_localizing_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)))
    (hA : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) A)
    (hB : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y) B) :
    CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj A ⊗ B) ∧
      CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) Y)
        ((lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
          (A ⊗ (@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (hasGoodTensorLeftShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (hasGoodTensorRightShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (upperStar (Profinite.padicAlgClRingObj ℓ) p)
            (upperStarAdditiveShortcut (Profinite.padicAlgClRingObj ℓ) p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut
                (Profinite.padicAlgClRingObj ℓ) Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut
                (Profinite.padicAlgClRingObj ℓ) Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut (Profinite.padicAlgClRingObj ℓ) Y)
            (projectionModuleHasDerived (Profinite.padicAlgClRingObj ℓ) Y)
            (projectionModuleHasDerived (Profinite.padicAlgClRingObj ℓ) X)
            (preservesKFlatQuasiIso_upperStar
              (Profinite.padicAlgClRingObj ℓ) p)).obj B)) ∧
      IsIso (moduleObjectProjectionMate (Profinite.padicAlgClRingObj ℓ) p A B)  := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  have hbc (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) :=
    constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType k ℓ T
  have hctf (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      (constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T := by
    have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
    have : QuasiSeparatedSpace T := quasiSeparatedSpace_of_quasiSeparated (T ↘ Spec (.of k))
    exact (localizingClosure_ctf_equals_bc ℓ T Λ
      (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
  let F₀ : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  have hp := proper_image_localizing_proper_coefficients ℓ F₀ (ZMod ℓ)
    ⟨1, by simp⟩ (Mon.mk Λ)
      (by exact .tail _ <| .tail _ <| .tail _ <| .tail _ <| .tail _ <| .head _) k p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have hpull : ∀ K, constantModelBoundedConstructible Λ Y K →
      constantModelBoundedConstructible Λ X ((@Functor.leftDerivedFunctor _ _ _ _ _ _ _ _ _
            (hasTensorFourShortcut Λ Y)
            (hasGoodTensorLeftShortcut Λ Y)
            (hasGoodTensorRightShortcut Λ Y)
            (upperStar Λ p)
            (upperStarAdditiveShortcut Λ p)
            inferInstance inferInstance
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorLeftShortcut Λ Y M) ℤ inferInstance)
            (fun M ↦ @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _
              (preservesColimitsTensorRightShortcut Λ Y M) ℤ inferInstance)
            (flatResolutionModulesShortcut Λ Y)
            (projectionModuleHasDerived Λ Y)
            (projectionModuleHasDerived Λ X)
            (preservesKFlatQuasiIso_upperStar Λ p)).obj K) :=
    pullback_bounded_constructible Λ p (pullback_constructible Λ p)
  have htensor (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] :
      ∀ K M, constantModelBoundedConstructible Λ T K →
        constantModelBoundedConstructible Λ T M →
        constantModelBoundedConstructible Λ T (K ⊗ M) := by
    intro K M hK hM
    simpa only [derivedTensor, curriedTensor_obj_obj] using
      (constantModelBoundedConstructible_derivedTensor ℓ (ringChar k)
      Fact.out (T ↘ Spec (.of k)) Λ (Or.inr ⟨Iso.refl _⟩)).1 K M hK hM
  apply projection_localizing_of_interfaces Λ p (hbc X) (hbc Y) (hctf X) (hctf Y)
    hp hpull (htensor X) (htensor Y) ?_ A B hA hB
  intro K M hK hM
  have : LocallyOfFiniteType (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated (X.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have : LocallyOfFiniteType (Y.asOver (Spec (.of k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
  have : QuasiCompact (Y.asOver (Spec (.of k))).hom :=
    inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  have : IsSeparated (Y.asOver (Spec (.of k))).hom :=
    inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  have : IsProper (p.asOver (Spec (.of k))).left := inferInstanceAs (IsProper p)
  exact (canonical_projection_isIso Λ p K M).mp
    (isIso_properProjectionMap_boundedConstructible_rational ℓ
      (p.asOver (Spec (.of k))) (Mon.mk Λ) (Or.inr rfl) K M hK hM)

end AlgebraicGeometry.ProEtale.CondensedRing
