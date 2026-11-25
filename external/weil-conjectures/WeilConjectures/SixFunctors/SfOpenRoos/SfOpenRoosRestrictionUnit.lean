/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosExtensionComparison
public import WeilConjectures.SixFunctors.Sf.SfClopenCoefficientComparison
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import all WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus

/-! # Restriction of the normalized open Roos comparison through its unit

Source: Stacks Project, proetale.tex, Tag 09BP, lemma-j-shriek-limits;
sites-modules.tex, Tags 04IX and 03DJ; sites-cohomology.tex, Tag 0941
(blueprint: lem-sf-open-roos-restriction-unit).

The open is presented by its pro-etale slice, with the actual completed ring,
extension, restriction and normalized adjunction from the recorded dependencies.
Index n is positive level n+1. Both comparison directions share their signed
Roos models, coordinates and normalized derived-limit identifications.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe a b c d wA wB t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.SfOpenRoos

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

/-- Localization of the actual exact adjunction, allowing independent localization sizes.
Source: Stacks 015F, 03DI (blueprint: lem-sf-open-roos-restriction-unit). -/
def restrictionUnitDerivedAdjunction
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : J ⊣ G) :
    J.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (J.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q J.mapDerivedCategory := ⟨J.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    J.mapDerivedCategory G.mapDerivedCategory

/-- Localize the actual termwise tower adjunction with its pointwise exactness data.
Source: Stacks 015F, 03DI (blueprint: lem-sf-open-roos-restriction-unit). -/
def restrictionUnitTowerDerivedAdjunction
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]
    {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : J ⊣ G) :
    (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance
        (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)) ⊣
    (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
        (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)) :=
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  letI : PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  restrictionUnitDerivedAdjunction (adj.whiskerRight ℕᵒᵖ)

attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] restrictionUnitDerivedAdjunction
attribute [local irreducible] restrictionUnitTowerDerivedAdjunction

-- Keep chosen limits abstract while checking the large comparison assertion.
attribute [local irreducible] limit limit.cone BinaryBiproduct.bicone

section Assertion
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

/-- Expanded normalization and compatibility laws of this node. These are propositions
about shared comparison data; no arbitrary derived map replaces either comparison.
The signed coordinates are the canonical shifted-cone coordinates (u,-v).
Source: Stacks 09BP and 0941 (blueprint: lem-sf-open-roos-restriction-unit). -/
def RestrictionUnitAssertions (J : A ⥤ B) (G : B ⥤ A)
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : J ⊣ G)
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB) : Prop :=
    ∃ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (chiB : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psiJ : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦
          (M).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op n))))
      (kappaJ : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
      (lambdaJ : LA ⋙ J.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _
        _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance (⟨fun _ _ _ ↦
          inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB)
      (psiG : ∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        (G.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ N.asFunctor.obj (op n))) ≅
          (∏ᶜ (fun n : ℕ ↦
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N).asFunctor.obj (op n))))
      (kappaG : ∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        (G.mapHomologicalComplex (.up ℤ)).obj (HB.obj N) ≅
          HA.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
            (.up ℤ)).obj N))
      (rho : LB ⋙ G.mapDerivedCategory ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
            (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)) ⋙ LA),
      -- The signed coordinates are pinned to the actual shifted cone, in both categories.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      -- Roos maps are the product map on each signed coordinate.
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : M ⟶ N) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA N p).hom = (chiA M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : M ⟶ N) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB N p).hom = (chiB M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      -- K-injective normalization of the same thetaA and thetaB.
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota) ∧
      -- The canonical product map, and its two-summand version kappaJ.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psiJ M).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n =
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦
          M.asFunctor.obj (op k))
          n)) ∧
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappaJ M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          J).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f (p + 1) =
          J.map ((chiA M p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappaJ M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          J).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f p =
          J.map ((chiA M p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f p)) ∧
      -- This square is lambdaJ = thetaB inverse, kappaJ, F(thetaA), in Lean order.
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapDerivedCategory).map (thetaA.hom.app M) ≫ J.mapDerivedCategoryFactors.hom.app (HA.obj
          M) ≫
            DerivedCategory.Q.{wB}.map (kappaJ M).hom =
          lambdaJ.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj J) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
                _ _ _ ↦
              inferInstance⟩)).hom.app M) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ∧
      -- Forward augmentation normalization uses the same lambda and the same theta.
      (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (D : CochainComplex A ℤ)
          (c : ∀ n : ℕ, D ⟶ M.asFunctor.obj (op n))
          (_hc : ∀ n : ℕ,
            c (n + 1) ≫ M.asFunctor.map (homOfLE (Nat.le_succ n)).op = c n),
        ∃ (b : D ⟶ HA.obj M)
          (bJ : (J.mapHomologicalComplex (.up ℤ)).obj D ⟶
            HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M)),
          (∀ p : ℤ, b.f (p + 1) ≫ (chiA M p).hom =
            biprod.lift ((Pi.lift c).f (p + 1)) 0) ∧
          (∀ p : ℤ, bJ.f (p + 1) ≫
            (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M) p).hom =
              biprod.lift ((Pi.lift (fun n : ℕ ↦
                (J.mapHomologicalComplex (.up ℤ)).map (c n))).f (p + 1)) 0) ∧
          (J.mapHomologicalComplex (.up ℤ)).map b ≫ (kappaJ M).hom = bJ ∧
          J.mapDerivedCategory.map (DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app M) ≫
              lambdaJ.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
                ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance
                  (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app M) =
            J.mapDerivedCategoryFactors.hom.app D ≫
              DerivedCategory.Q.{wB}.map bJ ≫ thetaB.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
                  (.up ℤ)).obj M)) ∧
      -- Restriction is the canonical product comparison on both signed coordinates.
      (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (n : ℕ),
        (psiG N).hom ≫ Pi.π _ n =
          (G.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n)) ∧
      (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ) (n : ℕ),
        (kappaG N).hom.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom ≫ biprod.fst ≫ (Pi.π (fun k : ℕ ↦
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                (.up ℤ)).obj N).asFunctor.obj (op k)) n).f (p + 1) =
          G.map ((chiB N p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappaG N).hom.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom ≫ biprod.snd ≫ (Pi.π (fun k : ℕ ↦
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                (.up ℤ)).obj N).asFunctor.obj (op k)) n).f p =
          G.map ((chiB N p).hom ≫ biprod.snd ≫ (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f p)) ∧
      (∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        G.mapDerivedCategory.map (thetaB.hom.app N) ≫
            G.mapDerivedCategoryFactors.hom.app (HB.obj N) ≫
            DerivedCategory.Q.{wA}.map (kappaG N).hom =
          rho.hom.app (DerivedCategory.Q.{wB}.obj N) ≫
            LA.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
              ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
                (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app N) ≫
            thetaA.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N)) ∧
      -- The actual descended adjunction unit, for every strict tower complex.
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (restrictionUnitDerivedAdjunction adj).unit.app (LA.obj (DerivedCategory.Q.obj M)) ≫
            G.mapDerivedCategory.map (lambdaJ.hom.app (DerivedCategory.Q.obj M)) ≫
            rho.hom.app (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
              ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance
                (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩))).obj
                  (DerivedCategory.Q.obj M)) =
          LA.map ((restrictionUnitTowerDerivedAdjunction adj).unit.app (DerivedCategory.Q.obj M))) ∧
      -- The same equality before localization, on both signed Roos summands.
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (adj.mapHomologicalComplex (.up ℤ)).unit.app (HA.obj M) ≫
            (G.mapHomologicalComplex (.up ℤ)).map (kappaJ M).hom ≫
            (kappaG ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M)).hom =
          HA.map (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app M)) ∧
      -- Every strict augmentation is sent to the coordinatewise restricted augmentation.
      (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (D : CochainComplex B ℤ)
          (c : ∀ n : ℕ, D ⟶ N.asFunctor.obj (op n))
          (_hc : ∀ n : ℕ,
            c (n + 1) ≫ N.asFunctor.map (homOfLE (Nat.le_succ n)).op = c n),
        ∃ (b : D ⟶ HB.obj N)
          (bG : (G.mapHomologicalComplex (.up ℤ)).obj D ⟶
            HA.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N)),
          (∀ p : ℤ, b.f (p + 1) ≫ (chiB N p).hom =
            biprod.lift ((Pi.lift c).f (p + 1)) 0) ∧
          (∀ p : ℤ, bG.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom =
              biprod.lift ((Pi.lift (fun n : ℕ ↦
                (G.mapHomologicalComplex (.up ℤ)).map (c n))).f (p + 1)) 0) ∧
          (G.mapHomologicalComplex (.up ℤ)).map b ≫ (kappaG N).hom = bG ∧
          G.mapDerivedCategory.map (DerivedCategory.Q.{wB}.map b ≫ thetaB.inv.app N) ≫
              rho.hom.app (DerivedCategory.Q.{wB}.obj N) ≫
              LA.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
                ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
                  (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app N) =
            G.mapDerivedCategoryFactors.hom.app D ≫
              DerivedCategory.Q.{wA}.map bG ≫ thetaA.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                  (.up ℤ)).obj N))
end Assertion

attribute [local semireducible] Functor.mapDerivedCategory
attribute [local semireducible] Functor.mapDerivedCategoryFactors
attribute [local semireducible] restrictionUnitDerivedAdjunction
attribute [local semireducible] restrictionUnitTowerDerivedAdjunction

private theorem complexProducts
    {A : Type a} [Category.{c} A] [Abelian A] [HasCountableProducts A]
    {I : Type*} [Countable I] :
    HasLimitsOfShape (Discrete I) (CochainComplex A ℤ) := inferInstance

private theorem complexTowerLimits
    {A : Type a} [Category.{c} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A] :
    HasLimitsOfShape ℕᵒᵖ (CochainComplex A ℤ) := inferInstance

attribute [local instance] complexProducts complexTowerLimits

private theorem product_degree_ext
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (K : ℕ → CochainComplex A ℤ) (p : ℤ) {D : A}
    (f g : D ⟶ (∏ᶜ K).X p)
    (h : ∀ n, f ≫ (Pi.π K n).f p = g ≫ (Pi.π K n).f p) : f = g := by
  apply (cancel_mono (piComparison (HomologicalComplex.eval A (.up ℤ) p) K)).mp
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, piComparison_comp_π, HomologicalComplex.eval_map] using h n

private theorem augmentation_eq
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (P : ℕ → CochainComplex A ℤ) (V : CochainComplex A ℤ) (W : CochainComplex B ℤ)
    (chi : ∀ p : ℤ, V.X (p + 1) ≅ (∏ᶜ P).X (p + 1) ⊞ (∏ᶜ P).X p)
    (chi' : ∀ p : ℤ, W.X (p + 1) ≅
      (∏ᶜ (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).obj (P n))).X (p + 1) ⊞
      (∏ᶜ (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).obj (P n))).X p)
    (k : (F.mapHomologicalComplex (.up ℤ)).obj V ⟶ W)
    (hk : ∀ p n,
      (k.f (p + 1) ≫ (chi' p).hom ≫ biprod.fst ≫
        (Pi.π (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).obj (P n)) n).f (p + 1) =
        F.map ((chi p).hom ≫ biprod.fst ≫ (Pi.π P n).f (p + 1))) ∧
      (k.f (p + 1) ≫ (chi' p).hom ≫ biprod.snd ≫
        (Pi.π (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).obj (P n)) n).f p =
        F.map ((chi p).hom ≫ biprod.snd ≫ (Pi.π P n).f p)))
    (D : CochainComplex A ℤ) (gamma : ∀ n, D ⟶ P n)
    (b : D ⟶ V) (b' : (F.mapHomologicalComplex (.up ℤ)).obj D ⟶ W)
    (hb : ∀ p, b.f (p + 1) ≫ (chi p).hom = biprod.lift ((Pi.lift gamma).f (p + 1)) 0)
    (hb' : ∀ p, b'.f (p + 1) ≫ (chi' p).hom =
      biprod.lift ((Pi.lift (fun n ↦
        (F.mapHomologicalComplex (.up ℤ)).map (gamma n))).f (p + 1)) 0) :
    (F.mapHomologicalComplex (.up ℤ)).map b ≫ k = b' := by
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  change F.map (b.f (p + 1)) ≫ k.f (p + 1) = b'.f (p + 1)
  apply (cancel_mono (chi' p).hom).mp
  apply biprod.hom_ext
  · apply product_degree_ext
    intro n
    simp only [Category.assoc]
    rw [(hk p n).1, ← F.map_comp, ← Category.assoc, ← Category.assoc, hb,
      biprod.lift_fst]
    rw [← Category.assoc (b'.f _), hb',
      biprod.lift_fst_assoc]
    have h := congrArg (fun f ↦ f.f (p + 1)) (Pi.lift_comp_π gamma n)
    have h' := congrArg (fun f ↦ f.f (p + 1))
      (Pi.lift_comp_π (fun n ↦ (F.mapHomologicalComplex (.up ℤ)).map (gamma n)) n)
    simpa only [HomologicalComplex.comp_f] using
      (congrArg F.map h).trans h'.symm
  · apply product_degree_ext
    intro n
    simp only [Category.assoc]
    rw [(hk p n).2, ← F.map_comp, ← Category.assoc, ← Category.assoc, hb,
      biprod.lift_snd]
    rw [← Category.assoc (b'.f _), hb',
      biprod.lift_snd_assoc]
    simp

private theorem descendIso {A B E : Type*} [Category* A] [Category* B] [Category* E]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W]
    (G H : B ⥤ E) (e : L ⋙ G ≅ L ⋙ H) :
    ∃ t : G ≅ H, ∀ X : A, t.hom.app (L.obj X) = e.hom.app X := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W E
  refine ⟨ff.preimageIso e, ?_⟩
  intro X
  exact congr_app (ff.map_preimage e.hom) X

section Descent
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

private theorem roosDescent (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ)
    (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex B ℤ)
    (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
    (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
    (kappa : ∀ M, (F.mapHomologicalComplex (.up ℤ)).obj (HA.obj M) ≅
      HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).obj M))
    (hknat : ∀ {M N} (f : M ⟶ N),
      (F.mapHomologicalComplex (.up ℤ)).map (HA.map f) ≫ (kappa N).hom =
        (kappa M).hom ≫ HB.map
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (.up ℤ)).map f)) :
    let Ftw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
    have : PreservesFiniteLimits Ftw := ⟨fun _ _ _ ↦ inferInstance⟩
    have : PreservesFiniteColimits Ftw := ⟨fun _ _ _ ↦ inferInstance⟩
    ∃ lambda : LA ⋙ F.mapDerivedCategory ≅ Ftw.mapDerivedCategory ⋙ LB,
      ∀ M, F.mapDerivedCategory.map (thetaA.hom.app M) ≫
        F.mapDerivedCategoryFactors.hom.app (HA.obj M) ≫
        DerivedCategory.Q.{wB}.map (kappa M).hom =
      lambda.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
        LB.map (Ftw.mapDerivedCategoryFactors.hom.app M) ≫
        thetaB.hom.app (Ftw.mapHomologicalComplex (.up ℤ) |>.obj M) := by
  let Ftw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
  have : PreservesFiniteLimits Ftw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits Ftw := ⟨fun _ _ _ ↦ inferInstance⟩
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Ft := Ftw.mapHomologicalComplex (.up ℤ)
  let FD := F.mapDerivedCategory
  let TD := Ftw.mapDerivedCategory
  let tk : HA ⋙ Fc ≅ Ft ⋙ HB := NatIso.ofComponents kappa (fun f ↦ hknat f)
  let e₁ : DerivedCategory.Q.{wA} ⋙ (LA ⋙ FD) ≅ HA ⋙ (Fc ⋙ DerivedCategory.Q.{wB}) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight thetaA FD ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft HA F.mapDerivedCategoryFactors
  let e₂ : DerivedCategory.Q.{wA} ⋙ (TD ⋙ LB) ≅ Ft ⋙ (HB ⋙ DerivedCategory.Q.{wB}) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight Ftw.mapDerivedCategoryFactors LB ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Ft thetaB
  let e : DerivedCategory.Q.{wA} ⋙ (LA ⋙ FD) ≅
      DerivedCategory.Q.{wA} ⋙ (TD ⋙ LB) :=
    e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight tk DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫ e₂.symm
  obtain ⟨lambda, hlambda⟩ := descendIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) (LA ⋙ FD) (TD ⋙ LB) e
  refine ⟨lambda, ?_⟩
  intro M
  rw [hlambda M]
  have hh : e₁.hom.app M ≫ DerivedCategory.Q.map (tk.hom.app M) =
      e.hom.app M ≫ e₂.hom.app M := by simp [e, Category.assoc]
  simpa only [e₁, e₂, tk, Iso.trans_hom, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, NatIso.ofComponents_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_id] using hh

end Descent

private theorem derivedUnit_isIso
    {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    {J : A ⥤ B} {G : B ⥤ A} [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : J ⊣ G)
    (hu : ∀ M, IsIso (adj.unit.app M)) (M : DerivedCategory.{wA} A) :
    IsIso ((restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app M) := by
  let a := restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj
  have hQ (P : CochainComplex A ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ,
          IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ hu (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have he : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          G.mapDerivedCategoryFactors.inv.app _ ≫
            G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, restrictionUnitDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [he]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

section UnitCompatibility
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

omit [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)] in
private theorem chainUnit
    (J : A ⥤ B) (G : B ⥤ A)
    [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : J ⊣ G)
    (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ)
    (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
    (chiA : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
    (chiB : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
    (kappaJ : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
    (kappaG : ∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        (G.mapHomologicalComplex (.up ℤ)).obj (HB.obj N) ≅
          HA.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
            (.up ℤ)).obj N))
    (hAm : (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : M ⟶ N) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA N p).hom = (chiA M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)))
    (hkappaJ : (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappaJ M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          J).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f (p + 1) =
          J.map ((chiA M p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappaJ M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          J).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f p =
          J.map ((chiA M p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f p)))
    (hkappaG : (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ) (n : ℕ),
        (kappaG N).hom.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom ≫ biprod.fst ≫ (Pi.π (fun k : ℕ ↦
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                (.up ℤ)).obj N).asFunctor.obj (op k)) n).f (p + 1) =
          G.map ((chiB N p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappaG N).hom.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom ≫ biprod.snd ≫ (Pi.π (fun k : ℕ ↦
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                (.up ℤ)).obj N).asFunctor.obj (op k)) n).f p =
          G.map ((chiB N p).hom ≫ biprod.snd ≫ (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f p)))
    : (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (adj.mapHomologicalComplex (.up ℤ)).unit.app (HA.obj M) ≫
            (G.mapHomologicalComplex (.up ℤ)).map (kappaJ M).hom ≫
            (kappaG ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M)).hom =
          HA.map (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app M)) := by
  let Jtw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj J
  let Gtw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G
  let Jc := J.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Jt := Jtw.mapHomologicalComplex (.up ℤ)
  let Gt := Gtw.mapHomologicalComplex (.up ℤ)
  intro M
  let v := ((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app M
  apply HomologicalComplex.Hom.ext
  funext i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  change adj.unit.app ((HA.obj M).X (p + 1)) ≫
    G.map ((kappaJ M).hom.f (p + 1)) ≫ (kappaG (Jt.obj M)).hom.f (p + 1) =
      (HA.map v).f (p + 1)
  apply (cancel_mono (chiA (Gt.obj (Jt.obj M)) p).hom).mp
  apply biprod.hom_ext
  · apply product_degree_ext
    intro n
    have hv := congrArg (fun f ↦ f ≫ biprod.fst ≫
        (Pi.π (fun n ↦ (Gt.obj (Jt.obj M)).asFunctor.obj (op n)) n).f (p + 1))
      (hAm v p)
    dsimp only [Functor.id_obj, Functor.comp_obj] at hv
    simp only [Category.assoc] at hv ⊢
    erw [biprod.map_fst_assoc] at hv
    erw [hv]
    erw [(hkappaG (Jt.obj M) p n).1, ← G.map_comp, (hkappaJ M p n).1]
    have hπ := congrArg (fun f ↦ f.f (p + 1))
      (Pi.map_π (fun n ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v).app (op n)) n)
    simp only [HomologicalComplex.comp_f] at hπ
    erw [hπ]
    convert! (adj.unit.naturality
      ((chiA M p).hom ≫ biprod.fst ≫
        (Pi.π (fun n ↦ M.asFunctor.obj (op n)) n).f (p + 1))).symm using 1
    all_goals simp [v, Adjunction.mapHomologicalComplex, Adjunction.whiskerRight_unit_app_app,
        Category.assoc]
  · apply product_degree_ext
    intro n
    have hv := congrArg (fun f ↦ f ≫ biprod.snd ≫
        (Pi.π (fun n ↦ (Gt.obj (Jt.obj M)).asFunctor.obj (op n)) n).f p)
      (hAm v p)
    dsimp only [Functor.id_obj, Functor.comp_obj] at hv
    simp only [Category.assoc] at hv ⊢
    erw [biprod.map_snd_assoc] at hv
    erw [hv]
    erw [(hkappaG (Jt.obj M) p n).2, ← G.map_comp, (hkappaJ M p n).2]
    have hπ := congrArg (fun f ↦ f.f p)
      (Pi.map_π (fun n ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v).app (op n)) n)
    simp only [HomologicalComplex.comp_f] at hπ
    erw [hπ]
    convert! (adj.unit.naturality
      ((chiA M p).hom ≫ biprod.snd ≫
        (Pi.π (fun n ↦ M.asFunctor.obj (op n)) n).f p)).symm using 1
    all_goals simp [v, Adjunction.mapHomologicalComplex, Adjunction.whiskerRight_unit_app_app,
        Category.assoc]

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem derivedUnitCompatibility
    (J : A ⥤ B) (G : B ⥤ A)
    [J.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : J ⊣ G)
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ)
    (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
    (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
    (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
    (kappaJ : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
    (lambdaJ : LA ⋙ J.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _
        _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance (⟨fun _ _ _ ↦
          inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB)
    (kappaG : ∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        (G.mapHomologicalComplex (.up ℤ)).obj (HB.obj N) ≅
          HA.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
            (.up ℤ)).obj N))
    (rho : LB ⋙ G.mapDerivedCategory ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
            (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)) ⋙ LA)
    (hsquareJ : (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapDerivedCategory).map (thetaA.hom.app M) ≫ J.mapDerivedCategoryFactors.hom.app (HA.obj
          M) ≫
            DerivedCategory.Q.{wB}.map (kappaJ M).hom =
          lambdaJ.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj J) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
                _ _ _ ↦
              inferInstance⟩)).hom.app M) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)))
    (hsquareG : (∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        G.mapDerivedCategory.map (thetaB.hom.app N) ≫
            G.mapDerivedCategoryFactors.hom.app (HB.obj N) ≫
            DerivedCategory.Q.{wA}.map (kappaG N).hom =
          rho.hom.app (DerivedCategory.Q.{wB}.obj N) ≫
            LA.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
              ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
                (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app N) ≫
            thetaA.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N)))
    (hunitChain : (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (adj.mapHomologicalComplex (.up ℤ)).unit.app (HA.obj M) ≫
            (G.mapHomologicalComplex (.up ℤ)).map (kappaJ M).hom ≫
            (kappaG ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M)).hom =
          HA.map (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app M)))
    : (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (LA.obj (DerivedCategory.Q.obj M)) ≫
            G.mapDerivedCategory.map (lambdaJ.hom.app (DerivedCategory.Q.obj M)) ≫
            rho.hom.app (((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
              ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance
                (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩))).obj
                  (DerivedCategory.Q.obj M)) =
          LA.map ((restrictionUnitTowerDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (DerivedCategory.Q.obj M))) := by
  let Jtw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj J
  let Gtw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G
  have : PreservesFiniteLimits Jtw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits Jtw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits Gtw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits Gtw := ⟨fun _ _ _ ↦ inferInstance⟩
  let Jc := J.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Jt := Jtw.mapHomologicalComplex (.up ℤ)
  let Gt := Gtw.mapHomologicalComplex (.up ℤ)
  intro M
  let v := ((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app M
  let dJ := Jtw.mapDerivedCategoryFactors.hom.app M
  let dG := Gtw.mapDerivedCategoryFactors.hom.app (Jt.obj M)
  apply (cancel_mono (LA.map (Gtw.mapDerivedCategory.map dJ ≫ dG) ≫
    thetaA.hom.app (Gt.obj (Jt.obj M)))).mp
  have hloc (P : CochainComplex A ℤ) :
      (restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          G.mapDerivedCategoryFactors.inv.app (Jc.obj P) ≫
            G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.inv.app P) := by
    simp only [restrictionUnitDerivedAdjunction, Adjunction.localization_unit_app]
    rfl
  have htloc :
      (restrictionUnitTowerDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (DerivedCategory.Q.obj M) ≫
          Gtw.mapDerivedCategory.map dJ ≫ dG = DerivedCategory.Q.map v := by
    simp only [restrictionUnitTowerDerivedAdjunction, restrictionUnitDerivedAdjunction,
      Adjunction.localization_unit_app]
    change (DerivedCategory.Q.map v ≫ Gtw.mapDerivedCategoryFactors.inv.app (Jt.obj M) ≫
      Gtw.mapDerivedCategory.map (Jtw.mapDerivedCategoryFactors.inv.app M)) ≫
      Gtw.mapDerivedCategory.map dJ ≫ dG = _
    simp only [dJ, dG, Category.assoc, ← Iso.app_inv, ← Iso.app_hom,
      Iso.inv_hom_id_map_assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = (restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (LA.obj (DerivedCategory.Q.obj M)) ≫
        G.mapDerivedCategory.map (lambdaJ.hom.app (DerivedCategory.Q.obj M) ≫
          LB.map dJ) ≫
        rho.hom.app (DerivedCategory.Q.obj (Jt.obj M)) ≫
        LA.map dG ≫ thetaA.hom.app (Gt.obj (Jt.obj M)) := by
      simp only [Functor.map_comp, Category.assoc]
      have hr :
          rho.hom.app (Jtw.mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
            LA.map (Gtw.mapDerivedCategory.map dJ) =
          G.mapDerivedCategory.map (LB.map dJ) ≫
            rho.hom.app (DerivedCategory.Q.obj (Jt.obj M)) :=
        (rho.hom.naturality dJ).symm
      rw [← Category.assoc (rho.hom.app _) (LA.map _) _, hr]
      simp only [Category.assoc]
    _ = (restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (LA.obj (DerivedCategory.Q.obj M)) ≫
        G.mapDerivedCategory.map
          (J.mapDerivedCategory.map (thetaA.hom.app M) ≫
            J.mapDerivedCategoryFactors.hom.app (HA.obj M) ≫
            DerivedCategory.Q.map (kappaJ M).hom) ≫
        G.mapDerivedCategoryFactors.hom.app (HB.obj (Jt.obj M)) ≫
        DerivedCategory.Q.map (kappaG (Jt.obj M)).hom := by
      rw [← hsquareG]
      rw [← G.mapDerivedCategory.map_comp_assoc]
      simpa only [Category.assoc] using
        congrArg (fun f ↦
          (restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
              (LA.obj (DerivedCategory.Q.obj M)) ≫
            G.mapDerivedCategory.map f ≫
            G.mapDerivedCategoryFactors.hom.app (HB.obj (Jt.obj M)) ≫
            DerivedCategory.Q.map (kappaG (Jt.obj M)).hom) (hsquareJ M).symm
    _ = thetaA.hom.app M ≫
        (restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.app
          (DerivedCategory.Q.obj (HA.obj M)) ≫
        G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app (HA.obj M)) ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map (kappaJ M).hom) ≫
        G.mapDerivedCategoryFactors.hom.app (HB.obj (Jt.obj M)) ≫
        DerivedCategory.Q.map (kappaG (Jt.obj M)).hom := by
      simp only [Functor.map_comp, Category.assoc]
      convert! (congrArg (fun f ↦ f ≫
          G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app (HA.obj M)) ≫
          G.mapDerivedCategory.map (DerivedCategory.Q.map (kappaJ M).hom) ≫
          G.mapDerivedCategoryFactors.hom.app (HB.obj (Jt.obj M)) ≫
          DerivedCategory.Q.map (kappaG (Jt.obj M)).hom)
          ((restrictionUnitDerivedAdjunction.{a, b, c, d, wA, wB} adj).unit.naturality
            (thetaA.hom.app M))).symm using 1 <;>
        simp only [Functor.id_map, Functor.id_obj, Functor.comp_map,
          Functor.comp_obj, Category.assoc]
    _ = thetaA.hom.app M ≫ DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app (HA.obj M) ≫
          Gc.map (kappaJ M).hom ≫ (kappaG (Jt.obj M)).hom) := by
      rw [hloc]
      simp only [Category.assoc, ← Iso.app_inv, ← Iso.app_hom,
        Iso.inv_hom_id_map_assoc]
      simp only [Iso.app_hom]
      rw [G.mapDerivedCategoryFactors_hom_naturality_assoc]
      dsimp only [Jc, Gc]
      simp only [← Iso.app_hom, Iso.inv_hom_id_assoc, Functor.map_comp]
    _ = thetaA.hom.app M ≫ DerivedCategory.Q.map (HA.map v) := by
      rw [hunitChain]
    _ = LA.map (DerivedCategory.Q.map v) ≫
        thetaA.hom.app (Gt.obj (Jt.obj M)) := by
      exact (thetaA.hom.naturality v).symm
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← LA.map_comp_assoc, ← LA.map_comp_assoc, Category.assoc, htloc]

end UnitCompatibility

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CochainComplex.mappingCone
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] restrictionUnitDerivedAdjunction
attribute [local irreducible] restrictionUnitTowerDerivedAdjunction
attribute [local irreducible] ComparisonAssertions
attribute [local irreducible] RestrictionUnitAssertions
attribute [local irreducible] SheafOfModules.localizedSystemAdjunction

attribute [local semireducible] CochainComplex.mappingCone

section Combine
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

private theorem combineComparisons
    (J : A ⥤ B) (G : B ⥤ A)
    [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : J ⊣ G)
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B)
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ⋙
        DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙ LA)
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex B ℤ) ⥤ CochainComplex B ℤ) ⋙
        DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙ LB)
    (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ)
    (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
    (hAobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
    (hBobj : ∀ M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj M =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (M).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
    (chiA : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
    (chiB : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        M).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (M).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (M).asFunctor.obj (op n))).X p)
    (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
    (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
    (psiJ : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦
          (M).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op n))))
    (kappaJ : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj M) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        M))
    (lambdaJ : LA ⋙ J.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _
        _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance (⟨fun _ _ _ ↦
          inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB)
    (psiG : ∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        (G.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ N.asFunctor.obj (op n))) ≅
          (∏ᶜ (fun n : ℕ ↦
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N).asFunctor.obj (op n))))
    (kappaG : ∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        (G.mapHomologicalComplex (.up ℤ)).obj (HB.obj N) ≅
          HA.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
            (.up ℤ)).obj N))
    (rho : LB ⋙ G.mapDerivedCategory ≅
        (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
            (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)) ⋙ LA)
    (hAc : (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)))
    (hBc : (∀ (M : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB M p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj M))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (M).asFunctor.obj (op n)) (fun n : ℕ ↦ (M).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)))
    (hAm : (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : M ⟶ N) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA N p).hom = (chiA M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)))
    (hBm : (∀ {M N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : M ⟶ N) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB N p).hom = (chiB M p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)))
    (hAn : (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HA.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiA I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaA.app I ≫ thetaA.hom.app I = DerivedCategory.Q.{wA}.map iota))
    (hBn : (∀ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) [I.IsKInjective] (_hIinj :
        ∀ p : ℤ, Injective (I.X p)),
        ∃ iota : limit I.asFunctor ⟶ HB.obj I,
          QuasiIso iota ∧
          (∀ p : ℤ, iota.f (p + 1) ≫ (chiB I p).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) 0) ∧
          etaB.app I ≫ thetaB.hom.app I = DerivedCategory.Q.{wB}.map iota))
    (hpsiJ : (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psiJ M).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n =
        (J.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦
          M.asFunctor.obj (op k))
          n)))
    (hkappaJ : (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappaJ M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          J).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f (p + 1) =
          J.map ((chiA M p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappaJ M).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          J).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) p).hom ≫
            biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M).asFunctor.obj (op k)) n).f p =
          J.map ((chiA M p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n).f p)))
    (hsquareJ : (∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (J.mapDerivedCategory).map (thetaA.hom.app M) ≫ J.mapDerivedCategoryFactors.hom.app (HA.obj
          M) ≫
            DerivedCategory.Q.{wB}.map (kappaJ M).hom =
          lambdaJ.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj J) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
                _ _ _ ↦
              inferInstance⟩)).hom.app M) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)))
    (haugJ : (∀ (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (D : CochainComplex A ℤ)
          (c : ∀ n : ℕ, D ⟶ M.asFunctor.obj (op n))
          (_hc : ∀ n : ℕ,
            c (n + 1) ≫ M.asFunctor.map (homOfLE (Nat.le_succ n)).op = c n),
        ∃ (b : D ⟶ HA.obj M)
          (bJ : (J.mapHomologicalComplex (.up ℤ)).obj D ⟶
            HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M)),
          (∀ p : ℤ, b.f (p + 1) ≫ (chiA M p).hom =
            biprod.lift ((Pi.lift c).f (p + 1)) 0) ∧
          (∀ p : ℤ, bJ.f (p + 1) ≫
            (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
              (.up ℤ)).obj M) p).hom =
              biprod.lift ((Pi.lift (fun n : ℕ ↦
                (J.mapHomologicalComplex (.up ℤ)).map (c n))).f (p + 1)) 0) ∧
          J.mapDerivedCategory.map (DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app M) ≫
              lambdaJ.hom.app (DerivedCategory.Q.{wA}.obj M) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
                ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J) inferInstance
                  (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app M) =
            J.mapDerivedCategoryFactors.hom.app D ≫
              DerivedCategory.Q.{wB}.map bJ ≫ thetaB.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex
                  (.up ℤ)).obj M)))
    (hpsiG : (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (n : ℕ),
        (psiG N).hom ≫ Pi.π _ n =
          (G.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n)))
    (hkappaG : (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ) (n : ℕ),
        (kappaG N).hom.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom ≫ biprod.fst ≫ (Pi.π (fun k : ℕ ↦
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                (.up ℤ)).obj N).asFunctor.obj (op k)) n).f (p + 1) =
          G.map ((chiB N p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappaG N).hom.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom ≫ biprod.snd ≫ (Pi.π (fun k : ℕ ↦
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                (.up ℤ)).obj N).asFunctor.obj (op k)) n).f p =
          G.map ((chiB N p).hom ≫ biprod.snd ≫ (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f p)))
    (hsquareG : (∀ N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        G.mapDerivedCategory.map (thetaB.hom.app N) ≫
            G.mapDerivedCategoryFactors.hom.app (HB.obj N) ≫
            DerivedCategory.Q.{wA}.map (kappaG N).hom =
          rho.hom.app (DerivedCategory.Q.{wB}.obj N) ≫
            LA.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
              ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
                (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app N) ≫
            thetaA.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N)))
    (haugG : (∀ (N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (D : CochainComplex B ℤ)
          (c : ∀ n : ℕ, D ⟶ N.asFunctor.obj (op n))
          (_hc : ∀ n : ℕ,
            c (n + 1) ≫ N.asFunctor.map (homOfLE (Nat.le_succ n)).op = c n),
        ∃ (b : D ⟶ HB.obj N)
          (bG : (G.mapHomologicalComplex (.up ℤ)).obj D ⟶
            HA.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N)),
          (∀ p : ℤ, b.f (p + 1) ≫ (chiB N p).hom =
            biprod.lift ((Pi.lift c).f (p + 1)) 0) ∧
          (∀ p : ℤ, bG.f (p + 1) ≫
            (chiA ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
              (.up ℤ)).obj N) p).hom =
              biprod.lift ((Pi.lift (fun n : ℕ ↦
                (G.mapHomologicalComplex (.up ℤ)).map (c n))).f (p + 1)) 0) ∧
          G.mapDerivedCategory.map (DerivedCategory.Q.{wB}.map b ≫ thetaB.inv.app N) ≫
              rho.hom.app (DerivedCategory.Q.{wB}.obj N) ≫
              LA.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
                ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) inferInstance
                  (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦ inferInstance⟩)).hom.app N) =
            G.mapDerivedCategoryFactors.hom.app D ≫
              DerivedCategory.Q.{wA}.map bG ≫ thetaA.inv.app
                ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex
                  (.up ℤ)).obj N)))
    : RestrictionUnitAssertions J G adj LA LB etaA etaB := by
  unfold RestrictionUnitAssertions
  let Jt := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J).mapHomologicalComplex (.up ℤ)
  let Gt := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G).mapHomologicalComplex (.up ℤ)
  have hunit := chainUnit J G adj HA HB chiA chiB kappaJ kappaG hAm hkappaJ hkappaG
  refine ⟨HA, HB, hAobj, hBobj, chiA, chiB, thetaA, thetaB,
    psiJ, kappaJ, lambdaJ, psiG, kappaG, rho,
    hAc, hBc, hAm, hBm, hAn, hBn, hpsiJ, hkappaJ, hsquareJ,
    ?_, hpsiG, hkappaG, hsquareG, ?_, hunit, ?_⟩
  · intro M Q gamma hgamma
    obtain ⟨b, b', hb, hb', he⟩ := haugJ M Q gamma hgamma
    refine ⟨b, b', hb, hb', ?_, he⟩
    exact augmentation_eq J _ _ _ (chiA M) (chiB (Jt.obj M))
      (kappaJ M).hom (hkappaJ M) Q gamma b b' hb hb'
  · exact derivedUnitCompatibility J G adj LA LB HA HB thetaA thetaB
      kappaJ lambdaJ kappaG rho hsquareJ hsquareG hunit
  · intro N Q gamma hgamma
    obtain ⟨b, b', hb, hb', he⟩ := haugG N Q gamma hgamma
    refine ⟨b, b', hb, hb', ?_, he⟩
    exact augmentation_eq G _ _ _ (chiB N) (chiA (Gt.obj N))
      (kappaG N).hom (hkappaG N) Q gamma b b' hb hb'

end Combine

section ReverseProperties
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ B)]

private def ChainConstruction (F : A ⥤ B) [F.Additive] : Prop :=
  ∀ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (chiB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
    (_hcoord :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)))
    (_hmaps :
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HA.map f).f (p + 1) ≫ (chiA Y p).hom = (chiA X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} (f : X ⟶ Y) (p : ℤ),
        (HB.map f).f (p + 1) ≫ (chiB Y p).hom = (chiB X p).hom ≫
        biprod.map
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f (p + 1))
          ((Limits.Pi.map (fun n : ℕ ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            f).app (op n))).f p))),
    ∃ (psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X)),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psi X).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k))
          n)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA X p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f p =
          F.map ((chiA X p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
        (f : X ⟶ Y),
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (HA.map f) ≫ (kappa Y).hom =
          (kappa X).hom ≫ HB.map
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f))

attribute [local irreducible] ChainConstruction

private def CompatibilityConstruction (F : A ⥤ B)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA} A)
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB} B) : Prop :=
  ∀ (HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex
      (A) ℤ) (HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ CochainComplex (B) ℤ)
      (hAobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, HA.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (hBobj : ∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, HB.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦ (X).asFunctor.obj
        (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (chiA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (HA.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (chiB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (HB.obj
        X).X (p + 1) ≅ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))).X (p + 1) ⊞ (∏ᶜ (fun n : ℕ ↦
        (X).asFunctor.obj (op n))).X p)
      (thetaA : DerivedCategory.Q.{wA} ⋙ LA ≅ HA ⋙ DerivedCategory.Q.{wA})
      (thetaB : DerivedCategory.Q.{wB} ⋙ LB ≅ HB ⋙ DerivedCategory.Q.{wB})
      (psi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op
        n))) ≅ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
      (kappa : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HA.obj X) ≅ HB.obj
        ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        X))
      (lambda : LA ⋙ F.mapDerivedCategory ≅ (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun
        _ _ _ ↦ inferInstance⟩)) ⋙ LB)
    (_hcoord :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ), (chiA X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (A) ℤ ↦ V.X (p +
          1)) (hAobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (p : ℤ), (chiB X p).hom =
        (eqToIso (congrArg (fun V : CochainComplex (B) ℤ ↦ V.X (p +
          1)) (hBobj X))).hom ≫
        ((CochainComplex.mappingCone (towerTransitionEndomorphism (K := fun n : ℕ ↦
          (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ
          n)).op))).shiftFunctorObjXIso (-1) (p + 1) p (add_neg_cancel_right p 1).symm).hom ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism (K := fun n : ℕ
          ↦ (X).asFunctor.obj (op n)) (fun n : ℕ ↦ (X).asFunctor.map (homOfLE (Nat.le_succ n)).op))
          p (p + 1) rfl).hom ≫
        biprod.map (𝟙 _) (-𝟙 _)))
    (_hpsi :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ), (psi X).hom ≫
        Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k))
          n)))
    (_hkappa :
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ),
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f (p + 1) =
          F.map ((chiA X p).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
        (kappa X).hom.f (p + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
          F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X).asFunctor.obj (op k)) n).f p =
          F.map ((chiA X p).hom ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f p)))
    (_hsquare :
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        (F.mapDerivedCategory).map (thetaA.hom.app X) ≫ F.mapDerivedCategoryFactors.hom.app (HA.obj
          X) ≫
            DerivedCategory.Q.{wB}.map (kappa X).hom =
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
            LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
              ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
              inferInstance⟩)).hom.app X) ≫
            thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X))),
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        ∃ (p : HA.obj X ⟶ (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n)))) (p' : HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X) ⟶ (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))))
          (delta : (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ⟶ (HA.obj X)⟦(1 : ℤ)⟧)
          (delta' : (∏ᶜ (fun n : ℕ ↦ ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X).asFunctor.obj (op n))) ⟶ (HB.obj
            ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
            ℤ)).obj X))⟦(1 : ℤ)⟧),
          (∀ i : ℤ, p.f (i + 1) = (chiA X i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, p'.f (i + 1) = (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom ≫ biprod.fst) ∧
          (∀ i : ℤ, delta.f i ≫ ((HA.obj X).shiftFunctorObjXIso 1 i (i + 1) rfl).hom ≫
            (chiA X i).hom = -biprod.inr) ∧
          (∀ i : ℤ, delta'.f i ≫ ((HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)).shiftFunctorObjXIso 1 i (i + 1)
            rfl).hom ≫
            (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X) i).hom = -biprod.inr) ∧
          lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) ≫
              thetaB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫ DerivedCategory.Q.{wB}.map p' =
            (F.mapDerivedCategory).map (thetaA.hom.app X ≫ DerivedCategory.Q.{wA}.map p) ≫
              F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
                DerivedCategory.Q.{wB}.map (psi X).hom ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map delta ≫
            (DerivedCategory.Q.{wA}.commShiftIso (1 : ℤ)).hom.app (HA.obj X) ≫
              (thetaA.inv.app X)⟦(1 : ℤ)⟧') ≫
              (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (LA.obj
                (DerivedCategory.Q.{wA}.obj X)) ≫
              (lambda.hom.app (DerivedCategory.Q.{wA}.obj X))⟦(1 : ℤ)⟧' ≫
              (LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X))⟦(1 : ℤ)⟧' =
            F.mapDerivedCategoryFactors.hom.app (∏ᶜ (fun n : ℕ ↦ (X).asFunctor.obj (op n))) ≫
              DerivedCategory.Q.{wB}.map (psi X).hom ≫
              DerivedCategory.Q.{wB}.map delta' ≫ (DerivedCategory.Q.{wB}.commShiftIso (1 :
                ℤ)).hom.app (HB.obj ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
                F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)) ≫
              (thetaB.inv.app ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X))⟦(1 : ℤ)⟧') ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Q : CochainComplex
        (A) ℤ) (gamma : ∀ n : ℕ, Q ⟶ X.asFunctor.obj (op n))
        (_hgamma : ∀ n : ℕ, gamma (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = gamma n),
        ∃ (b : Q ⟶ HA.obj X) (b' : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ⟶ HB.obj
          ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          X)),
          (∀ i : ℤ, b.f (i + 1) ≫ (chiA X i).hom = biprod.lift ((Pi.lift gamma).f (i + 1)) 0) ∧
          (∀ i : ℤ, b'.f (i + 1) ≫ (chiB ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj
            F).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) i).hom =
            biprod.lift ((Pi.lift (fun n : ℕ ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (gamma n))).f (i + 1)) 0) ∧
          (F.mapDerivedCategory).map (DerivedCategory.Q.{wA}.map b ≫ thetaA.inv.app X) ≫
              lambda.hom.app (DerivedCategory.Q.{wA}.obj X) ≫
              LB.map ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _ ((Functor.whiskeringRight
                ℕᵒᵖ _ _).obj F) inferInstance (⟨fun _ _ _ ↦ inferInstance⟩) (⟨fun _ _ _ ↦
                inferInstance⟩)).hom.app X) =
            F.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.{wB}.map b' ≫ thetaB.inv.app
              ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapHomologicalComplex (ComplexShape.up
              ℤ)).obj X))

attribute [local irreducible] CompatibilityConstruction

private theorem assembleFromProperties
    (JF : A ⥤ B)
    [JF.Additive] [PreservesFiniteLimits JF] [PreservesFiniteColimits JF]
    (GF : B ⥤ A)
    [GF.Additive] [PreservesFiniteLimits GF] [PreservesFiniteColimits GF]
    (adj : JF ⊣ GF)
    (_hprodG : ∀ M : ℕ → B,
      IsIso (piComparison GF M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{wA}
      (A))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{wB}
      (B))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (A) ℤ) ⥤ CochainComplex
        (A) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙
        LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (B) ℤ) ⥤ CochainComplex
        (B) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙
        LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (ComplexShape.up ℤ)))
    (hchain : ChainConstruction GF)
    (hcompat : CompatibilityConstruction GF LB LA)
    (hcomparison : ComparisonAssertions JF LA LB etaA etaB) :
    RestrictionUnitAssertions JF GF adj LA LB etaA etaB := by
  unfold ChainConstruction at hchain
  unfold CompatibilityConstruction at hcompat
  unfold ComparisonAssertions at hcomparison
  obtain ⟨HA, HB, hAobj, hBobj, chiA, chiB, thetaA, thetaB, psiJ, kappaJ,
      betaJ, lambdaJ, laws⟩ := hcomparison
  have hAc := laws.1
  have hBc := laws.2.1
  have hAm {M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
      (f : M ⟶ N) (p : ℤ) := laws.2.2.1 f p
  have hBm {M N : CochainComplex (ℕᵒᵖ ⥤ B) ℤ}
      (f : M ⟶ N) (p : ℤ) := laws.2.2.2.1 f p
  have hAn := laws.2.2.2.2.1
  have hBn := laws.2.2.2.2.2.1
  have hpsiJ := laws.2.2.2.2.2.2.1
  have hkappaJ := laws.2.2.2.2.2.2.2.1
  have hsquareJ := laws.2.2.2.2.2.2.2.2.1
  have haugJ := laws.2.2.2.2.2.2.2.2.2.2.2
  let JFtw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj JF
  let GFtw := (Functor.whiskeringRight ℕᵒᵖ _ _).obj GF
  have : PreservesFiniteLimits JFtw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits JFtw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits GFtw := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits GFtw := ⟨fun _ _ _ ↦ inferInstance⟩
  let JFt := JFtw.mapHomologicalComplex (.up ℤ)
  let GFt := GFtw.mapHomologicalComplex (.up ℤ)
  obtain ⟨psiG, kappaG, hpsiG, hkappaG, hknatG⟩ :=
    hchain
      HB HA hBobj hAobj chiB chiA ⟨hBc, hAc⟩ ⟨hBm, hAm⟩
  have hd := @roosDescent
    (B) (A)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    GF inferInstance inferInstance inferInstance LB LA HB HA thetaB thetaA kappaG hknatG
  obtain ⟨rho, hsquareG⟩ := hd
  have haugG :=
    (hcompat
      HB HA hBobj hAobj chiB chiA thetaB thetaA psiG kappaG rho
      ⟨hBc, hAc⟩ hpsiG hkappaG hsquareG).2
  exact combineComparisons JF GF adj LA LB etaA etaB
    HA HB hAobj hBobj chiA chiB thetaA thetaB psiJ kappaJ lambdaJ psiG kappaG rho
    hAc hBc hAm hBm hAn hBn hpsiJ hkappaJ hsquareJ
    (fun M Q gamma hgamma ↦ by
      obtain ⟨b, b', hb, hb', he, _⟩ := haugJ M Q gamma hgamma
      exact ⟨b, b', hb, hb', he⟩) hpsiG hkappaG hsquareG haugG

end ReverseProperties

attribute [local irreducible] CochainComplex.mappingCone

universe uC vC r uD vD s

set_option backward.defeqAttrib.useBackward true in
private theorem assembleRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    {D : Type uD} [Category.{vD} D] (K : GrothendieckTopology D)
    [HasSheafify K AddCommGrpCat.{max uD vD s}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max uD vD s}]
    (S : Sheaf K RingCat.{max uD vD s})
    (_hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uD vD s} S)]
    [HasCountableProducts (ringedSiteModules.{max uC vC r} R)]
    [HasCountableProducts (ringedSiteModules.{max uD vD s} S)]
    [HasBinaryBiproducts (ringedSiteModules.{max uC vC r} R)]
    [HasBinaryBiproducts (ringedSiteModules.{max uD vD s} S)]
    [HasLimitsOfShape ℕᵒᵖ (ringedSiteModules.{max uC vC r} R)]
    [HasLimitsOfShape ℕᵒᵖ (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wA} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{max uD vD s} S)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S)]
    (JF : ringedSiteModules.{max uC vC r} R ⥤ ringedSiteModules.{max uD vD s} S)
    [JF.Additive] [PreservesFiniteLimits JF] [PreservesFiniteColimits JF]
    (GF : ringedSiteModules.{max uD vD s} S ⥤ ringedSiteModules.{max uC vC r} R)
    [GF.Additive] [PreservesFiniteLimits GF] [PreservesFiniteColimits GF]
    (adj : JF ⊣ GF)
    (hprodG : ∀ M : ℕ → ringedSiteModules.{max uD vD s} S,
      IsIso (piComparison GF M))
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤ DerivedCategory.{wA}
      (ringedSiteModules.{max uC vC r} R))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) ⥤ DerivedCategory.{wB}
      (ringedSiteModules.{max uD vD s} S))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wA} ⋙
        LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uD vD s} S) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uD vD s} S) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶ DerivedCategory.Q.{wB} ⋙
        LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uD vD s} S) (ComplexShape.up ℤ)))
    (hcomparison : ComparisonAssertions JF LA LB etaA etaB) :
    RestrictionUnitAssertions JF GF adj LA LB etaA etaB := by
  have hc : ChainConstruction GF := by
    unfold ChainConstruction
    exact exactProductFunctorRoosChainMaps.{uD, vD, s, uC, vC, r, wB, wA}
      K S J R _hS _hR GF hprodG
  have ha : CompatibilityConstruction GF LB LA := by
    unfold CompatibilityConstruction
    exact exactProductFunctorRoosCompatibility.{uD, vD, s, uC, vC, r, wB, wA}
      K S J R _hS _hR GF hprodG LB LA etaB _hLB etaA _hLA
  exact assembleFromProperties JF GF adj hprodG LA LB etaA _hLA etaB _hLB hc ha hcomparison

attribute [-instance] complexProducts complexTowerLimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{t}) (U : X.ProEt)

/-- Exact restriction structure reused from the canonical slice functor.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-restriction-unit). -/
instance restrictionUnitAdditive : (restriction l E X U).Additive :=
  SheafOfModules.localizedSystemRestrictionAdditive.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U

/-- Exact restriction structure reused from the canonical slice functor.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-restriction-unit). -/
instance restrictionUnitLimits : PreservesFiniteLimits (restriction l E X U) :=
  SheafOfModules.localizedSystemRestrictionLimits.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U

/-- Exact restriction structure reused from the canonical slice functor.
Source: Stacks 03DJ (blueprint: lem-sf-open-roos-restriction-unit). -/
instance restrictionUnitColimits : PreservesFiniteColimits (restriction l E X U) :=
  SheafOfModules.localizedSystemRestrictionColimits.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U

/-- Restriction preserves coefficients and products, and its normalized Roos comparison
composed with the open-extension comparison is precisely the actual open unit.

Source: Stacks 09BP, 04IX, 03DJ and 0941
(blueprint: lem-sf-open-roos-restriction-unit).

Proof:
1. The actual restriction is a right adjoint, so it preserves countable products.
   The product-comparison projection equation gives the stated section formula.
   The clopen coefficient comparison identifies the completed coefficients.
2. An open slice is subterminal. On it the extension presheaf has one summand;
   its canonical injection is invertible. Cocontinuous restriction commutes with
   sheafification, so the uniquely normalized actual unit is invertible. The
   localization-unit formula gives the same result for the derived unit.
3. Reuse the shared signed Roos models of the extension comparison. Apply the
   exact-product chain-map theorem to restriction with these models reversed.
   Descend the resulting natural comparison through Q by full faithfulness of
   whiskering, and use the existing compatibility theorem for augmentations.
4. On each signed coordinate, product projection and actual unit naturality
   identify the composite comparison with HA of the tower unit. Product and
   biproduct extensionality prove the chain-map equality. The same argument on
   the coordinates (gamma,0) proves the two chain augmentation identities.
5. Postcompose with the tower localization comparisons and thetaA. Naturality
   of rho, its normalized square, and the extension square cancel thetaB.
   Derived-unit naturality, the localization-unit formula, and the chain
   identity reduce both sides to thetaA followed by Q of HA of the tower unit.
All degrees are arbitrary integers; no tensor, boundedness or constructibility is used.
-/
theorem restriction_unit
    (D : FiniteFieldDatum.{t}) (_hl : l ≠ D.p)
    (aX : X ⟶ Spec (CommRingCat.of D.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType (U.hom ≫ aX)] [QuasiCompact (U.hom ≫ aX)]
    [IsOpenImmersion U.hom]
    [HasDerivedCategory.{wA} (modulesU l E X U)]
    [HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ modulesU l E X U)]
    [HasDerivedCategory.{wB} (modulesX l E X)]
    [HasDerivedCategory.{wB} (ℕᵒᵖ ⥤ modulesX l E X)]
    (LA : DerivedCategory.{wA} (ℕᵒᵖ ⥤ modulesU l E X U) ⥤
      DerivedCategory.{wA} (modulesU l E X U))
    (LB : DerivedCategory.{wB} (ℕᵒᵖ ⥤ modulesX l E X) ⥤
      DerivedCategory.{wB} (modulesX l E X))
    (etaA : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (modulesU l E X U) ℤ) ⥤
        CochainComplex (modulesU l E X U) ℤ) ⋙ DerivedCategory.Q.{wA} ⟶
      DerivedCategory.Q.{wA} ⋙ LA)
    (_hLA : LA.IsRightDerivedFunctor etaA
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ modulesU l E X U) (ComplexShape.up ℤ)))
    (etaB : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (modulesX l E X) ℤ) ⥤
        CochainComplex (modulesX l E X) ℤ) ⋙ DerivedCategory.Q.{wB} ⟶
      DerivedCategory.Q.{wB} ⋙ LB)
    (_hLB : LB.IsRightDerivedFunctor etaB
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ modulesX l E X) (ComplexShape.up ℤ))) :
    (∀ M : ℕ → modulesX l E X,
      IsIso (piComparison (restriction l E X U) M)) ∧
    (∀ (M : ℕ → modulesX l E X) (V : Over U)
        (x : (((restriction l E X U).obj (∏ᶜ M)).val.obj (op V))) (n : ℕ),
      ((Pi.π (fun k : ℕ ↦ (restriction l E X U).obj (M k)) n).val.app (op V))
          ((piComparison (restriction l E X U) M).val.app (op V) x) =
        (Pi.π M n).val.app (op V.left) x) ∧
    Nonempty (SfClopenCoefficientRestriction l E X U.hom.opensRange) ∧
    (∀ M : modulesU l E X U,
      IsIso ((SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
        (completedIntegralCommRingSheafUnrestricted l E X) U).unit.app M)) ∧
    (∀ M : DerivedCategory.{wA} (modulesU l E X U),
      IsIso ((restrictionUnitDerivedAdjunction
        (SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
          (completedIntegralCommRingSheafUnrestricted l E X) U) :
          (extension l E X U).mapDerivedCategory ⊣
            (restriction l E X U).mapDerivedCategory).unit.app M)) ∧
    RestrictionUnitAssertions (extension l E X U) (restriction l E X U)
      (SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
        (completedIntegralCommRingSheafUnrestricted l E X) U) LA LB etaA etaB := by
  let adj := SheafOfModules.localizedSystemAdjunction.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U
  have hU : ∀ V : X.ProEt, Subsingleton (V ⟶ U) := by
    intro V
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  have : Mono (terminal.from U) := ⟨fun {V} f g _ ↦ (hU V).elim f g⟩
  have hunit := SheafOfModules.SubterminalLocal.adj_unit_isIso.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E X) U
  have hu : ∀ M : modulesU l E X U, IsIso (adj.unit.app M) :=
    fun M ↦ (NatTrans.isIso_iff_isIso_app _).mp hunit M
  have : PreservesLimitsOfSize.{0, 0} (restriction l E X U) :=
    adj.rightAdjoint_preservesLimits
  refine ⟨fun M ↦ inferInstance, ?_,
    sf_clopen_coefficient_comparison l E X U.hom.opensRange, ?_, ?_, ?_⟩
  · intro M V x n
    have h := congrArg (fun f ↦ (f.val.app (op V)) x)
      (piComparison_comp_π (restriction l E X U) M n)
    exact h
  · exact hu
  · intro M
    exact derivedUnit_isIso.{_, _, _, _, wA, wB}
      (A := modulesU l E X U) (B := modulesX l E X)
      (J := extension l E X U) (G := restriction l E X U) adj hu M
  · have hproducts := (geometry_products l E X U D _hl aX).2.2.2.2.2.2.2.2.2
    have := hproducts.1
    have := hproducts.2.1
    let R := completedIntegralCoefficientSheafUnrestricted l E X
    have hR : ∀ V, ∀ x y : R.obj.obj V, x * y = y * x :=
      completedIntegralCoefficient_mul_commUnrestricted l E X
    exact assembleRestriction.{wA, wB, t + 1, t, u, t + 1, t, u}
      (C := Over U) (D := X.ProEt)
      ((Scheme.ProEt.topology X).over U) (R.over U)
      (Scheme.ProEt.topology X) R (fun (V : (Over U)ᵒᵖ) ↦ hR (op V.unop.left)) hR
      (extension l E X U) (restriction l E X U) adj
      (fun M ↦ inferInstance) LA LB etaA _hLA etaB _hLB
      (comparison.{t, u, wA, wB} l E X U D _hl aX LA LB etaA _hLA etaB _hLB)

end WeilConjectures.SfOpenRoos
