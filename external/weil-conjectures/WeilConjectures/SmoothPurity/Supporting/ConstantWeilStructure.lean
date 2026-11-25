/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

import Mathlib.LinearAlgebra.TensorProduct.Tower

import Mathlib.Algebra.Homology.HomologicalComplexLimits

import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm

import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.MilnorTower
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # Canonical Weil structure on constant coefficients

Source: Weil blueprint, ordinary compact cohomology, order 1510, coefficient paragraph;
Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: def-weil-constant-weil-structure).

Finite coefficients use the constant-section inverse-image map. The integral map is its
inverse limit. The derived normalization is fixed on the regular K-flat representative:
the inverse structure map is the compatible unit into the strict finite-pullback Roos
complex, with zero shifted-cone component. Thus no arbitrary derived isomorphism is chosen.
The natural number n denotes the positive coefficient exponent n+1 throughout.

## Main definitions

- `constantWeilFiniteComparison` and `constantWeilIntegralComparison`: canonical ring maps.
- `constantWeilIntegralLambda` and `constantWeilIntegralTheta`: normalized derived structure.
- `constantWeilRationalSheaf`: the rational constant Weil sheaf.
- `constantWeilAlgebraicallyClosedSheaf`: the literal least-stage constant Weil sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual quotient reduction on finite constant commutative-ring sheaves.
Source: blueprint order 1510, clause 1 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilCoefficientReduction (Y : Scheme.{u}) (n : ℕ) :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))

/-- The completed integral comparison, uniquely fixed by all finite projections.
Its defining projection equations are exactly limit(c_n) after the inverse-limit comparison.
Source: blueprint order 1510, clause 2 (blueprint: def-weil-constant-weil-structure). -/
abbrev constantWeilIntegralComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  isomorphismCompletedCoefficientComparison l E g

/-- The actual regular coefficient complex, before derived localization.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralComplex (Y : Scheme.{u}) :=
  (CochainComplex.singleFunctor (integralTowerModules l E Y) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

universe c w

private theorem regular_good {C : Type c} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) :
    let U := (CochainComplex.singleFunctor (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) 0).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    CochainComplex.IsKFlatIndependentCoefficients (R := R) U ∧
      ∀ i, SheafOfModules.IsFlatOnSite.{c, v, w, w} (J := J) (R := R) (U.X i) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let A := SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let U := (CochainComplex.singleFunctor A 0).obj
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
  constructor
  · intro Z hZ
    exact fun i ↦ (hZ i).of_iso (HomologicalComplex.rightUnitor Z).symm
  · intro i
    have hcat : ObjectProperty.flat (U.X i) := by
      by_cases hi : i = 0
      · subst i
        exact ObjectProperty.prop_unit _
      · exact ObjectProperty.flat.prop_of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hcat.2

/-- The regular coefficient complex is a permitted K-flat representative with flat terms.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure).
Proof: its only nonzero term is the regular module. Tensoring with it is naturally the
identity on complexes, so it preserves acyclicity. The regular module is flat, and all
other terms are zero and flat. This proves both clauses of integralOperationsGoodComplex. -/
theorem constantWeilIntegralComplex_good (Y : Scheme.{u}) :
    integralOperationsGoodComplex l E Y (constantWeilIntegralComplex l E Y) := by
  exact @regular_good.{u, u + 1, u + 1} Y.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Y)
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E Y)

/-- The specified good representative; only its K-flatness proof is postponed.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralGood (Y : Scheme.{u}) :
    (integralOperationsGoodComplex l E Y).FullSubcategory :=
  ⟨constantWeilIntegralComplex l E Y, constantWeilIntegralComplex_good l E Y⟩

/-- The strict pullback tower of the actual regular representative.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilPullbackTower {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (integralOperationsPullbackTowerFunctor l E g).obj (constantWeilIntegralComplex l E Y)

/-- The actual 1-shift endomorphism of the product in the pullback Roos complex.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilPullbackRoosEndomorphism {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  towerTransitionEndomorphism
    (K := fun n ↦ (constantWeilPullbackTower l E g).obj (op n))
    (integralOperationsTowerStep (constantWeilPullbackTower l E g))

/-- The section one in degree zero of the single regular complex.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilUnitSection (Y : Scheme.{u}) (V : Y.ProEt) :
    ((constantWeilIntegralComplex l E Y).X 0).val.obj (op V) :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))).inv.val.app
      (op V)) (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))

/-- The image of 1 tensor 1 in degree zero of the actual finite reduction.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilReducedUnitSection (Y : Scheme.{u}) (n : ℕ) (V : Y.ProEt) :
    ((((unrestrictedIntegralFiniteComplex l E Y n).obj
      (constantWeilIntegralComplex l E Y)).X 0).val.obj (op V)) :=
  (((unrestrictedIntegralReductionFunctor l E Y n).map
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))).inv).val.app
        (op V))
    (unrestrictedIntegralTensorSection l E Y n
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) (op V) 1
      (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)))

section ConstantWeilUnitProof

universe d r
open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency.types false

section
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)
private def regularExtensionApp (U : Cᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheaf.{v, c, r} α
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).obj U ≅
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)).val.obj U := by
  let : Algebra (R.obj.obj U) (S.obj.obj U) := (α.hom.app U).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj U)
    (S.obj.obj U) (S.obj.obj U)).toModuleIso
private theorem regularExtensionApp_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : R.obj.obj U) :
    (regularExtensionApp α U).hom (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x) =
      s * α.hom.app U x := by
  change α.hom.app U x * s = s * α.hom.app U x
  exact mul_comm _ _
private def regularExtensionPresheafIso :
    SheafOfModules.changeOfRingsPresheaf.{v, c, r} α
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)).val := by
  refine PresheafOfModules.isoMk (regularExtensionApp α) ?_
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s x =>
    change (regularExtensionApp α V).hom
      (SheafOfModules.changeOfRingsMap.{v, c, r} α _ f _) =
        S.obj.map f ((regularExtensionApp α U).hom _)
    erw [regularExtensionApp_tmul,
      Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{v, c, r} α _ f),
      regularExtensionApp_tmul, map_mul]
    congr 1
    exact ConcreteCategory.congr_hom (α.hom.naturality f) x
private def identityRestrictionIso
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) :
    M.val ≅ (PresheafOfModules.restrictScalars (𝟙 _)).obj M.val :=
  PresheafOfModules.isoMk (fun U ↦ {
    hom := ModuleCat.ofHom
      { toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    inv := ModuleCat.ofHom
      { toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl } }) (by intros; ext; rfl)
attribute [local irreducible] identityRestrictionIso regularExtensionPresheafIso
  PresheafOfModules.sheafificationAdjunction

-- Elaborating the sheafification comparison traverses the coefficient transports.
private def regularExtensionIso :
    SheafOfModules.changeOfRings.{v, c, r} α
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S) :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso
    (regularExtensionPresheafIso α ≪≫ identityRestrictionIso (S := S) _) ≪≫
      (asIso (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)).counit).app
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
private theorem regularExtensionIso_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : R.obj.obj U) :
    (regularExtensionIso α).hom.val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf.{v, c, r} α
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).presheaf).app U
          (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x)) = s * α.hom.app U x := by
  let M := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)
  let e := regularExtensionPresheafIso α ≪≫ identityRestrictionIso M
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)
  have hn := adj.unit.naturality e.hom
  have h := congrArg (fun k ↦ k.app U
    (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x)) hn
  have hc := congrArg (fun k ↦ k.app U (s * α.hom.app U x))
    (adj.right_triangle_components M)
  change (regularExtensionIso α).hom.val.app U _ = _
  change (adj.counit.app M).val.app U
    (((PresheafOfModules.sheafification (𝟙 _)).map e.hom).val.app U _) = _
  -- The sheafification unit is the canonical toSheafify map.
  have hu : ∀ P : PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj,
      ∀ z : P.obj U, (adj.unit.app P).app U z =
        (toSheafify J P.presheaf).app U z := by
    intro P z
    unfold adj PresheafOfModules.sheafificationAdjunction
    rfl
  change (adj.unit.app ((PresheafOfModules.restrictScalars (𝟙 _)).obj M.val)).app U
      (e.hom.app U (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x)) =
    (((PresheafOfModules.sheafification (𝟙 _)).map e.hom).val.app U)
      ((adj.unit.app _).app U (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x)) at h
  rw [hu, hu] at h
  rw [← h]
  have he : e.hom.app U (s ⊗ₜ[R.obj.obj U,(α.hom.app U).hom] x) =
      s * α.hom.app U x := by
    change (identityRestrictionIso M).hom.app U
      ((regularExtensionPresheafIso α).hom.app U _) = _
    unfold identityRestrictionIso regularExtensionPresheafIso
    exact regularExtensionApp_tmul α U s x
  rw [he]
  change (adj.counit.app M).val.app U
    ((adj.unit.app ((PresheafOfModules.restrictScalars (𝟙 _)).obj M.val)).app U
      (s * α.hom.app U x)) = s * α.hom.app U x at hc
  rw [hu] at hc
  exact hc
attribute [local irreducible] regularExtensionIso
end

section
variable {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
  [(SheafOfModules.pushforward.{r} φ).IsRightAdjoint]
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullbackUnit_one (V : C) :
    (SheafOfModules.pullbackObjUnitToUnit φ).val.app (op (F.obj V))
      ((((SheafOfModules.pullbackPushforwardAdjunction.{r} φ).unit.app
        (SheafOfModules.unit S)).val.app (op V)) (1 : S.obj.obj (op V))) =
      (1 : R.obj.obj (op (F.obj V))) := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ
  rw [Adjunction.homEquiv_unit] at h
  have he := congrArg (fun a ↦ a.val.app (op V) (1 : S.obj.obj (op V))) h
  change (SheafOfModules.pullbackObjUnitToUnit φ).val.app (op (F.obj V))
    ((((SheafOfModules.pullbackPushforwardAdjunction.{r} φ).unit.app
      (SheafOfModules.unit S)).val.app (op V)) (1 : S.obj.obj (op V))) =
        φ.hom.app (op V) 1 at he
  have hφ : φ.hom.app (op V) 1 = (1 : R.obj.obj (op (F.obj V))) := map_one _
  exact he.trans hφ
end

section ChainConstruction
attribute [local irreducible] unrestrictedIntegralReductionExistence limit

-- Explicit coefficient transports require a larger elaboration budget.
private theorem reduction_map_tensor (Y : Scheme.{u}) (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E Y n).map a).val.app U
      (unrestrictedIntegralTensorSection l E Y n M U s x) =
    unrestrictedIntegralTensorSection l E Y n N U s (a.val.app U x) := by
  let p := completedIntegralCommRingProjectionUnrestricted.{u, u} l E Y n
  let k : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p N :=
    { app := fun V ↦ (ModuleCat.extendScalars (p.hom.app V).hom).map (a.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u + 1, u + 1} p M a }
  have hn := toSheafify_naturality (ProEt.topology Y)
    ((PresheafOfModules.toPresheaf _).map k)
  have h := congrArg (fun η ↦ (η.app U).hom
    (s ⊗ₜ[_, (p.hom.app U).hom] x)) hn
  change _ = (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} p M a).val.app U _ at h
  change (toSheafify (ProEt.topology Y)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p N).presheaf).app U
    (((ModuleCat.extendScalars (p.hom.app U).hom).map (a.val.app U))
      (s ⊗ₜ[_, (p.hom.app U).hom] x)) = _ at h
  erw [ModuleCat.ExtendScalars.map_tmul] at h
  let ho := (unrestrictedIntegralReductionExistence.{u, u} l E Y n).choose_spec.choose
  have he : (unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map a =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} p M a ≫
        eqToHom (ho N).symm :=
    (unrestrictedIntegralReductionExistence.{u, u} l E Y n).choose_spec.choose_spec.choose a
  unfold unrestrictedIntegralTensorSection
  change ((eqToHom (ho M).symm ≫
    (unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map a).val.app U)
      ((toSheafify (ProEt.topology Y)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p M).presheaf).app U
          (s ⊗ₜ[_, (p.hom.app U).hom] x)) = _
  rw [he]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact congrArg ((eqToHom (ho N).symm).val.app U) h.symm

private def reducedUnitSections (Y : Scheme.{u}) (n : ℕ) :
    ((((unrestrictedIntegralFiniteComplex l E Y n).obj
      (constantWeilIntegralComplex l E Y)).X 0).sections) := by
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y
  let S := integralCoefficientCommRingSheaf.{u, u} l E Y n
  let p := completedIntegralCommRingProjectionUnrestricted.{u, u} l E Y n
  let M := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p M
  let s : P.sections := PresheafOfModules.sectionsMk
    (fun U ↦ (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (p.hom.app U).hom]
      (1 : R.obj.obj U)) (by
        intro U V f
        change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1} p M f _ = _
        erw [Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1} p M f)]
        simp only [map_one]
        congr 1
        change (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y).obj.map f 1 = 1
        exact map_one _)
  let a := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)).unit.app P
  let e := eqToHom
    ((unrestrictedIntegralReductionExistence.{u, u} l E Y n).choose_spec.choose M).symm
  let b := (unrestrictedIntegralReductionFunctor l E Y n).map
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv
  exact PresheafOfModules.sectionsMap b.val
    (PresheafOfModules.sectionsMap e.val (PresheafOfModules.sectionsMap a s))

private def pullbackUnitSections {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    (((constantWeilPullbackTower l E g).obj (op n)).X 0).sections := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT := hT.isTerminalObj (proEtaleBaseChange g) T
  let M := ((unrestrictedIntegralFiniteComplex l E Y n).obj
    (constantWeilIntegralComplex l E Y)).X 0
  let N := (integralOperationsLevelPullback l E g n).obj M
  let a := (coefficientProEtaleModuleAdjunction.{u, u} g
    (CommRingCat.of (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))))).unit.app M
  let t := PresheafOfModules.sectionsMap a.val (reducedUnitSections l E Y n)
  exact PresheafOfModules.sectionsMk
    (fun U ↦ N.val.map (hGT.from U.unop).op (t.val (op T))) (by
      intro U V f
      change N.val.map f (N.val.map (hGT.from U.unop).op _) = _
      rw [← PresheafOfModules.map_comp_apply]
      have he : (hGT.from U.unop).op ≫ f = (hGT.from V.unop).op := by
        apply Quiver.Hom.unop_inj
        exact hGT.hom_ext _ _
      rw [he])

private theorem pullbackUnitSections_base {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) (V : Y.ProEt) :
    (pullbackUnitSections l E g n).val (op ((proEtaleBaseChange g).obj V)) =
      integralOperationsPullbackGenerator l E g n
        (((unrestrictedIntegralFiniteComplex l E Y n).obj
          (constantWeilIntegralComplex l E Y)).X 0) V
        (constantWeilReducedUnitSection l E Y n V) := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT := hT.isTerminalObj (proEtaleBaseChange g) T
  let M := ((unrestrictedIntegralFiniteComplex l E Y n).obj
    (constantWeilIntegralComplex l E Y)).X 0
  let a := (coefficientProEtaleModuleAdjunction.{u, u} g
    (CommRingCat.of (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1))))).unit.app M
  have ht := (PresheafOfModules.sectionsMap a.val
    (reducedUnitSections l E Y n)).property (hT.from V).op
  change ((integralOperationsLevelPullback l E g n).obj M).val.map
    (hGT.from ((proEtaleBaseChange g).obj V)).op _ = _
  rw [show hGT.from ((proEtaleBaseChange g).obj V) =
    (proEtaleBaseChange g).map (hT.from V) from hGT.hom_ext _ _]
  simpa only [PresheafOfModules.sectionsMap, PresheafOfModules.sectionsMk,
    constantWeilReducedUnitSection, reducedUnitSections,
    integralOperationsPullbackGenerator] using! ht

private theorem regular_hom_ext (X : Scheme.{u})
    {K : CochainComplex (integralTowerModules l E X) ℤ}
    (T : X.ProEt) (hT : IsTerminal T)
    (a b : constantWeilIntegralComplex l E X ⟶ K)
    (h : (a.f 0).val.app (op T) (constantWeilUnitSection l E X T) =
      (b.f 0).val.app (op T) (constantWeilUnitSection l E X T)) : a = b := by
  apply HomologicalComplex.from_single_hom_ext
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))
  apply (cancel_epi e.inv).1
  apply (SheafOfModules.unitHomEquiv _).injective
  apply PresheafOfModules.sections_ext
  intro U
  have ha := (SheafOfModules.unitHomEquiv _ (e.inv ≫ a.f 0)).property
    (hT.from U.unop).op
  have hb := (SheafOfModules.unitHomEquiv _ (e.inv ≫ b.f 0)).property
    (hT.from U.unop).op
  change (SheafOfModules.unitHomEquiv _ (e.inv ≫ a.f 0)).val (op T) =
    (SheafOfModules.unitHomEquiv _ (e.inv ≫ b.f 0)).val (op T) at h
  exact ha.symm.trans ((congrArg ((K.X 0).val.map (hT.from U.unop).op) h).trans hb)

private def pullbackUnitLevel {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    constantWeilIntegralComplex l E X ⟶ (constantWeilPullbackTower l E g).obj (op n) := by
  apply HomologicalComplex.mkHomFromSingle
    ((SheafOfModules.unitHomEquiv _).symm (pullbackUnitSections l E g n))
  intro k hk
  have hzero : IsZero (((constantWeilPullbackTower l E g).obj (op n)).X k) := by
    apply Functor.map_isZero (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)))
    apply Functor.map_isZero (integralOperationsLevelPullback l E g n)
    apply Functor.map_isZero (unrestrictedIntegralReductionFunctor l E Y n)
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by
      change 0 + 1 = k at hk
      omega)
  exact hzero.eq_of_tgt _ _

private theorem pullbackUnitLevel_generator {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) (V : Y.ProEt) :
    ((pullbackUnitLevel l E g n).f 0).val.app (op ((proEtaleBaseChange g).obj V))
      (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
    integralOperationsPullbackGenerator l E g n
      (((unrestrictedIntegralFiniteComplex l E Y n).obj
        (constantWeilIntegralComplex l E Y)).X 0) V
      (constantWeilReducedUnitSection l E Y n V) := by
  rw [← pullbackUnitSections_base l E g n V]
  have h := congrArg
    (fun s ↦ s.val (op ((proEtaleBaseChange g).obj V)))
    ((SheafOfModules.unitHomEquiv _).apply_symm_apply (pullbackUnitSections l E g n))
  dsimp only [pullbackUnitLevel]
  rw [HomologicalComplex.mkHomFromSingle_f]
  change (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))).inv ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))).hom ≫
    (SheafOfModules.unitHomEquiv _).symm (pullbackUnitSections l E g n)).val.app
      (op ((proEtaleBaseChange g).obj V)))
      (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op ((proEtaleBaseChange g).obj V))) = _
  simpa only [Iso.inv_hom_id_assoc, SheafOfModules.unitHomEquiv_apply_coe] using! h

private theorem reducedUnit_transition (Y : Scheme.{u}) (n : ℕ) (V : Y.ProEt) :
    (((unrestrictedIntegralTransition l E Y n).app
      (constantWeilIntegralComplex l E Y)).f 0).val.app (op V)
        (constantWeilReducedUnitSection l E Y (n + 1) V) =
      constantWeilReducedUnitSection l E Y n V := by
  unfold constantWeilReducedUnitSection
  simp only [reduction_map_tensor]
  change (((unrestrictedIntegralTransition l E Y n).app
    (constantWeilIntegralComplex l E Y)).f 0).val.app (op V)
      (unrestrictedIntegralTensorSection l E Y (n + 1)
        ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
        (constantWeilUnitSection l E Y V)) =
    unrestrictedIntegralTensorSection l E Y n
      ((constantWeilIntegralComplex l E Y).X 0) (op V) 1
      (constantWeilUnitSection l E Y V)
  have h := (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec
    (constantWeilIntegralComplex l E Y) 0 (op V) 1 (constantWeilUnitSection l E Y V)
  simpa only [map_one, unrestrictedIntegralTransition] using h

private theorem pullbackUnitLevel_transition {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    pullbackUnitLevel l E g (n + 1) ≫
      (integralOperationsPullbackTransition l E g n).app (constantWeilIntegralComplex l E Y) =
    pullbackUnitLevel l E g n := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply regular_hom_ext l E X ((proEtaleBaseChange g).obj T)
    (hT.isTerminalObj (proEtaleBaseChange g) T)
  change (((integralOperationsPullbackTransition l E g n).app
    (constantWeilIntegralComplex l E Y)).f 0).val.app _
    (((pullbackUnitLevel l E g (n + 1)).f 0).val.app _ _) = _
  simp only [pullbackUnitLevel_generator]
  have ht := (integralOperationsPullbackTransition_existsUnique l E g n).exists.choose_spec
    (constantWeilIntegralComplex l E Y) 0 T (constantWeilReducedUnitSection l E Y (n + 1) T)
  exact ht.trans (by
    rw [reducedUnit_transition]
    exact (pullbackUnitLevel_generator l E g n T).symm)

private def pullbackUnitProduct {X Y : Scheme.{u}} (g : X ⟶ Y) :
    constantWeilIntegralComplex l E X ⟶
      ∏ᶜ fun n ↦ (constantWeilPullbackTower l E g).obj (op n) :=
  Pi.lift (pullbackUnitLevel l E g)

private theorem pullbackUnitProduct_zero {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullbackUnitProduct l E g ≫ constantWeilPullbackRoosEndomorphism l E g = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [pullbackUnitProduct, constantWeilPullbackRoosEndomorphism,
    towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.comp_id, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc,
    zero_comp]
  apply sub_eq_zero.mpr
  change pullbackUnitLevel l E g n = pullbackUnitLevel l E g (n + 1) ≫
    (((Functor.ofOpSequence (integralOperationsPullbackTransition l E g)).map
      (homOfLE (Nat.le_succ n)).op).app (constantWeilIntegralComplex l E Y))
  rw [Functor.ofOpSequence_map_homOfLE_succ, pullbackUnitLevel_transition]

private def chainUnitCandidate {X Y : Scheme.{u}} (g : X ⟶ Y) :
    constantWeilIntegralComplex l E X ⟶
      (integralOperationsPullbackComplexFunctor l E g).obj
        (constantWeilIntegralComplex l E Y) :=
  CochainComplex.mappingCocone.lift
    (constantWeilPullbackRoosEndomorphism l E g) (pullbackUnitProduct l E g) 0
    (by simp [pullbackUnitProduct_zero])

private theorem chainUnitCandidate_generators {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) (V : Y.ProEt) :
    (((chainUnitCandidate l E g).f 0 ≫
      (CochainComplex.mappingCocone.fst
        (constantWeilPullbackRoosEndomorphism l E g)).f 0 ≫
      (Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n).f 0).val.app
        (op ((proEtaleBaseChange g).obj V)))
      (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
    integralOperationsPullbackGenerator l E g n
      (((unrestrictedIntegralFiniteComplex l E Y n).obj
        (constantWeilIntegralComplex l E Y)).X 0) V
      (constantWeilReducedUnitSection l E Y n V) := by
  simp only [chainUnitCandidate, CochainComplex.mappingCocone.lift_f_fst_f_assoc]
  have h := congrArg (fun a ↦ a.f 0)
    (Pi.lift_comp_π (pullbackUnitLevel l E g) n)
  change ((pullbackUnitProduct l E g).f 0 ≫ _).val.app _ _ = _
  rw [← HomologicalComplex.comp_f]
  change (((Pi.lift (pullbackUnitLevel l E g) ≫ Pi.π _ n).f 0).val.app _) _ = _
  rw [Pi.lift_comp_π]
  exact pullbackUnitLevel_generator l E g n V

private theorem cocone_hom_ext {A : Type*} [Category A] [Preadditive A]
    [HasBinaryBiproducts A] {P Q K : CochainComplex A ℤ} (φ : P ⟶ Q)
    (a b : K ⟶ CochainComplex.mappingCocone φ)
    (h₁ : a ≫ CochainComplex.mappingCocone.fst φ =
      b ≫ CochainComplex.mappingCocone.fst φ)
    (h₂ : ∀ i : ℤ, a.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1)
      (by omega) = b.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1)
      (by omega)) : a = b := by
  ext i
  have h := congrArg (fun f ↦ f.f i) h₁
  simp only [HomologicalComplex.comp_f] at h
  calc
    a.f i = a.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = a.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
          (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
          (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      rw [CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)]
    _ = b.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
          (CochainComplex.mappingCocone.inl φ).v i i (by omega) +
        (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
          (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, h, h₂ i]
    _ = b.f i := by rw [CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega),
      Category.comp_id]

private theorem normalized_chainUnit_unique {X Y : Scheme.{u}} (g : X ⟶ Y)
    (η : constantWeilIntegralComplex l E X ⟶
      (integralOperationsPullbackComplexFunctor l E g).obj
        (constantWeilIntegralComplex l E Y))
    (hη : (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E g)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange g).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E g)).v i (i - 1) (by omega) = 0)) :
    η = chainUnitCandidate l E g := by
  have hfst : η ≫ CochainComplex.mappingCocone.fst
      (constantWeilPullbackRoosEndomorphism l E g) = pullbackUnitProduct l E g := by
    apply Pi.hom_ext
    intro n
    let T : Y.ProEt := ProEt.mk (𝟙 Y)
    let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
    apply regular_hom_ext l E X ((proEtaleBaseChange g).obj T)
      (hT.isTerminalObj (proEtaleBaseChange g) T)
    simp only [HomologicalComplex.comp_f]
    rw [Category.assoc]
    rw [hη.1 n T]
    change _ = ((pullbackUnitProduct l E g ≫ Pi.π _ n).f 0).val.app _ _
    change _ = (((Pi.lift (pullbackUnitLevel l E g) ≫ Pi.π _ n).f 0).val.app _) _
    rw [Pi.lift_comp_π]
    exact (pullbackUnitLevel_generator l E g n T).symm
  apply cocone_hom_ext (constantWeilPullbackRoosEndomorphism l E g)
  · simpa only [chainUnitCandidate, CochainComplex.mappingCocone.lift_fst] using hfst
  · intro i
    simpa only [chainUnitCandidate, CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v] using hη.2 i

end ChainConstruction

section LevelIsoProof
attribute [local irreducible] unrestrictedIntegralReductionExistence limit
private def finiteRegularIso (Y : Scheme.{u}) (n : ℕ) :
    (unrestrictedIntegralReductionFunctor.{u, u} l E Y n).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)) ≅
    SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n) :=
  eqToIso ((unrestrictedIntegralReductionExistence.{u, u} l E Y n).choose_spec.choose _) ≪≫
    regularExtensionIso (completedIntegralCommRingProjectionUnrestricted.{u, u} l E Y n)
private theorem finiteRegularIso_one (Y : Scheme.{u}) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    (finiteRegularIso l E Y n).hom.val.app U
      (unrestrictedIntegralTensorSection l E Y n
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)) U 1
          (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y).obj.obj U)) =
        (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj U) := by
  let p := completedIntegralCommRingProjectionUnrestricted.{u, u} l E Y n
  let M := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)
  let ho := (unrestrictedIntegralReductionExistence.{u, u} l E Y n).choose_spec.choose M
  let z := (toSheafify (ProEt.topology Y)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} p M).presheaf).app U
      ((1 : (integralCoefficientCommRingSheaf.{u, u} l E Y n).obj.obj U)
        ⊗ₜ[(completedIntegralCommRingSheafUnrestricted.{u, u} l E Y).obj.obj U,
          (p.hom.app U).hom]
          (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y).obj.obj U))
  have hc : eqToHom ho.symm ≫ (finiteRegularIso l E Y n).hom =
      (regularExtensionIso p).hom := by
    change eqToHom ho.symm ≫ (eqToHom ho ≫ _) = _
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rfl
  change ((eqToHom ho.symm ≫ (finiteRegularIso l E Y n).hom).val.app U) z = _
  rw [hc]
  change (regularExtensionIso p).hom.val.app U z = _
  simpa only [map_one, mul_one] using! regularExtensionIso_tmul p U 1 1
attribute [local irreducible] finiteRegularIso

private def finiteSingleRegularIso (Y : Scheme.{u}) (n : ℕ) :
    (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj (constantWeilIntegralComplex l E Y) ≅
      (CochainComplex.singleFunctor (integralOperationsFiniteModules.{u, u} l E Y n) 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (unrestrictedIntegralReductionFunctor.{u, u} l E Y n) (.up ℤ) 0).app _ ≪≫
      (CochainComplex.singleFunctor _ 0).mapIso (finiteRegularIso l E Y n)
private def finitePullbackRegularIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (integralOperationsLevelPullback.{u, u} l E g n).obj
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) ≅
        SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E X n) := by
  have : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  have : (proEtaleBaseChange g).IsEquivalence :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial).isEquivalence_right_of_isEquivalence_left
  have : (proEtaleBaseChange g).Final := inferInstance
  let A := CommRingCat.of (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E (n + 1)))
  let φ : integralCoefficientSheaf.{u, u} l E Y n ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf.{u, u} l E X n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} g A
  exact asIso (SheafOfModules.pullbackObjUnitToUnit φ)
private def quotientUnit (X : Scheme.{u}) (n : ℕ) : integralTowerModules l E X :=
  (SheafOfModules.restrictScalars
    (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n))).obj
      (SheafOfModules.unit ((integralCoefficientSheafSystem.{u, u} l E X).obj (op n)))
private def pullbackLevelRegularIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    (constantWeilPullbackTower l E g).obj (op n) ≅
      (CochainComplex.singleFunctor (integralTowerModules l E X) 0).obj
        (quotientUnit l E X n) := by
  let F := integralOperationsLevelPullback.{u, u} l E g n
  let R := SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))
  exact (R.mapHomologicalComplex (.up ℤ)).mapIso
    ((F.mapHomologicalComplex (.up ℤ)).mapIso (finiteSingleRegularIso l E Y n) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _ ≪≫
      (CochainComplex.singleFunctor _ 0).mapIso (finitePullbackRegularIso l E g n)) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app _
private theorem finiteSingleRegularIso_one (Y : Scheme.{u}) (n : ℕ) (U : Y.ProEtᵒᵖ) :
    ((finiteSingleRegularIso l E Y n).hom.f 0).val.app U
      (constantWeilReducedUnitSection l E Y n U.unop) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).inv.val.app U
        (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj U) := by
  have hf : (finiteSingleRegularIso l E Y n).hom.f 0 =
      (unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))).hom ≫
      (finiteRegularIso l E Y n).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).inv := by
    simp only [finiteSingleRegularIso, Iso.trans_hom, Functor.mapIso_hom,
      HomologicalComplex.comp_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hf]
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).inv.val.app U)
    ((finiteRegularIso l E Y n).hom.val.app U
      (((unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))).hom).val.app
            U
            (constantWeilReducedUnitSection l E Y n U.unop))) = _
  have hc :
      (((unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))).hom).val.app
            U)
        (constantWeilReducedUnitSection l E Y n U.unop) =
      unrestrictedIntegralTensorSection l E Y n
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))
          U 1 (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y).obj.obj U) := by
    change (((unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))).inv ≫
      (unrestrictedIntegralReductionFunctor.{u, u} l E Y n).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit
            (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))).hom).val.app
            U) _ = _
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id]
    erw [CategoryTheory.Functor.map_id]
    rfl
  rw [hc]
  exact congrArg
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).inv.val.app U)
    (finiteRegularIso_one l E Y n U)
attribute [local irreducible] finiteSingleRegularIso

private theorem finitePullbackRegularIso_generator {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) (V : Y.ProEt) :
    (finitePullbackRegularIso l E g n).hom.val.app (op ((proEtaleBaseChange g).obj V))
      (integralOperationsPullbackGenerator l E g n
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) V
          (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj (op V))) =
      (1 : (integralCoefficientSheaf.{u, u} l E X n).obj.obj
        (op ((proEtaleBaseChange g).obj V))) := by
  let A := CommRingCat.of (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E (n + 1)))
  let φ : integralCoefficientSheaf.{u, u} l E Y n ⟶
      ((proEtaleBaseChange g).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj
          (integralCoefficientSheaf.{u, u} l E X n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} g A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} g A
  exact pullbackUnit_one φ V
private theorem pullbackLevelRegularIso_one {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) (V : Y.ProEt) :
    ((pullbackLevelRegularIso l E g n).hom.f 0).val.app
      (op ((proEtaleBaseChange g).obj V))
      (integralOperationsPullbackGenerator l E g n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj
          (constantWeilIntegralComplex l E Y)).X 0) V
        (constantWeilReducedUnitSection l E Y n V)) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientUnit l E X n)).inv.val.app
      (op ((proEtaleBaseChange g).obj V))
        (1 : (integralCoefficientSheaf.{u, u} l E X n).obj.obj
          (op ((proEtaleBaseChange g).obj V))) := by
  let F := integralOperationsLevelPullback.{u, u} l E g n
  let A := CommRingCat.of (ULift.{u + 1, u}
    (Padic.coefficientExtensionRing l E (n + 1)))
  let a := (finiteSingleRegularIso l E Y n).hom.f 0 ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).hom
  have hn := (coefficientProEtaleModuleAdjunction.{u, u} g A).unit.naturality a
  have h := congrArg (fun b ↦ b.val.app (op V)
    (constantWeilReducedUnitSection l E Y n V)) hn
  change integralOperationsPullbackGenerator l E g n
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n)) V
        (a.val.app (op V) (constantWeilReducedUnitSection l E Y n V)) =
    ((F.map a).val.app (op ((proEtaleBaseChange g).obj V)))
      (integralOperationsPullbackGenerator l E g n _ V
        (constantWeilReducedUnitSection l E Y n V)) at h
  have ha : a.val.app (op V) (constantWeilReducedUnitSection l E Y n V) =
      (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj (op V)) := by
    change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))).hom.val.app (op V))
      (((finiteSingleRegularIso l E Y n).hom.f 0).val.app (op V) _) = _
    rw [finiteSingleRegularIso_one]
    have he := congrArg (fun f ↦ f.val.app (op V))
      (Iso.inv_hom_id (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E Y n))))
    have he' := ConcreteCategory.congr_hom he
      (1 : (integralCoefficientSheaf.{u, u} l E Y n).obj.obj (op V))
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using! he'
  rw [ha] at h
  let R := SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n))
  have hf : (pullbackLevelRegularIso l E g n).hom.f 0 =
      R.map (F.map a ≫ (finitePullbackRegularIso l E g n).hom) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientUnit l E X n)).inv := by
    simp only [pullbackLevelRegularIso, Iso.trans_hom, Functor.mapIso_hom,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
    dsimp only [R, F, a]
    simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [hf]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientUnit l E X n)).inv.val.app
    (op ((proEtaleBaseChange g).obj V))
      ((finitePullbackRegularIso l E g n).hom.val.app _ ((F.map a).val.app _ _)) = _
  rw [← h, finitePullbackRegularIso_generator]
attribute [local irreducible] finitePullbackRegularIso pullbackLevelRegularIso

private theorem pullbackLevelRegularIso_projection {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    pullbackUnitLevel l E g n ≫ (pullbackLevelRegularIso l E g n).hom =
      (CochainComplex.singleFunctor _ 0).map (constantCoefficientProjection l E X n) := by
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  apply regular_hom_ext l E X ((proEtaleBaseChange g).obj T)
    (hT.isTerminalObj (proEtaleBaseChange g) T)
  change ((pullbackLevelRegularIso l E g n).hom.f 0).val.app _
    (((pullbackUnitLevel l E g n).f 0).val.app _ _) = _
  rw [pullbackUnitLevel_generator, pullbackLevelRegularIso_one]
  change _ = (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (quotientUnit l E X n)).inv.val.app _
      ((constantCoefficientProjection l E X n).val.app _
        (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X))).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X))).inv).val.app
              _
              (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj _)))
  simp only [Iso.hom_inv_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]
  congr 1
  change 1 = (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n).hom.app _ 1 * 1
  simp only [map_one, mul_one]

end LevelIsoProof

section CoefficientTowerProof
private def quotientProjection (X : Scheme.{u}) (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) ⟶
      quotientUnit l E X n := constantCoefficientProjection l E X n
private theorem quotientProjection_apply (X : Scheme.{u}) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj U) :
    (quotientProjection l E X n).val.app U x =
      (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app U x := by
  change (completedIntegralCommRingProjectionUnrestricted l E X n).hom.app U x * 1 = _
  exact mul_one _
private theorem coefficientProjection_step (X : Scheme.{u}) (n : ℕ) :
    limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op (n + 1)) ≫
      integralCoefficientSheafTransition.{u, u} l E X n =
        limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n) := by
  simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
    using limit.w (integralCoefficientSheafSystem.{u, u} l E X) (homOfLE n.le_succ).op
private def quotientStep (X : Scheme.{u}) (n : ℕ) :
    quotientUnit l E X (n + 1) ⟶ quotientUnit l E X n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (quotientUnit l E X (n + 1)).val.obj U)
        (Y := (quotientUnit l E X n).val.obj U)
        { toFun := (integralCoefficientSheafTransition.{u, u} l E X n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change ((integralCoefficientSheafSystem.{u, u} l E X).obj (op (n + 1))).obj.obj U at x
            let t : ((integralCoefficientSheafSystem.{u, u} l E X).obj
                (op (n + 1))).obj.obj U →+*
                ((integralCoefficientSheafSystem.{u, u} l E X).obj (op n)).obj.obj U :=
              ((integralCoefficientSheafTransition.{u, u} l E X n).hom.app U).hom
            change t ((limit.π (integralCoefficientSheafSystem.{u, u} l E X)
              (op (n + 1))).hom.app U r * x) =
                (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app U r * t x
            rw [map_mul]
            congr 1
            exact ConcreteCategory.congr_hom
              (congrArg (fun a : completedIntegralCoefficientSheafUnrestricted.{u, u} l E X ⟶
                  integralCoefficientSheaf.{u, u} l E X n ↦ a.hom.app U)
                (coefficientProjection_step l E X n)) r }
      naturality := by
        intro U V f
        ext x
        exact ConcreteCategory.congr_hom
          ((integralCoefficientSheafTransition.{u, u} l E X n).hom.naturality f) x }
private theorem quotientProjection_step (X : Scheme.{u}) (n : ℕ) :
    quotientProjection l E X (n + 1) ≫ quotientStep l E X n =
      quotientProjection l E X n := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, quotientProjection_apply]
  change (integralCoefficientSheafTransition.{u, u} l E X n).hom.app U
      ((limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op (n + 1))).hom.app U x) =
    (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app U x
  exact ConcreteCategory.congr_hom
    (congrArg (fun a : completedIntegralCoefficientSheafUnrestricted.{u, u} l E X ⟶
                  integralCoefficientSheaf.{u, u} l E X n ↦ a.hom.app U)
      (coefficientProjection_step l E X n)) x
private def quotientDiagram (X : Scheme.{u}) : ℕᵒᵖ ⥤ integralTowerModules l E X :=
  Functor.ofOpSequence (quotientStep l E X)
private def quotientCone (X : Scheme.{u}) : Cone (quotientDiagram l E X) where
  pt := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
  π := NatTrans.ofOpSequence (quotientProjection l E X) (by
    intro n
    simp only [Functor.const_obj_map, quotientDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (quotientProjection_step l E X n).symm)
private theorem quotientProjection_locallySurjective (X : Scheme.{u}) (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology X)
      (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom := by
  let J := ProEt.topology X
  let B := CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
  let η := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj B)
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  have : J.WEqualsLocallyBijective CommRingCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : Presheaf.IsLocallySurjective J η := by infer_instance
  refine ⟨fun {U} s ↦ J.superset_covering ?_ (Presheaf.imageSieve_mem J η s)⟩
  intro V f hf
  obtain ⟨x, hx⟩ := hf
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.down
  have hxa : x = ULift.up ((Ideal.Quotient.mk _) a) := ULift.ext ha.symm
  subst x
  let A := CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
  let b := (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj A)).app (op V) (ULift.up a)
  refine ⟨(integralConstantToCompletionOfUniverses.{u, u} l E X).hom.app (op V) b, ?_⟩
  have hπ := limit.lift_π (integralConstantConeOfUniverses.{u, u} l E X) (op n)
  have hb := congrArg (fun f ↦ f.hom.app (op V) b) hπ
  change (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app (op V)
    ((integralConstantToCompletionOfUniverses.{u, u} l E X).hom.app (op V) b) = _
  change (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app (op V)
    ((integralConstantToCompletionOfUniverses.{u, u} l E X).hom.app (op V) b) = _ at hb
  rw [hb]
  change ((integralConstantQuotientOfUniverses.{u, u} l E X n).hom.app (op V)) b = _
  let q : A ⟶ B := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
        (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom))
  have hn := congrArg (fun f ↦ (f.app (op V)).hom (ULift.up a))
    (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map q))
  exact hn.symm.trans hx
private theorem quotientProjection_epi (X : Scheme.{u}) (n : ℕ) :
    Epi (quotientProjection l E X n) := by
  let F := SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)
  let g := F.map (quotientProjection l E X n)
  have hlocal := quotientProjection_locallySurjective l E X n
  have : Sheaf.IsLocallySurjective g := by
    constructor
    intro U s
    have he : Presheaf.imageSieve g.hom s =
        Presheaf.imageSieve
          (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom s := by
      ext V f
      change (∃ x, g.hom.app (op V) x = _) ↔ ∃ x,
        (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app (op V) x = _
      simp only [show ∀ x, g.hom.app (op V) x =
        (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom.app (op V) x from
          quotientProjection_apply l E X n (op V)]
      rfl
    rw [he]
    exact Presheaf.imageSieve_mem (ProEt.topology X)
      (limit.π (integralCoefficientSheafSystem.{u, u} l E X) (op n)).hom s
  have : Epi g := Sheaf.epi_of_isLocallySurjective g
  exact F.epi_of_epi_map inferInstance
private theorem quotientStep_epi (X : Scheme.{u}) (n : ℕ) : Epi (quotientStep l E X n) := by
  have := quotientProjection_epi l E X n
  exact epi_of_epi_fac (quotientProjection_step l E X n)
private def quotientConeIsLimit (X : Scheme.{u}) : IsLimit (quotientCone l E X) := by
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects
    (forget₂ (ModuleCat.{u + 1}
      ((completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj U)) AddCommGrpCat)
  let F := quotientDiagram l E X ⋙
    SheafOfModules.evaluation (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) U ⋙
      forget₂ _ AddCommGrpCat
  let T := sheafToPresheaf (ProEt.topology X) RingCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.ProEtᵒᵖ RingCat.{u + 1}).obj U ⋙
      forget₂ RingCat AddCommGrpCat
  let G := integralCoefficientSheafSystem.{u, u} l E X ⋙ T
  let α : F ⟶ G := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    ext x
    simp only [F, G, T, quotientDiagram, integralCoefficientSheafSystem,
      Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
      Category.id_comp, Category.comp_id]
    rfl)
  let β : G ⟶ F := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    ext x
    simp only [F, G, T, quotientDiagram, integralCoefficientSheafSystem,
      Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
      Category.id_comp, Category.comp_id]
    rfl)
  let eα : F ≅ G :=
    { hom := α
      inv := β
      hom_inv_id := by
        ext n x
        simp [α, β]
      inv_hom_id := by
        ext n x
        simp [α, β] }
  let c := (forget₂ (ModuleCat.{u + 1}
    ((completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj U)) AddCommGrpCat).mapCone
      ((PresheafOfModules.evaluation
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj U).mapCone
          ((SheafOfModules.forget _).mapCone (quotientCone l E X)))
  apply (IsLimit.postcomposeHomEquiv eα c).toFun
  exact (isLimitOfPreserves T
    (limit.isLimit (integralCoefficientSheafSystem.{u, u} l E X))).ofIsoLimit
    (Cone.ext (by
      change (forget₂ RingCat AddCommGrpCat).obj
        ((limit (integralCoefficientSheafSystem.{u, u} l E X)).obj.obj U) ≅ _
      exact Iso.refl _) (by
      intro n
      ext x
      change (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj U at x
      exact (quotientProjection_apply l E X n.unop U x).symm))

end CoefficientTowerProof

section FinalAssemblyProof
attribute [local irreducible] finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel
  unrestrictedIntegralReductionExistence limit
private theorem singleTower_epi {A : Type c} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasCountableProducts (CochainComplex A ℤ)]
    (M : ℕᵒᵖ ⥤ A)
    (h : Epi (towerTransitionEndomorphism (K := fun n ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)))
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (e : F ≅ M ⋙ CochainComplex.singleFunctor A 0) :
    Epi (towerTransitionEndomorphism (K := fun n ↦ F.obj (op n))
      (WeilConjectures.integralOperationsTowerStep F)) := by
  let : Epi (towerTransitionEndomorphism (K := fun n ↦ M.obj (op n))
    (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)) := h
  let S := HomologicalComplex.single A (.up ℤ) 0
  let t := fun n : ℕ ↦ M.map (homOfLE n.le_succ).op
  have : Epi (S.map (towerTransitionEndomorphism (K := fun n ↦ M.obj (op n)) t)) := inferInstance
  have : Epi (piComparison S (fun n ↦ M.obj (op n)) ≫
      towerTransitionEndomorphism (K := fun n ↦ S.obj (M.obj (op n)))
        (fun n ↦ S.map (t n))) := by
    rw [← AlgebraicGeometry.ProEtale.map_transition]
    infer_instance
  have : Epi (towerTransitionEndomorphism (K := fun n ↦ S.obj (M.obj (op n)))
        (fun n ↦ S.map (t n))) :=
    epi_of_epi (piComparison S (fun n ↦ M.obj (op n))) _
  let p := Limits.Pi.map (fun n ↦ e.hom.app (op n))
  have (n : ℕ) : IsIso (e.hom.app (op n)) := inferInstance
  have : IsIso p := by dsimp [p]; infer_instance
  have he : towerTransitionEndomorphism (K := fun n ↦ F.obj (op n))
      (WeilConjectures.integralOperationsTowerStep F) ≫ p =
      p ≫ towerTransitionEndomorphism (K := fun n ↦ S.obj (M.obj (op n)))
        (fun n ↦ S.map (t n)) :=
    WeilConjectures.integralOperationsRoos_square e.hom
  have : Epi (towerTransitionEndomorphism (K := fun n ↦ F.obj (op n))
      (WeilConjectures.integralOperationsTowerStep F) ≫ p) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso _ p).1 inferInstance

private def compatibleTowerIso {B : Type c} [Category.{v} B]
    (F G : ℕᵒᵖ ⥤ B) (Z : B)
    (a : ∀ n : ℕ, Z ⟶ F.obj (op n))
    (b : ∀ n : ℕ, Z ⟶ G.obj (op n))
    (ha : ∀ n, a (n + 1) ≫ F.map (homOfLE n.le_succ).op = a n)
    (hb : ∀ n, b (n + 1) ≫ G.map (homOfLE n.le_succ).op = b n)
    (e : ∀ n, F.obj (op n) ≅ G.obj (op n))
    (he : ∀ n, a n ≫ (e n).hom = b n)
    (h : ∀ n, Epi (b n)) : F ≅ G := by
  let α : F ⟶ G := NatTrans.ofOpSequence (fun n ↦ (e n).hom) (by
    intro n
    have : Epi (a (n + 1) ≫ (e (n + 1)).hom) := by rw [he]; exact h _
    have : Epi (a (n + 1)) := (epi_comp_iff_of_isIso _ (e (n + 1)).hom).1 inferInstance
    apply (cancel_epi (a (n + 1))).1
    rw [← Category.assoc, ha, he, ← Category.assoc, he, hb])
  have (n : ℕᵒᵖ) : IsIso (α.app n) := by
    change IsIso (e n.unop).hom
    infer_instance
  exact @asIso _ _ _ _ α (NatIso.isIso_of_isIso_app α)

private def pullbackRegularTowerIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    constantWeilPullbackTower l E g ≅ quotientDiagram l E X ⋙
      CochainComplex.singleFunctor (integralTowerModules l E X) 0 := by
  let S := CochainComplex.singleFunctor (integralTowerModules l E X) 0
  have : PreservesFiniteColimits S :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (integralTowerModules l E X) (.up ℤ) 0))
  refine compatibleTowerIso _ _ (constantWeilIntegralComplex l E X)
    (pullbackUnitLevel l E g) (fun n ↦ S.map (quotientProjection l E X n))
    ?_ ?_ (pullbackLevelRegularIso l E g) ?_ ?_
  · intro n
    simpa only [constantWeilPullbackTower, integralOperationsPullbackTowerFunctor,
      Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ] using
        pullbackUnitLevel_transition l E g n
  · intro n
    change S.map (quotientProjection l E X (n + 1)) ≫
      S.map ((quotientDiagram l E X).map (homOfLE n.le_succ).op) = _
    rw [← S.map_comp]
    simpa only [quotientDiagram, Functor.ofOpSequence_map_homOfLE_succ] using
      congrArg S.map (quotientProjection_step l E X n)
  · intro n
    exact pullbackLevelRegularIso_projection l E g n
  · intro n
    have := quotientProjection_epi l E X n
    infer_instance
private def pullbackRegularCone {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Cone (constantWeilPullbackTower l E g) where
  pt := constantWeilIntegralComplex l E X
  π := NatTrans.ofOpSequence (pullbackUnitLevel l E g) (by
    intro n
    change 𝟙 _ ≫ pullbackUnitLevel l E g n =
      pullbackUnitLevel l E g (n + 1) ≫ _
    rw [Category.id_comp]
    simpa only [constantWeilPullbackTower, integralOperationsPullbackTowerFunctor,
      Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ] using
        (pullbackUnitLevel_transition l E g n).symm)
private def pullbackRegularConeIsLimit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsLimit (pullbackRegularCone l E g) := by
  let S := CochainComplex.singleFunctor (integralTowerModules l E X) 0
  haveI : PreservesFiniteColimits S :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (integralTowerModules l E X) (.up ℤ) 0))
  haveI : PreservesLimitsOfShape ℕᵒᵖ S :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (HomologicalComplex.single (integralTowerModules l E X) (.up ℤ) 0))
  let e := pullbackRegularTowerIso l E g
  apply (IsLimit.postcomposeHomEquiv e (pullbackRegularCone l E g)).toFun
  exact (isLimitOfPreserves S (quotientConeIsLimit l E X)).ofIsoLimit
    (Cone.ext (Iso.refl _) (by
      intro n
      simp only [Cone.postcompose_obj_π, NatTrans.comp_app, Iso.refl_hom, Category.id_comp]
      exact (pullbackLevelRegularIso_projection l E g n.unop).symm))
private theorem pullbackRoos_epi {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    Epi (constantWeilPullbackRoosEndomorphism l E g) := by
  let M := quotientDiagram l E X
  have ht (n : ℕ) : Epi (M.map (homOfLE n.le_succ).op) := by
    simpa only [M, quotientDiagram, Functor.ofOpSequence_map_homOfLE_succ]
      using quotientStep_epi l E X n
  have h := AlgebraicGeometry.ProEtale.milnor_epimorphic.{u, u, _} X
    (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X) M ht
  have : HasCountableProducts (CochainComplex (integralTowerModules l E X) ℤ) :=
    ⟨fun _ _ ↦ HomologicalComplex.instHasLimitsOfShape⟩
  exact singleTower_epi M h.1 _ (pullbackRegularTowerIso l E g)
private theorem chainUnitCandidate_quasiIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    QuasiIso (chainUnitCandidate l E g) := by
  let F := constantWeilPullbackTower l E g
  let P := Fan.mk (∏ᶜ fun n ↦ F.obj (op n)) (fun n ↦ Pi.π _ n)
  obtain ⟨hz, ⟨hk⟩⟩ := AlgebraicGeometry.ProEtale.tower_kernel F
    (pullbackRegularCone l E g) (pullbackRegularConeIsLimit l E g)
    P (productIsProduct _) (pullbackUnitProduct l E g)
    (constantWeilPullbackRoosEndomorphism l E g)
    (fun n ↦ Pi.lift_comp_π (pullbackUnitLevel l E g) n)
    (fun n ↦ (towerTransitionEndomorphism_eq_iff _ _).1 rfl n)
  let S := ShortComplex.mk (pullbackUnitProduct l E g)
    (constantWeilPullbackRoosEndomorphism l E g) hz
  have : Mono S.f := mono_of_isLimit_fork hk
  have : Epi S.g := pullbackRoos_epi l E g
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel hk }
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (by simp [S, pullbackUnitProduct_zero])

end FinalAssemblyProof

end ConstantWeilUnitProof

section NormalizedUnitUse
attribute [local irreducible] unrestrictedIntegralReductionExistence limit
  chainUnitCandidate pullbackUnitProduct pullbackUnitLevel

/-- The canonical comparison into the strict completed pullback is uniquely fixed by the
finite-level unit generators and by its zero shifted component. This is the inverse of
the desired derived structure map on the regular coefficient object.
Source: blueprint order 1510, clauses 1--3; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-constant-weil-structure).
Proof: at each finite level multiplication identifies reduction of the regular module
with the finite regular module, and its unit is 1 tensor 1. Apply the actual module
pullback adjunction unit. These generators are compatible with reductions by clause 1.
Their product is killed by 1-shift, so mappingCocone.lift with zero degree -1 component
gives the map. On an isomorphism, every site object is isomorphic to a base-change
object, where the prescribed generator generates the regular module. Thus the first
component is determined by the equations below. The zero second component and the two
cone projections determine the chain map uniquely. No cone filler is chosen. -/
theorem constantWeilChainUnit_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E g).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E g)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange g).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E g)).v i (i - 1) (by omega) = 0) := by
  refine ⟨chainUnitCandidate l E g, ⟨?_, ?_⟩, ?_⟩
  · intro n V
    exact chainUnitCandidate_generators l E g n V
  · intro i
    simp only [chainUnitCandidate, CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v]
  · intro η hη
    exact normalized_chainUnit_unique l E g η hη

/-- The uniquely normalized strict chain map, with real source and target complexes.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilChainUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (constantWeilChainUnit_existsUnique l E g).exists.choose

/-- The specified unit is a quasi-isomorphism.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure).
Proof: finite pullback takes the regular module to the regular module by the canonical
constant-ring comparison. The unit equations identify its tower with the finite
coefficient tower of X, with the actual quotient transitions. These are surjective
and their limit is the completed ring sheaf. Its Roos complex is therefore quasi-isomorphic
to that completed sheaf in degree zero. The normalized map above is precisely this
comparison. The empty scheme is allowed; the same calculation is vacuous there. -/
theorem constantWeilChainUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso (DerivedCategory.Q.map (constantWeilChainUnit l E g)) := by
  have he : constantWeilChainUnit l E g = chainUnitCandidate l E g :=
    normalized_chainUnit_unique l E g _
      (constantWeilChainUnit_existsUnique l E g).exists.choose_spec
  rw [he]
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (chainUnitCandidate_quasiIso l E g)

end NormalizedUnitUse

/-- Canonical derived integral coefficient structure: invert the strict unit, then use
the specified good-representative comparison of the recorded completed derived pullback.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralRoosComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralDerivedPullback l E g).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E g).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (constantWeilChainUnit l E g))
      (constantWeilChainUnit_isIso l E g)).symm

attribute [-instance] coefficientProEtaleModelBaseChange_isContinuous
  coefficientProEtaleModelUp_isContinuous in
/-- The regular module map induced by the completed coefficient comparison. On the small
model it is Mathlib's canonical pullback-of-unit map; transports are precomposition.
Source: blueprint order 1510, clauses 2--3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilTermwiseUnitMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isomorphismTermwiseModuleInverseImage g
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (constantWeilIntegralComparison l E g)).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (constantWeilIntegralComparison l E g).inv)).obj
        (SheafOfModules.unit
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (completedIntegralCommRingSheafUnrestricted l E Y)))) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (constantWeilIntegralComparison l E g).inv)).map
    ((proEtaleModuleFromModel
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E Y)))).map
      (SheafOfModules.pullbackObjUnitToUnit
        (F := proEtaleModelBaseChange g)
        (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
        (proEtaleModelRingUnit g (completedIntegralCommRingSheafUnrestricted l E Y))))

/-- The canonical unit map for restriction along the inverse coefficient isomorphism.
Source: blueprint order 1510, clauses 2--3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRestrictionUnitMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X) ⟶
      (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (constantWeilIntegralComparison l E g).inv)).obj
        (SheafOfModules.unit
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
              (completedIntegralCommRingSheafUnrestricted l E Y)))) :=
  let R' := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (completedIntegralCommRingSheafUnrestricted l E Y))
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : R'.obj.obj U))
      (fun {_ _} f ↦ map_one (R'.obj.map f).hom))

/-- The canonical module maps used for c_O_E are isomorphisms.
Source: blueprint order 1510, clauses 2--3 (blueprint: def-weil-constant-weil-structure).
Proof: on the small site models base change along an isomorphism is a final equivalence.
Mathlib's pullback-of-unit map is therefore invertible. Precomposition and restriction
preserve this. Restriction along the inverse coefficient isomorphism has inverse
restriction along the coefficient isomorphism; its unit map is sectionwise that ring
isomorphism. Both statements hold without any nonempty-site assumption. -/
theorem constantWeilTermwiseUnitMaps_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso (constantWeilTermwiseUnitMap l E g) ∧
      IsIso (constantWeilRestrictionUnitMap l E g) := by
  have : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  have : (proEtaleBaseChange g).IsEquivalence :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
      (inferInstance : WeaklyEtale g) trivial).isEquivalence_right_of_isEquivalence_left
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_functor
  have : (proEtaleModelBaseChange g).IsEquivalence := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange g).Final := inferInstance
  constructor
  · unfold constantWeilTermwiseUnitMap
    infer_instance
  · let c := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (constantWeilIntegralComparison l E g)
    apply (isIso_iff_of_reflects_iso (constantWeilRestrictionUnitMap l E g)
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted l E X) ⋙
        sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1})).mp
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective (fun x ↦ c.inv.hom.app U x * 1)
    simp only [mul_one]
    exact (ConcreteCategory.isIso_iff_bijective (c.inv.hom.app U)).1 inferInstance

/-- c_O_E on the completed regular module, with its transported coefficient action.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilTermwiseUnitIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  @asIso _ _ _ _ (constantWeilTermwiseUnitMap l E g)
      (constantWeilTermwiseUnitMaps_isIso l E g).1 ≪≫
    (@asIso _ _ _ _ (constantWeilRestrictionUnitMap l E g)
      (constantWeilTermwiseUnitMaps_isIso l E g).2).symm

/-- The coefficient comparison in the ambient derived category, via the exact single
functor comparison. Its underlying module map is the specified c_O_E.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilDerivedCoefficientComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isomorphismIntegralTermwiseInverseImage l E g).obj
        (integralConstantCoefficientObject l E Y) ≅ integralConstantCoefficientObject l E X :=
  ((isomorphismTermwiseModuleInverseImage g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (constantWeilIntegralComparison l E g)).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≪≫
    (DerivedCategory.singleFunctor (scalarReductionSource l E X) 0).mapIso
      (constantWeilTermwiseUnitIso l E g)

/-- The normalized derived-to-termwise comparison on the completed regular module.
The regular K-flat representative and strict Roos unit fix it, rather than bare existence
of a natural isomorphism. Multiplication by c_O_E identifies the same finite generators.
Source: blueprint order 1510, clause 3; lem-weil-isomorphism-derived-pullback
(blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralLambda {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  constantWeilIntegralRoosComparison l E g ≪≫
    (constantWeilDerivedCoefficientComparison l E g).symm

/-- theta_O_E is c_O_E composed with the normalized derived-to-termwise comparison.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralTheta {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  constantWeilIntegralLambda l E g ≪≫ constantWeilDerivedCoefficientComparison l E g

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The actual completed coefficient object in the intrinsic integral subcategory.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilIntegralObject (Y : Scheme.{u}) : sfIntegralConstructibleCategory l E Y :=
  ⟨integralConstantCoefficientObject l E Y,
    (integralConstantCoefficient_constructible l E Y D hl).2.1⟩

/-- E_Y is the image of the completed integral object under raw rationalization.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalObject (Y : Scheme.{u}) : sfRationalConstructibleCategory l E Y :=
  (sfRationalConstructibleLocalization l E Y).obj (constantWeilIntegralObject l E D hl Y)

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Lift the actual integral theta to the full constructible subcategory.
Source: blueprint order 1510, clause 3 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilConstructibleIntegralTheta :
    (@constructibleIntegralPullback l _ E _ _ _ _ _ (D.geometricFrobenius Y₀).asIso.hom
      (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
      (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)).obj
        (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left :=
  ObjectProperty.isoMk _ (constantWeilIntegralTheta l E (D.geometricFrobenius Y₀).asIso.hom)

/-- Rational theta is exactly integral theta tensor one. The source identification is
part of the recorded rational pullback's unchanged-integral-object normalization.
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalTheta :
    (sfWeilFrobeniusPullback D l hl Y₀ E).obj
        (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left :=
  eqToIso ((@rationalDerivedPullback_existsUnique l _ E _ _ _ _ _
    (D.geometricFrobenius Y₀).asIso.hom
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)
    (fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x)).exists.choose_spec.2.1 _) ≪≫
      (sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).mapIso
        (constantWeilConstructibleIntegralTheta l E D hl Y₀)

/-- The canonical E-Weil complex is the fixed pair (E_Y,theta_E).
Source: blueprint order 1510, clause 4 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilRationalComplex : sfWeilComplex D l hl Y₀ E :=
  IsoAlgebra.mk (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left)
    (constantWeilRationalTheta l E D hl Y₀)

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- At the least finite stage, the coefficient field is Q_l itself, transported by
Shrink.algEquiv. Its underlying object is the literal pair (Q_l,(Q_l)_Y).
Source: blueprint order 1510, clause 5 (blueprint: def-weil-constant-weil-structure). -/
def constantWeilAlgebraicallyClosedComplex : sfCommonStageWeilComplex D l hl Y₀ Ω :=
  sfWeilStageObject D l hl Y₀ Ω (Padic.finiteCoefficientBase l Ω)
    (constantWeilRationalComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (Padic.finiteCoefficientBase l Ω))
      D hl Y₀)

end WeilConjectures
