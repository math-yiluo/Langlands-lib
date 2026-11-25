/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Realization of integral pullback comparisons

Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: def-trf-integral-comparison-realization-models).

The sequence site retains the whole quotient diagram. Its pullback is the left
adjoint of the actual sectionwise direct image. Scalar change is the universal
derived change of rings for the actual map of quotient coefficient sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped ChangeOfRings

namespace IntegralComparisonModelProof

universe j c hj hc r w

private def constantRing (J : Type j) (C : Type c) [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r}) :
    Sheaf (verticalDiagramSiteTopology J C K) RingCat.{r} where
  obj := (CategoryTheory.Prod.snd J C).op ⋙ O.obj
  property := by
    apply (verticalDiagramSite_isSheaf_iff J C K _).2
    intro j
    exact O.property

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a product module to a vertical component. -/
private noncomputable def diagramSiteModuleComponent
    (J : Type j) (C : Type c) [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r})
    (F : ringedSiteModules.{r} (constantRing J C K O)) (j : Jᵒᵖ) :
    ringedSiteModules.{r} O where
  val := PresheafOfModules.pushforward₀Obj (Prod.sectR j.unop C)
    (constantRing J C K O).obj F.val
  isSheaf := (verticalDiagramSite_isSheaf_iff J C K F.val.presheaf).1 F.isSheaf j.unop

set_option backward.isDefEq.respectTransparency false in
set_option linter.unnecessarySimpa false in
/-- Horizontal structure map on the component modules. -/
private noncomputable def diagramSiteModuleArrow
    {J : Type j} {C : Type c} [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r})
    (F : ringedSiteModules.{r} (constantRing J C K O))
    {j k : Jᵒᵖ} (a : j ⟶ k) :
    diagramSiteModuleComponent J C K O F j ⟶ diagramSiteModuleComponent J C K O F k where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := F.val.map (Prod.mkHom a.unop (𝟙 U.unop)).op
          map_add' := map_add _
          map_smul' := by
            intro r x
            have H := F.val.map_smul (Prod.mkHom a.unop (𝟙 U.unop)).op r x
            simpa [constantRing, CategoryTheory.Prod.snd] using H }
      naturality := by
        intro U V f
        ext x
        simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
        change F.val.map (Prod.mkHom a.unop (𝟙 V.unop)).op
          (F.val.map ((Prod.sectR j.unop C).op.map f) x) =
          F.val.map ((Prod.sectR k.unop C).op.map f)
            (F.val.map (Prod.mkHom a.unop (𝟙 U.unop)).op x)
        have H : ((Prod.sectR j.unop C).op.map f) ≫
            (Prod.mkHom a.unop (𝟙 V.unop)).op =
            (Prod.mkHom a.unop (𝟙 U.unop)).op ≫ (Prod.sectR k.unop C).op.map f := by
          apply Quiver.Hom.unop_inj
          ext <;> simp
        have HH := F.val.presheaf.congr_map H
        rw [Functor.map_comp, Functor.map_comp] at HH
        exact ConcreteCategory.congr_hom HH x }

set_option backward.isDefEq.respectTransparency false in
/-- The functor restricting module sheaves to component modules. -/
private noncomputable def diagramSiteModuleCurry
    (J : Type j) (C : Type c) [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r}) :
    ringedSiteModules.{r} (constantRing J C K O) ⥤ Jᵒᵖ ⥤ ringedSiteModules.{r} O where
  obj F :=
    { obj j := diagramSiteModuleComponent J C K O F j
      map a := diagramSiteModuleArrow K O F a
      map_id j := by
        ext U x
        change F.val.map (𝟙 (op (j.unop, U.unop))) x = x
        simp
      map_comp {j k l} a b := by
        ext U x
        change F.val.map (Prod.mkHom (a ≫ b).unop (𝟙 U.unop)).op x =
          F.val.map (Prod.mkHom b.unop (𝟙 U.unop)).op
            (F.val.map (Prod.mkHom a.unop (𝟙 U.unop)).op x)
        rw [← F.val.map_comp_apply]
        apply F.val.congr_map_apply
        apply Quiver.Hom.unop_inj
        ext <;> simp }
  map f :=
    { app j :=
        { val :=
            { app U := f.val.app ((Prod.sectR j.unop C).op.obj U)
              naturality a := f.val.naturality ((Prod.sectR j.unop C).op.map a) } }
      naturality := by
        intro j k a
        ext U x
        exact (PresheafOfModules.naturality_apply f.val (Prod.mkHom a.unop (𝟙 U.unop)).op x) }
  map_id F := by ext j U x; rfl
  map_comp f g := by ext j U x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of presheaf modules along the two product coordinates. -/
private noncomputable def diagramSiteModuleUncurryVal
    {J : Type j} {C : Type c} [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r})
    (F : Jᵒᵖ ⥤ ringedSiteModules.{r} O) :
    PresheafOfModules.{r} (constantRing J C K O).obj where
  obj X := (F.obj (op X.unop.1)).val.obj (op X.unop.2)
  map {X Y} f := (F.map f.unop.1.op).val.app (op X.unop.2) ≫
    (F.obj (op Y.unop.1)).val.map f.unop.2.op
  map_id X := by
    ext x
    simp [constantRing, CategoryTheory.Prod.snd]
  map_comp {X Y Z} f g := by
    ext x
    change (F.obj (op Z.unop.1)).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map (f.unop.1.op ≫ g.unop.1.op)).val.app (op X.unop.2)) x) =
      (F.obj (op Z.unop.1)).val.map g.unop.2.op
        (((F.map g.unop.1.op).val.app (op Y.unop.2))
          ((F.obj (op Y.unop.1)).val.map f.unop.2.op
            (((F.map f.unop.1.op).val.app (op X.unop.2)) x)))
    rw [F.map_comp]
    change (F.obj (op Z.unop.1)).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map g.unop.1.op).val.app (op X.unop.2))
        (((F.map f.unop.1.op).val.app (op X.unop.2)) x)) = _
    rw [PresheafOfModules.naturality_apply (F.map g.unop.1.op).val]
    exact (F.obj (op Z.unop.1)).val.map_comp_apply _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of a diagram of module sheaves to a sheaf on the product site. -/
private noncomputable def diagramSiteModuleUncurryObj
    {J : Type j} {C : Type c} [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r})
    (F : Jᵒᵖ ⥤ ringedSiteModules.{r} O) :
    ringedSiteModules.{r} (constantRing J C K O) where
  val := diagramSiteModuleUncurryVal K O F
  isSheaf := by
    apply (verticalDiagramSite_isSheaf_iff J C K _).2
    intro j
    let e : (Prod.sectR j C).op ⋙ (diagramSiteModuleUncurryVal K O F).presheaf ≅
        (F.obj (op j)).val.presheaf :=
      NatIso.ofComponents (fun U ↦ Iso.refl _) (by
        intro U V f
        ext x
        change (F.obj (op j)).val.map f
          (((F.map (𝟙 (op j))).val.app U) x) = (F.obj (op j)).val.map f x
        simp)
    exact (Presheaf.isSheaf_of_iso_iff e).2 (F.obj (op j)).isSheaf

set_option backward.isDefEq.respectTransparency false in
/-- Assembly is functorial on module morphisms. -/
private noncomputable def diagramSiteModuleUncurry
    (J : Type j) (C : Type c) [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r}) :
    (Jᵒᵖ ⥤ ringedSiteModules.{r} O) ⥤ ringedSiteModules.{r} (constantRing J C K O) where
  obj F := diagramSiteModuleUncurryObj K O F
  map {F G} f :=
    { val :=
        { app X := (f.app (op X.unop.1)).val.app (op X.unop.2)
          naturality := by
            intro X Y a
            ext x
            change ((f.app (op Y.unop.1)).val.app (op Y.unop.2))
              (((F.obj (op Y.unop.1)).val.map a.unop.2.op)
                (((F.map a.unop.1.op).val.app (op X.unop.2)) x)) =
              ((G.obj (op Y.unop.1)).val.map a.unop.2.op)
                (((G.map a.unop.1.op).val.app (op X.unop.2))
                  (((f.app (op X.unop.1)).val.app (op X.unop.2)) x))
            rw [PresheafOfModules.naturality_apply (f.app (op Y.unop.1)).val]
            have H := congrArg (fun t ↦ t.val.app (op X.unop.2))
              (f.naturality a.unop.1.op)
            exact congrArg ((G.obj (op Y.unop.1)).val.map a.unop.2.op)
              (ConcreteCategory.congr_hom H x) } }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- A module-sheaf isomorphism from an isomorphism of its module presheaves. -/
private def diagramSiteModuleIso {C : Type c} [Category.{hc} C] {K : GrothendieckTopology C}
    {O : Sheaf K RingCat.{r}} {F G : ringedSiteModules.{r} O}
    (e : F.val ≅ G.val) : F ≅ G where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- The explicit equivalence for modules on the vertical product site. -/
private noncomputable def diagramSiteModuleEquivalence
    (J : Type j) (C : Type c) [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r}) :
    ringedSiteModules.{r} (constantRing J C K O) ≌ (Jᵒᵖ ⥤ ringedSiteModules.{r} O) where
  functor := diagramSiteModuleCurry J C K O
  inverse := diagramSiteModuleUncurry J C K O
  unitIso := NatIso.ofComponents (fun F ↦ diagramSiteModuleIso
    (PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by
      intro X Y f
      ext x
      change F.val.map f x = F.val.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
        (F.val.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
      have H : f = (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op ≫
          (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op := by
        apply Quiver.Hom.unop_inj
        ext <;> simp
      exact (F.val.congr_map_apply H x).trans (F.val.map_comp_apply _ _ x)))) (by
    intro F G f
    ext X x
    rfl)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ diagramSiteModuleIso (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      change (F.obj j).val.map f (((F.map (𝟙 j)).val.app U) x) =
        (F.obj j).val.map f x
      simp))) (by
      intro j k a
      ext U x
      change (F.obj k).val.map (𝟙 U) (((F.map a).val.app U) x) =
        ((F.map a).val.app U) x
      simp)) (by
    intro F G f
    ext j U x
    rfl)
  functor_unitIso_comp F := by
    ext j U x
    rfl

private def diagramSiteRingSlice
    {J : Type j} {C : Type c} [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r})
    (R : Sheaf (verticalDiagramSiteTopology J C K) RingCat.{r})
    (φ : constantRing J C K O ⟶ R) (j : J)
    [(Prod.sectR j C).IsContinuous K (verticalDiagramSiteTopology J C K)] :
    O ⟶ ((Prod.sectR j C).sheafPushforwardContinuous RingCat K
      (verticalDiagramSiteTopology J C K)).obj R where
  hom :=
    { app U := φ.hom.app (op (j, U.unop))
      naturality {_U _V} f := φ.hom.naturality ((Prod.sectR j C).op.map f) }

private theorem moduleSheaf_ext
    {C : Type c} [Category.{hc} C] {K : GrothendieckTopology C}
    {O : Sheaf K RingCat.{r}} (M N : SheafOfModules.{w} O)
    (hobj : ∀ U : Cᵒᵖ, M.val.obj U = N.val.obj U)
    (hmap : ∀ (U V : Cᵒᵖ) (f : U ⟶ V), HEq (M.val.map f) (N.val.map f)) : M = N := by
  cases M with | mk M hm =>
    cases N with | mk N hn =>
      congr 1
      cases M with | mk mo mm mi mc =>
        cases N with | mk no nm ni nc =>
          have ho : mo = no := funext hobj
          cases ho
          have hh : @mm = @nm := by
            funext U V f
            exact eq_of_heq (hmap U V f)
          cases hh
          rfl

private theorem diagramSiteModuleCurry_restrict_obj
    {J : Type j} {C : Type c} [Category.{hj} J] [Category.{hc} C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{r})
    (R : Sheaf (verticalDiagramSiteTopology J C K) RingCat.{r})
    (φ : constantRing J C K O ⟶ R) (j : J)
    [(Prod.sectR j C).IsContinuous K (verticalDiagramSiteTopology J C K)]
    (M : SheafOfModules.{r} R) :
    ((diagramSiteModuleCurry J C K O).obj
      ((SheafOfModules.restrictScalars φ).obj M)).obj (op j) =
      (SheafOfModules.pushforward (diagramSiteRingSlice K O R φ j)).obj M := by
  apply moduleSheaf_ext
  · intro U
    rfl
  · intro U V f
    rfl

private theorem pushforward_restrict_obj
    {C : Type c} [Category.{hc} C] {D : Type j} [Category.{hj} D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous K L]
    {A B : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (p : A ⟶ B) (φ : B ⟶ (F.sheafPushforwardContinuous RingCat K L).obj R)
    (M : SheafOfModules.{r} R) :
    (SheafOfModules.pushforward (p ≫ φ)).obj M =
      (SheafOfModules.restrictScalars p).obj ((SheafOfModules.pushforward φ).obj M) := by
  rfl

private theorem restriction_exact
    {C : Type c} [Category.{hc} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {O S : Sheaf J CommRingCat.{r}} (φ : O ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ∧
    PreservesFiniteColimits (SheafOfModules.restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let R := SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let A := SheafOfModules.derivedChangeRingIndependentCoefficients J O
  let B := SheafOfModules.derivedChangeRingIndependentCoefficients J S
  have : PreservesFiniteLimits (R ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf B))
  have : PreservesFiniteColimits (R ⋙ SheafOfModules.toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf A)⟩

end IntegralComparisonModelProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

variable (X : Scheme.{t})

private def integralComparisonConstantSequenceRing :
    Sheaf (coefficientSequenceTopology (ProEt.topology X))
      CommRingCat.{max u (t + 1)} where
  obj := (CategoryTheory.Prod.snd ℕ X.ProEt).op ⋙
    (completedIntegralCommRingSheafUnrestricted l E X).obj
  property := by
    apply (verticalDiagramSite_isSheaf_iff ℕ X.ProEt (ProEt.topology X) _).2
    intro n
    exact (completedIntegralCommRingSheafUnrestricted l E X).property

private def integralComparisonProjectionDiagram :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E X) ⟶
      coefficientSequenceCommRingSystem l E X :=
  NatTrans.ofOpSequence (completedIntegralCommRingProjectionUnrestricted l E X) (by
    intro n
    simp only [Functor.const_obj_map, coefficientSequenceCommRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
    apply RingCat.hom_ext
    apply RingHom.ext
    intro x
    have hw := congrArg (fun v ↦ (v.hom.app U).hom x)
      (limit.w (integralCoefficientSheafSystem l E X)
        (homOfLE (Nat.le_succ n)).op)
    simp only [integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ] at hw
    convert hw.symm using 1 <;> rfl)

private def integralComparisonSequenceProjection :
    integralComparisonConstantSequenceRing l E X ⟶ coefficientSequenceCommRingSheaf l E X where
  hom := Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := X.ProEt)).functor
    (Functor.uncurry.map (Functor.whiskerRight (integralComparisonProjectionDiagram l E X)
      (sheafToPresheaf (ProEt.topology X) CommRingCat.{max u (t + 1)})))

private def integralComparisonCoefficientCurry :
    SheafOfModules.{max u (t + 1)}
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (integralComparisonConstantSequenceRing l E X)) ≌
      (ℕᵒᵖ ⥤ scalarReductionSource l E X) :=
  IntegralComparisonModelProof.diagramSiteModuleEquivalence ℕ X.ProEt (ProEt.topology X)
    (SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))

private def integralComparisonRestrictionToConstant :=
  SheafOfModules.restrictScalars.{max u (t + 1)}
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (integralComparisonSequenceProjection l E X))

private def integralComparisonRestrictionCurried :=
  integralComparisonRestrictionToConstant l E X ⋙
    (integralComparisonCoefficientCurry l E X).functor

private theorem integralComparisonVerticalSliceContinuous (n : ℕ) :
    (Prod.sectR n X.ProEt).IsContinuous (ProEt.topology X)
      (verticalDiagramSiteTopology ℕ X.ProEt (ProEt.topology X)) :=
  coefficientSequenceEvaluationContinuous X n

attribute [local instance] integralComparisonVerticalSliceContinuous

private theorem integralComparisonSliceProjection_eq (n : ℕ) :
    IntegralComparisonModelProof.diagramSiteRingSlice (ProEt.topology X)
      (SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l E X)) _
      ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
        (forget₂ CommRingCat RingCat)).map (integralComparisonSequenceProjection l E X)) n =
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).map
        (completedIntegralCommRingProjectionUnrestricted l E X n)) ≫
      eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have he : (eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm).hom.app U =
      𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change _ = _ ≫ (eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm).hom.app U
  rw [he, Category.comp_id]
  rfl

private theorem integralComparisonRestrictionCurried_obj
    (M : coefficientSequenceModules l E X) (n : ℕ) :
    ((integralComparisonRestrictionCurried l E X).obj M).obj (op n) =
      (scalarReductionRestriction l E X n).obj
        ((coefficientSequenceEvaluation l E X n).obj M) := by
  let O := SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)
  let R := (sheafCompose (coefficientSequenceTopology (ProEt.topology X))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E X)
  let φ := (sheafCompose (coefficientSequenceTopology (ProEt.topology X))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (integralComparisonSequenceProjection l E X)
  have h := IntegralComparisonModelProof.diagramSiteModuleCurry_restrict_obj
    (ProEt.topology X) O R φ n M
  refine h.trans ?_
  change (SheafOfModules.pushforward
    (IntegralComparisonModelProof.diagramSiteRingSlice (ProEt.topology X) O R φ n)).obj M = _
  exact (congrArg (fun p ↦ (SheafOfModules.pushforward p).obj M)
    (integralComparisonSliceProjection_eq l E X n)).trans
      (IntegralComparisonModelProof.pushforward_restrict_obj _ _ M)

private theorem integralComparisonRestrictionCurried_eq :
    integralComparisonRestrictionCurried l E X = coefficientSequenceRestriction l E X := by
  apply (coefficientSequenceRestriction_exists l E X).unique ?_
    ((coefficientSequenceRestriction_exists l E X).exists.choose_spec)
  refine ⟨integralComparisonRestrictionCurried_obj l E X, ?_, ?_⟩
  · intro M m n h V
    rfl
  · intro M N f n V
    rfl

/-- The exact constant tower functor, on ordinary derived categories.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonConstantTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E X :=
  (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
    ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategory

/-- The exact diagonal/total-limit adjunction, using the ordinary adjunction
and the universal right derived functor. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonConstantAdjunction : integralComparisonConstantTower l E X ⊣
    coefficientConstantTowerLimit l E X :=
  (constLimAdj (J := ℕᵒᵖ)
    (C := scalarReductionSource l E X)).mapDerivedCategoryRightDerivedAdjunction

/-- The counit in the derived category of whole strict towers.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonTowerCounit :
    coefficientConstantTowerLimit l E X ⋙ integralComparisonConstantTower l E X ⟶ 𝟭 _ :=
  (integralComparisonConstantAdjunction l E X).counit

set_option backward.defeqAttrib.useBackward true in
private theorem integralComparisonDerivedCounit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G) (I : CochainComplex B ℤ) [I.IsKInjective] :
    adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso I).hom ≫
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I) := by
  let J := (HomotopyCategory.quotient B (.up ℤ)).obj I
  let d := adj.mapDerivedCategoryRightDerivedAdjunction
  let e := (DerivedCategory.quotientCompQhIso B).app I
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso B (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit J
  have hc : d.counit.app (DerivedCategory.Qh.obj J) =
      F.mapDerivedCategory.map (inv (G.rightDerivedFunctorUnit.app J)) ≫
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J) := by
    rw [← hfac, ← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have ht :
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J) ≫
        e.hom =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj I)) ≫
      F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app I) := by
    have hf := F.mapDerivedCategoryFactorsh_hom_app
      ((G.mapHomologicalComplex (.up ℤ)).obj I)
    change F.mapDerivedCategoryFactorsh.hom.app
      ((G.mapHomotopyCategory (.up ℤ)).obj J) = _ at hf
    rw [hf]
    dsimp [J]
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Category.assoc]
    erw [DerivedCategory.quotientCompQhIso_hom_naturality]
    dsimp only [Functor.comp_obj]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.id_comp, Iso.inv_hom_id_app_assoc]
    rfl
  calc
    d.counit.app (DerivedCategory.Q.obj I) =
        F.mapDerivedCategory.map (G.rightDerivedFunctor.map e.inv) ≫
        d.counit.app (DerivedCategory.Qh.obj J) ≫ e.hom := by
      have hn := d.counit.naturality e.inv
      change F.mapDerivedCategory.map (G.rightDerivedFunctor.map e.inv) ≫
        d.counit.app (DerivedCategory.Qh.obj J) =
        d.counit.app (DerivedCategory.Q.obj I) ≫ e.inv at hn
      rw [← Category.assoc, hn, Category.assoc, e.inv_hom_id]
      exact (Category.comp_id _).symm
    _ = F.mapDerivedCategory.map (G.rightDerivedFunctor.map e.inv) ≫
        F.mapDerivedCategory.map (inv (G.rightDerivedFunctorUnit.app J)) ≫
        F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app J) ≫
        e.hom := by rw [hc]; simp only [Category.assoc]
    _ = _ := by
      rw [ht]
      simp only [CategoryTheory.Functor.rightDerivedFunctorObjQIso, Iso.trans_hom,
        Functor.mapIso_hom, Iso.symm_hom, asIso_inv, CategoryTheory.Functor.map_comp,
        Category.assoc, Iso.app_hom, Iso.app_inv]
      rfl

/-- On a simultaneous K-injective resolution this is the ordinary limit cone.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models).
Proof: the universal derived adjunction evaluates on a K-injective complex by
the right-derived comparison. Its underlying ordinary adjunction counit is
exactly the constant limit cone, giving the displayed formula. Naturality
transports this formula along every K-injective resolution. -/
theorem integralComparisonTowerCounit_computes :
     ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
      [I.IsKInjective],
    (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj I) =
      (integralComparisonConstantTower l E X).map
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X) I).hom ≫
      (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
            scalarReductionSource l E X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).counit
          (ComplexShape.up ℤ)).app I) := by
  intro I _
  exact integralComparisonDerivedCounit (constLimAdj (J := ℕᵒᵖ)
    (C := scalarReductionSource l E X)) I

private theorem integralComparisonLimitToRoos_generic
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
    (C : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃! α : ((lim : (ℕᵒᵖ ⥤ A) ⥤
        A).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶
      integralOperationsRoos C.asFunctor,
      (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary C.asFunctor) ≫ Pi.π (fun m ↦ C.asFunctor.obj (op m)) n =
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app C) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), α.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v i j h = 0) := by
  unfold integralOperationsRoos
  let π (n : ℕ) :
      ((lim : (ℕᵒᵖ ⥤ A) ⥤
        A).mapHomologicalComplex (.up ℤ)).obj C ⟶
      C.asFunctor.obj (op n) :=
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app C
  let a := Pi.lift π
  have hπ (n : ℕ) : π (n + 1) ≫ integralOperationsTowerStep C.asFunctor n = π n := by
    ext i : 1
    exact limit.w (C.X i) (homOfLE (Nat.le_succ n)).op
  have ha : a ≫ scalarRoosBoundary C.asFunctor = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Category.assoc,
      Pi.lift_comp_π, zero_comp]
    rw [← Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π, hπ, sub_self]
  let α := CochainComplex.mappingCocone.lift (scalarRoosBoundary C.asFunctor) a 0
    (by simp [ha])
  have hα : α ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) = a :=
    CochainComplex.mappingCocone.lift_fst _ _ _ _
  refine ⟨α, ⟨?_, ?_⟩, ?_⟩
  · intro n
    rw [← Category.assoc, hα]
    exact Pi.lift_comp_π π n
  · intro i j h
    simp [α]
  · intro β hβ
    have hf : β ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) =
        α ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor) := by
      rw [hα]
      apply Pi.hom_ext
      intro n
      rw [Category.assoc, hβ.1 n]
      exact (Pi.lift_comp_π π n).symm
    ext i : 1
    have hfi := congrArg (fun f ↦ HomologicalComplex.Hom.f f i) hf
    have hsi : α.f i ≫ (CochainComplex.mappingCocone.snd
        (scalarRoosBoundary C.asFunctor)).v i (i - 1) (by omega) = 0 := by
      simp [α]
    calc
      β.f i = β.f i ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = β.f i ≫ ((CochainComplex.mappingCocone.fst
          (scalarRoosBoundary C.asFunctor)).f i ≫
          (CochainComplex.mappingCocone.inl (scalarRoosBoundary C.asFunctor)).v i i
            (add_zero i) +
          (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v i (i - 1)
            (by omega) ≫
          (CochainComplex.mappingCocone.inr (scalarRoosBoundary C.asFunctor)).1.v
            (i - 1) i (by omega)) := by
        rw [CochainComplex.mappingCocone.id_X]
      _ = α.f i ≫ 𝟙 _ := by
        rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
          hβ.2 i (i - 1) (by omega), zero_comp, add_zero]
        simp only [HomologicalComplex.comp_f] at hfi
        rw [hfi]
        conv_rhs => rw [← CochainComplex.mappingCocone.id_X
          (scalarRoosBoundary C.asFunctor) i (i - 1) (by omega)]
        rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
          hsi, zero_comp, add_zero]
      _ = α.f i := Category.comp_id _

/-- The ordinary limit maps to its Roos cocone by the limit tuple and zero in
its shifted coordinate. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models).
Proof: the compatible limit tuple is killed by 1-s, so the two indicated
coordinates commute with the signed cocone differential. They give a chain map.
The two cocone coordinates jointly determine that map, proving uniqueness. -/
theorem integralComparisonLimitToRoos_existsUnique
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    ∃! α : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
        scalarReductionSource l E X).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶
      integralOperationsRoos C.asFunctor,
      (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary C.asFunctor) ≫ Pi.π (fun m ↦ C.asFunctor.obj (op m)) n =
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app C) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), α.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v i j h = 0) := by
  exact integralComparisonLimitToRoos_generic C

/-- The specified limit-tuple/zero-shifted-coordinate map.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonLimitToRoos
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
      scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).obj C ⟶
        integralOperationsRoos C.asFunctor :=
  (integralComparisonLimitToRoos_existsUnique l E X C).exists.choose

/-- The K-injective normalization of a natural Roos comparison.
Naming this predicate prevents the model constructor from repeatedly elaborating
its full derived-limit equation. It is the unchanged representative formula.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def IsIntegralComparisonRoosNormalized
    (comparison : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) : Prop :=
  ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) [I.IsKInjective],
    comparison.hom.app I =
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X) I).hom ≫
      DerivedCategory.Q.map (integralComparisonLimitToRoos l E X I)

/-- The Roos model of total limit, with its exact K-injective normalization.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonRoosModel where
  /-- A natural comparison on entire strict tower complexes. -/
  comparison : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  /-- It is induced on simultaneous K-injectives by the ordinary limit cone. -/
  computes : IsIntegralComparisonRoosNormalized l E X comparison

/-- Scalar restriction has exactly the original underlying section type.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models).
Proof: the object equation for coefficientSequenceRestriction identifies it with
ordinary finite restriction after evaluation. Neither restriction changes the
underlying abelian sheaf, and coefficientSequenceEvaluationAb_eq finishes. -/
theorem integralComparisonRestrictedSectionType (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : X.ProEtᵒᵖ) :
    ↥((((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.obj U) =
      ↥(M.val.obj (op (n, U.unop))) := by
  unfold coefficientSequenceRestriction
  rw [((coefficientSequenceRestriction_exists l E X).exists.choose_spec).1 M n]
  exact congrArg (fun A : AddCommGrpCat ↦ ↥A)
    (coefficientSequenceEvaluationAb_eq l E X M n U)

/-- The same section read over the completed coefficient sheaf.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonRestrictedSection (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.obj U :=
  cast (integralComparisonRestrictedSectionType l E X M n U).symm x

/-- The inverse identification of evaluation sections with original sections.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonSequenceSection (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E X n).obj M).val.obj U) :
    M.val.obj (op (n, U.unop)) :=
  (eqToHom (coefficientSequenceEvaluationAb_eq l E X M n U)) x

/-- The normalized passage from the derived total limit to the actual Roos cocone.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonRoosBridge (ρ : IntegralComparisonRoosModel l E X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor) :=
  (coefficientConstantTowerLimit l E X).mapIso
    ((coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app C) ≪≫
    ρ.comparison.app
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C)

/-- A strict reduction presentation fixes its comparison in the whole derived tower.
The transpose of `e` is the localization of the tensor-unit map specified by `κ`.
Finite evaluations alone do not determine that derived tower morphism.
Source: Stacks 06YY, 0941, the ordinary extension/restriction adjunction.
(blueprint: def-trf-integral-comparison-realization-models). -/
@[irreducible] def IsIntegralComparisonPresentationCoherent
    (S : CoefficientDerivedSystemCalculus l E X)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P) : Prop :=
  ∃ b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C,
    (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U),
      (((b.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l E X (C.X i) n U
          (integralComparisonSequenceSection l E X (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E X n (P.X i) U 1 x)))) ∧
    (integralComparisonConstantTower l E X).map
        (S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
          (coefficientSequenceLimit l E X).map e.hom) ≫
        (integralComparisonTowerCounit l E X).app
          ((coefficientSequenceDerivedRestriction l E X).obj (DerivedCategory.Q.obj C)) =
      (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map b ≫
        (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.inv.app C

/-- The representative normalization of completed pullback, expressed as one named
predicate so that the model structure does not repeatedly elaborate the long equation.
Source: Stacks 099N(5), 0D6D, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def IsIntegralComparisonPullbackNormalized {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E Z)
    (realization : integralDerivedPullback l E f ≅ S.reduction ⋙
      integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E Z) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj),
    CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E Y S P.obj C e κ →
    ∃ q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
        ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
          (integralComparisonRestrictedSection l E Z
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E Z ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralDerivedPullbackComparison l E f).hom.app P

/-- The completed pullback is the total limit of the actual finite pullback of
one reduction diagram. The normalization tests every whole-system coherent
simultaneous presentation of every flat-term K-flat complex, and fixes maps on
tensor-unit generators.
Source: Stacks 099N(5), 0D6D, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonPullbackModel {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E Z) where
  /-- Natural realization on the ambient derived category. -/
  realization : integralDerivedPullback l E f ≅ S.reduction ⋙
    integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E Z
  /-- On every representative it is the defining pullback tower comparison. -/
  normalization : IsIntegralComparisonPullbackNormalized l E f S ρ realization

/-- The same coherent quotient-presentation normalization for completed scalar change.
Naming this predicate preserves the equation while keeping model projections small.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def IsIntegralComparisonScalarNormalized
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (realization : integralScalarExtensionOfUniverses l E L ι X ≅ S.reduction ⋙
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ coefficientSequenceLimit l L X) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    IsIntegralComparisonPresentationCoherent l E X S P.obj C e κ →
    ∃ q : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι X).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (P.obj.X i) U s x) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonDerivedSequenceScalar l E L ι X).map e.hom) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
        (integralComparisonRoosBridge l L X ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralScalarExtensionComparisonOfUniverses l E L ι X).hom.app P

/-- Scalar realization uses the very same reduction diagram and the universal
cochain counit of actual change of rings on that diagram.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonScalarModel
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X) where
  /-- Completed scalar extension as realization of whole-system scalar change. -/
  realization : integralScalarExtensionOfUniverses l E L ι X ≅ S.reduction ⋙
    integralComparisonDerivedSequenceScalar l E L ι X ⋙ coefficientSequenceLimit l L X
  /-- The fixed normalization on whole-system coherent quotient presentations. -/
  normalization : IsIntegralComparisonScalarNormalized l E L ι X S ρ realization

end WeilConjectures
