/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.SequenceSiteCompletionProjectionSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Scalar-extension comparisons and quotient transitions

Source: Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory
namespace WeilConjectures
open SemilinearSections

private theorem restriction_map_apply
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S) {M N : SheafOfModules.{r} S}
    (f : M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((SheafOfModules.restrictScalars φ).map f).val.app V x = f.val.app V x := rfl

private theorem restriction_composition_cast_apply
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (h : SheafOfModules.restrictScalars g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars k)
    (M : SheafOfModules.{r} T) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((eqToIso h).inv.app M).val.app V x = x := by
  let U := SheafOfModules.toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{r} ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{r}).obj V
  have he : U.map ((eqToIso h).inv.app M) = 𝟙 _ := by
    simp only [eqToIso.inv, eqToHom_app, eqToHom_map]
    rfl
  exact ConcreteCategory.congr_hom he x

private theorem quotient_mate_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {S : B ⥤ A} (adj : F ⊣ S)
    {F' : A ⥤ D} {S' : D ⥤ A} (adj' : F' ⊣ S')
    (U : D ⥤ B) (e : U ⋙ S ≅ S') (M : A) :
    adj.unit.app M ≫ S.map ((coefficientQuotientNatTrans adj adj' U e).app M) =
      adj'.unit.app M ≫ e.inv.app (F'.obj M) := by
  change adj.homEquiv M _ ((coefficientQuotientNatTrans adj adj' U e).app M) = _
  exact Equiv.apply_symm_apply _ _

private theorem quotient_mate_unit_of_eq
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {S : B ⥤ A} (adj : F ⊣ S)
    {F' : A ⥤ D} {S' : D ⥤ A} (adj' : F' ⊣ S')
    (U : D ⥤ B) (e : U ⋙ S ≅ S') (M : A)
    (q : F.obj M ⟶ U.obj (F'.obj M))
    (hq : q = (coefficientQuotientNatTrans adj adj' U e).app M) :
    adj.unit.app M ≫ S.map q = adj'.unit.app M ≫ e.inv.app (F'.obj M) := by
  subst q
  exact quotient_mate_unit adj adj' U e M

private theorem module_nat_iso_comp_apply
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {D : Type*} [Category D]
    {F G H : D ⥤ SheafOfModules.{r} R} (e : F ≅ G) (f : G ≅ H)
    (M : D) (V : Cᵒᵖ) (x : (F.obj M).val.obj V) :
    (((e ≪≫ f).hom.app M).val.app V) x =
      (f.hom.app M).val.app V ((e.hom.app M).val.app V x) := rfl

private theorem module_unit_sections_of_eq
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (h : SheafOfModules.restrictScalars g ⋙ SheafOfModules.restrictScalars f =
      SheafOfModules.restrictScalars k)
    {M : SheafOfModules.{r} R} {Q : SheafOfModules.{r} S} {Q' : SheafOfModules.{r} T}
    (u : M ⟶ (SheafOfModules.restrictScalars f).obj Q)
    (v : M ⟶ (SheafOfModules.restrictScalars k).obj Q')
    (q : Q ⟶ (SheafOfModules.restrictScalars g).obj Q')
    (hu : u ≫ (SheafOfModules.restrictScalars f).map q = v ≫ (eqToIso h).inv.app Q')
    (V : Cᵒᵖ) (x : M.val.obj V) : q.val.app V (u.val.app V x) = v.val.app V x := by
  have hv := congrArg (fun f ↦ f.val.app V x) hu
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
  erw [restriction_map_apply] at hv
  exact hv.trans (restriction_composition_cast_apply f g k h Q' V (v.val.app V x))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_comparison_unit_abstract
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    (A : SheafOfModules.SystemScalarModel φ) {F : Mod J R ⥤ Mod J S}
    (ad : F ⊣ res φ) (M : Mod J R) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((A.ordinaryAdj.leftAdjointUniq ad).hom.app M).val.app V
      (SheafOfModules.systemModelTmul A.model M V 1 x) = (ad.unit.app M).val.app V x := by
  have hu := congrArg (fun f ↦ f.val.app V x)
    (Adjunction.unit_leftAdjointUniq_hom_app A.ordinaryAdj ad M)
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at hu
  rw [A.unit_normalized] at hu
  exact hu

private theorem module_iso_inv_hom_sections
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{r}} {X Y : SheafOfModules.{r} R}
    (e : X ≅ Y) (V : Cᵒᵖ) (x : Y.val.obj V) :
    e.hom.val.app V (e.inv.val.app V x) = x := by
  have hh := congrArg (fun f ↦ f.val.app V x) e.inv_hom_id
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using hh

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar-extension adjoint comparisons preserve a transition which preserves unit tensors.
Source: Stacks 03D7 and 03EK (blueprint: lem-pur-system-scalar-transition-comparison).
Proof: precompose with the inverse model comparison. Scalar-extension Hom
extensionality reduces equality to unit tensors. Both left-adjoint uniqueness
comparisons preserve the adjunction units. The defining quotient mate has the
same unit equation, and scalar restriction leaves every underlying section map
unchanged. The two maps therefore agree on all local generators. -/
theorem systemScalarTransitionComparison
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S T : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (ψ : R ⟶ T)
    (A : SheafOfModules.SystemScalarModel φ) (B : SheafOfModules.SystemScalarModel ψ)
    {Fm : Mod J R ⥤ Mod J S} (am : Fm ⊣ res φ)
    {Fn : Mod J R ⥤ Mod J T} (an : Fn ⊣ res ψ)
    {Xm : Mod J R ⥤ Mod J S} {Xn : Mod J R ⥤ Mod J T}
    (em : Xm ≅ A.model.E) (en : Xn ≅ B.model.E) (M : Mod J R)
    (g : ring J S ⟶ ring J T)
    (e : SheafOfModules.restrictScalars g ⋙ res φ = res ψ)
    (δ : Xm.obj M ⟶ (SheafOfModules.restrictScalars g).obj (Xn.obj M))
    (hδ : ∀ (V : Cᵒᵖ) (x : M.val.obj V),
      (en.hom.app M).val.app V (δ.val.app V ((em.inv.app M).val.app V
        (SheafOfModules.systemModelTmul A.model M V 1 x))) =
          SheafOfModules.systemModelTmul B.model M V 1 x)
    (q : Fm.obj M ⟶ (SheafOfModules.restrictScalars g).obj (Fn.obj M))
    (hq : q = (coefficientQuotientNatTrans am an
      (SheafOfModules.restrictScalars g) (eqToIso e)).app M) :
    δ ≫ (SheafOfModules.restrictScalars g).map
      ((en ≪≫ B.ordinaryAdj.leftAdjointUniq an).hom.app M) =
        ((em ≪≫ A.ordinaryAdj.leftAdjointUniq am).hom.app M) ≫ q := by
  apply (cancel_epi (em.inv.app M)).mp
  apply SheafOfModules.systemScalarModel_hom_ext A M _
  intro V x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [restriction_map_apply]
  erw [module_nat_iso_comp_apply en (B.ordinaryAdj.leftAdjointUniq an) M V]
  rw [hδ V x, scalar_comparison_unit_abstract J ψ B an M V x]
  erw [module_nat_iso_comp_apply em (A.ordinaryAdj.leftAdjointUniq am) M V]
  erw [module_iso_inv_hom_sections (em.app M) V,
    scalar_comparison_unit_abstract J φ A am M V x]
  exact (module_unit_sections_of_eq
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ) g
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map ψ)
    e (am.unit.app M) (an.unit.app M) q
    (quotient_mate_unit_of_eq am an (SheafOfModules.restrictScalars g)
      (eqToIso e) M q hq) V x).symm

private theorem unit_iso_cancel
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y Z : A} {M : B} (u : M ⟶ F.obj X) (e : X ≅ Y) (f : Z ≅ Y) :
    u ≫ F.map e.hom ≫ F.map f.inv ≫ F.map f.hom ≫ F.map e.inv = u := by
  rw [← F.map_comp_assoc f.inv f.hom, Iso.inv_hom_id, F.map_id, Category.id_comp,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id]

private theorem unit_evaluation
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) (n : ℕ) :
    (seqModuleAdjunction J B τ b).unit.app M ≫
      limit.π ((seqRestriction J B τ b).obj ((seqExtension J B τ b).obj M)) (op n) ≫
      (res (b.π.app (op n))).map
        ((seqEvaluationIso J B τ n).inv.app ((seqExtension J B τ b).obj M)) ≫
      (res (b.π.app (op n))).map ((seqOrdinaryEvaluation J B τ b n).hom.app M) =
        (seqScalar J B τ b n).ordinaryAdj.unit.app M := by
  rw [← Category.assoc, ← Category.assoc, seqUnitMorphism]
  simp only [seqOrdinaryEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  change (seqScalar J B τ b n).ordinaryAdj.unit.app M ≫
    (res (b.π.app (op n))).map
      (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ)
        ((SheafOfModules.SequenceProjection.extension b.pt (rings J B τ) b.π).obj M) n).hom ≫
    (res (b.π.app (op n))).map
      ((seqEvaluationIso J B τ n).inv.app ((seqExtension J B τ b).obj M)) ≫
    (res (b.π.app (op n))).map
      ((seqEvaluationIso J B τ n).hom.app ((seqExtension J B τ b).obj M)) ≫
    (res (b.π.app (op n))).map
      (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ)
        ((SheafOfModules.SequenceProjection.extension b.pt (rings J B τ) b.π).obj M) n).inv = _
  exact unit_iso_cancel (res (b.π.app (op n)))
    ((seqScalar J B τ b n).ordinaryAdj.unit.app M)
    (SheafOfModules.strictSystemSequenceUnitLevel (rings J B τ)
      ((SheafOfModules.SequenceProjection.extension b.pt (rings J B τ) b.π).obj M) n)
    ((seqEvaluationIso J B τ n).app ((seqExtension J B τ b).obj M))

private theorem evaluation_comparison_eq
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (n : ℕ) :
    seqEvaluationIso J B τ n = eqToIso (seqEval_eq J B τ n) := by
  have h (φ ψ : ring J (B n) ⟶
      ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{r}
        J (coefficientSequenceTopology J)).obj (ring (coefficientSequenceTopology J)
          (systemRing J B τ))) (e : φ = ψ) :
      SheafOfModules.pushforwardCongr e =
        eqToIso (congrArg (fun k ↦ SheafOfModules.pushforward (F := Prod.sectR n C) k) e) := by
    subst ψ
    ext N V x
    rfl
  exact h _ _ (seqEval_ringMap J B τ n)

private theorem extension_horizontal_unit
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) {m n : ℕ} (h : n ≤ m) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((seqExtension J B τ b).obj M).val.map
      (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op
      (SheafOfModules.systemModelTmul (seqScalar J B τ b m).model M V 1 x) =
        SheafOfModules.systemModelTmul (seqScalar J B τ b n).model M V 1 x := by
  change (((SheafOfModules.SequenceProjection.extensionObj b.pt (rings J B τ) b.π M).level
    n).val.map (𝟙 V))
      ((SheafOfModules.SequenceProjection.transition b.pt (rings J B τ) b.π M h).val.app V
        (SheafOfModules.systemModelTmul (seqScalar J B τ b m).model M V 1 x)) = _
  rw [PresheafOfModules.map_id]
  change (SheafOfModules.SequenceProjection.transition b.pt (rings J B τ) b.π M h).val.app V
    (SheafOfModules.systemModelTmul (seqScalar J B τ b m).model M V 1 x) = _
  erw [SheafOfModules.SequenceProjection.transition_tmul.{c, v, r}, map_one]

private theorem transpose_of_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} (adj : F ⊣ R)
    {V : B ⥤ D} {S : D ⥤ A} {T : A ⥤ D} (fin : T ⊣ S)
    (e : F ⋙ V ≅ T) (π : R ⟶ V ⋙ S)
    (hu : ∀ M, adj.unit.app M ≫ π.app (F.obj M) ≫ S.map (e.hom.app M) = fin.unit.app M)
    (M : A) (N : B) (h : M ⟶ R.obj N) :
    fin.homEquiv M (V.obj N)
      (e.inv.app M ≫ V.map ((adj.homEquiv M N).symm h)) = h ≫ π.app N := by
  have hc : fin.unit.app M ≫ S.map (e.inv.app M) =
      adj.unit.app M ≫ π.app (F.obj M) := by
    apply (cancel_mono (S.map (e.hom.app M))).mp
    erw [Category.assoc, ← S.map_comp, Iso.inv_hom_id_app, S.map_id, Category.comp_id]
    simpa only [Category.assoc] using (hu M).symm
  erw [Adjunction.homEquiv_unit, S.map_comp, ← Category.assoc, hc,
    Category.assoc, ← π.naturality, ← Category.assoc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem generic_ordinary_transition
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) (m n : ℕ) (h : n ≤ m)
    {Fm : Mod J b.pt ⥤ Mod J (B m)} (am : Fm ⊣ res (b.π.app (op m)))
    {Fn : Mod J b.pt ⥤ Mod J (B n)} (an : Fn ⊣ res (b.π.app (op n)))
    (g : ring J (B m) ⟶ ring J (B n))
    (e : SheafOfModules.restrictScalars g ⋙ res (b.π.app (op m)) =
      res (b.π.app (op n)))
    (δ : (evaluation J B τ m).obj ((seqExtension J B τ b).obj M) ⟶
      (SheafOfModules.restrictScalars g).obj
        ((evaluation J B τ n).obj ((seqExtension J B τ b).obj M)))
    (hδ : ∀ (V : Cᵒᵖ),
      HEq (fun x : ((evaluation J B τ m).obj ((seqExtension J B τ b).obj M)).val.obj V ↦
        δ.val.app V x)
        (fun x : ((seqExtension J B τ b).obj M).val.obj (op (m, V.unop)) ↦
          ((seqExtension J B τ b).obj M).val.map
            (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    :
    δ ≫ (SheafOfModules.restrictScalars g).map
      (((seqOrdinaryEvaluation J B τ b n) ≪≫
        (seqScalar J B τ b n).ordinaryAdj.leftAdjointUniq an).hom.app M) =
      (((seqOrdinaryEvaluation J B τ b m) ≪≫
        (seqScalar J B τ b m).ordinaryAdj.leftAdjointUniq am).hom.app M) ≫
        (coefficientQuotientNatTrans am an
          (SheafOfModules.restrictScalars g) (eqToIso e)).app M := by
  apply systemScalarTransitionComparison J (b.π.app (op m)) (b.π.app (op n))
    (seqScalar J B τ b m) (seqScalar J B τ b n) am an
    (seqOrdinaryEvaluation J B τ b m) (seqOrdinaryEvaluation J B τ b n)
    M g e δ ?_
    ((coefficientQuotientNatTrans am an
      (SheafOfModules.restrictScalars g) (eqToIso e)).app M) rfl
  intro V x
  erw [seqOrdinaryEvaluation_hom J B τ b n M V]
  erw [seqOrdinaryEvaluation_inv J B τ b m M V]
  exact (congrFun (eq_of_heq (hδ V)) _).trans
    (extension_horizontal_unit J B τ b M h V x)

private def evaluatedIsoHom {A B D : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A) :
    G.obj (F.obj M) ⟶ H.obj M :=
  e.hom.app M

private theorem evaluatedIsoHom_heq {A B D : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A) :
    HEq (evaluatedIsoHom F G e M) (e.hom.app M) := HEq.rfl

private def evaluatedRightHom {A B D : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D]
    (F : A ⥤ D) (G : A ⥤ B) (R : B ⥤ D) (q : F ⟶ G ⋙ R) (M : A) :
    F.obj M ⟶ R.obj (G.obj M) := q.app M

private theorem evaluatedIsoHom_precomp_heq {A B D D' : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D] [Category.{v} D']
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A)
    (R : D ⥤ D') {N : D'} (δ : N ⟶ R.obj (G.obj (F.obj M))) :
    HEq (δ ≫ R.map (e.hom.app M)) (δ ≫ R.map (evaluatedIsoHom F G e M)) := HEq.rfl

private theorem evaluatedIsoHom_compRight_heq {A B D D' : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D] [Category.{v} D']
    (F : A ⥤ B) (G : B ⥤ D) {H : A ⥤ D} (e : F ⋙ G ≅ H) (M : A)
    (K : A ⥤ D') (R : D' ⥤ D) (q : H ⟶ K ⋙ R) :
    HEq (e.hom.app M ≫ q.app M)
      (evaluatedIsoHom F G e M ≫ evaluatedRightHom H K R q M) := HEq.rfl

private theorem evaluatedIsoHom_transition_eq {A B D D' : Type c}
    [Category.{v} A] [Category.{v} B] [Category.{v} D] [Category.{v} D']
    (F : A ⥤ B) (Vm : B ⥤ D) (Vn : B ⥤ D')
    {Tm : A ⥤ D} {Tn : A ⥤ D'}
    (tm : F ⋙ Vm ≅ Tm) (tn : F ⋙ Vn ≅ Tn) (M : A)
    (R : D' ⥤ D) (δ : Vm.obj (F.obj M) ⟶ R.obj (Vn.obj (F.obj M)))
    (q : Tm ⟶ Tn ⋙ R)
    (h : HEq (δ ≫ R.map (tn.hom.app M)) (tm.hom.app M ≫ q.app M)) :
    δ ≫ R.map (tn.hom.app M) = tm.hom.app M ≫ q.app M := eq_of_heq h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem generic_ordinary_transition_comparisons
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (b : Cone (rings J B τ))
    (M : Mod J b.pt) (m n : ℕ) (h : n ≤ m)
    {Fm : Mod J b.pt ⥤ Mod J (B m)}
    (Gm : Mod J (B m) ⥤ Mod J b.pt) (egm : Gm = res (b.π.app (op m)))
    (am : Fm ⊣ Gm)
    {Fn : Mod J b.pt ⥤ Mod J (B n)}
    (Gn : Mod J (B n) ⥤ Mod J b.pt) (egn : Gn = res (b.π.app (op n)))
    (an : Fn ⊣ Gn)
    (g : ring J (B m) ⟶ ring J (B n))
    (R : Mod J (B n) ⥤ Mod J (B m))
    (er : R = SheafOfModules.restrictScalars g)
    (e : R ⋙ Gm = Gn)
    (Xm : Mod J b.pt ⥤ Mod J (B m)) (Xn : Mod J b.pt ⥤ Mod J (B n))
    (exm : Xm = seqExtension J B τ b ⋙ evaluation J B τ m)
    (exn : Xn = seqExtension J B τ b ⋙ evaluation J B τ n)
    (xm : Mod J (B m)) (xn : Mod J (B n))
    (eam : xm = Xm.obj M) (ean : xn = Xn.obj M)
    (δ : xm ⟶ R.obj xn)
    (hδ : ∀ (V : Cᵒᵖ),
      HEq (fun x : xm.val.obj V ↦
        δ.val.app V x)
        (fun x : ((seqExtension J B τ b).obj M).val.obj (op (m, V.unop)) ↦
          ((seqExtension J B τ b).obj M).val.map
            (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    (tm : Xm ≅ Fm)
    (tn : Xn ≅ Fn)
    (htm : tm = eqToIso exm ≪≫ seqOrdinaryEvaluation J B τ b m ≪≫
      (seqScalar J B τ b m).ordinaryAdj.leftAdjointUniq
        (Eq.mp (congrArg (fun G ↦ Fm ⊣ G) egm) am))
    (htn : tn = eqToIso exn ≪≫ seqOrdinaryEvaluation J B τ b n ≪≫
      (seqScalar J B τ b n).ordinaryAdj.leftAdjointUniq
        (Eq.mp (congrArg (fun G ↦ Fn ⊣ G) egn) an))
    (fm : xm ⟶ Fm.obj M) (fn : xn ⟶ Fn.obj M)
    (hfm : HEq fm (tm.hom.app M)) (hfn : HEq fn (tn.hom.app M))
    (q : Fm ⟶ Fn ⋙ R)
    (hq : q = coefficientQuotientNatTrans am an R (eqToIso e))
    {α β : Type (max c r)} (L : α) (Q : β)
    (hL : HEq L (δ ≫ R.map fn)) (hQ : HEq Q (fm ≫ evaluatedRightHom Fm Fn R q M)) : HEq L Q := by
  refine hL.trans ((heq_of_eq ?_).trans hQ.symm)
  clear hL hQ L Q
  subst q
  cases eam
  cases ean
  have hm := eq_of_heq hfm
  have hn := eq_of_heq hfn
  subst fm
  subst fn
  cases egm
  cases egn
  cases er
  cases exm
  cases exn
  simp only [eqToIso_refl, Iso.refl_trans] at htm htn
  subst tm
  subst tn
  change δ ≫ (SheafOfModules.restrictScalars g).map
      (((seqOrdinaryEvaluation J B τ b n) ≪≫
        (seqScalar J B τ b n).ordinaryAdj.leftAdjointUniq an).hom.app M) =
    (((seqOrdinaryEvaluation J B τ b m) ≪≫
      (seqScalar J B τ b m).ordinaryAdj.leftAdjointUniq am).hom.app M) ≫
        (coefficientQuotientNatTrans am an
          (SheafOfModules.restrictScalars g) (eqToIso e)).app M
  exact generic_ordinary_transition J B τ b M m n h am an g e δ hδ

end WeilConjectures

attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
