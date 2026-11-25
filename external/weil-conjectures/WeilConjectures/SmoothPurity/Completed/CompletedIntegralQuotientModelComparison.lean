/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
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
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionExists
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # Balanced realization of the principal quotient completion model

Source: Stacks Project, Tags 093M, 03EK, 06YT and 08TC;
Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-quotient-model-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace WeilConjectures

namespace CompletedIntegralComparisonProof
universe u₀ v₀ r
open CategoryTheory.MonoidalCategory
open SheafOfModules
variable {C₀ : Type u₀} [Category.{v₀} C₀] [EssentiallySmall.{r} C₀]
  {J : GrothendieckTopology C₀}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R S : Sheaf J CommRingCat.{r}}
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
private noncomputable def restrictedTensorPresheafIso (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⊗ M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf.{v₀, u₀, r} φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (φ.hom.app V).hom
    let T := TensorProduct (R.obj.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
      (M.val.obj V)
    change ModuleCat.of (R.obj.obj V) T ≅
      (ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) T)
    exact (LinearEquiv.refl (R.obj.obj V) T).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      let : Module (R.obj.obj W)
          ((ModuleCat.restrictScalars
            (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
              (M.val.obj W)) := inferInstanceAs (Module (R.obj.obj W) (M.val.obj W))
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

private theorem restrictedTensorPresheafIso_hom_app (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C₀ᵒᵖ)
    (z : ((((restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⊗ M.val).obj U)) :
    (restrictedTensorPresheafIso φ M).hom.app U z = z := rfl

attribute [local irreducible] restrictedTensorPresheafIso

section
variable {R₀ B₀ : Sheaf J RingCat.{r}}

private noncomputable def restrictionSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  let A := (PresheafOfModules.restrictScalars α.hom).obj P
  let u := (PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app A
  let v := (PresheafOfModules.restrictScalars α.hom).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P)
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := A) (F := (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P)) (𝟙 R₀.obj)).apply_symm_apply v
  change u ≫ (restrictionSheafificationComparison α P).val = v at h
  apply (isIso_iff_of_reflects_iso _ (toSheaf R₀)).1
  apply (J.W_sheafToPresheaf_map_iff_isIso _).1
  change J.W ((PresheafOfModules.toPresheaf R₀.obj).map
    (restrictionSheafificationComparison α P).val)
  apply J.W.of_precomp (W' := J.W) ((PresheafOfModules.toPresheaf R₀.obj).map u) _
  · dsimp only [u]
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact J.W_toSheafify _
  · rw [← CategoryTheory.Functor.map_comp, h]
    change J.W ((PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact J.W_toSheafify _

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_unit
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj)
    (W : C₀ᵒᵖ) (x : P.obj W) :
    (restrictionSheafificationComparison α P).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app
          ((PresheafOfModules.restrictScalars α.hom).obj P)).app W x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P).app W x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars α.hom).obj P)
    (F := (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P))
    (𝟙 R₀.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))
  exact congrArg (fun k ↦ (k.app W) x) h

private theorem sheafification_map_unit_apply
    (P Q : PresheafOfModules.{r} R₀.obj) (f : P ⟶ Q)
    (V : C₀ᵒᵖ) (z : P.obj V) :
    (((PresheafOfModules.sheafification (𝟙 R₀.obj)).map f).val.app V)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app P).app V z) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app Q).app V
        (f.app V z) := by
  exact (congrArg (fun k ↦ k.app V z)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.naturality f)).symm

end

/-- The canonical map from the presheaf tensor to the underlying sheaf tensor.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
private noncomputable def tensorPresheafUnit
    (M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
      (tensorObjIsoSheafification M N).inv.val

set_option maxHeartbeats 50000 in
-- Mixed tensor coefficient structures require additional elaboration.
/-- Restricted extension of scalars is tensoring with the restricted target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison).

Proof: the presheaf tensor of the restricted target ring with M has exactly the
same section modules as restricted sectionwise scalar extension. Both restriction
maps send s tensor m to the tensor of the two restrictions, so the identity maps
form an isomorphism. Sheafify it over R. Restriction commutes with sheafification:
after forgetting to abelian sheaves the comparison is the identity of the same
sheafification, and forgetting reflects isomorphisms. Compose with the canonical
tensor-sheafification comparison. Naturality of the sheafification unit gives the
pure-tensor formula. No flatness or localization assumption is used. -/
private theorem exists_extensionTensorComparison (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (monoidalCategory R).tensorObj
        ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M ≅
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (changeOfRings.{v₀, u₀, r} φ M),
      ∀ (V : C₀ᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
        e.hom.val.app V
          ((tensorPresheafUnit
            ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
              (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M).app V
            ((show ((restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
                  (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val.obj V
              from s) ⊗ₜ[R.obj.obj V] m)) =
        (toSheafify J (changeOfRingsPresheaf.{v₀, u₀, r} φ M).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) := by
  let N := (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let P := changeOfRingsPresheaf.{v₀, u₀, r} φ M
  let SR := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := restrictedTensorPresheafIso φ M
  have := restrictionSheafificationComparison_isIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P
  let e := tensorObjIsoSheafification N M ≪≫ SR.mapIso eP ≪≫
    asIso (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P)
  have he : (tensorObjIsoSheafification N M).inv ≫ e.hom =
      SR.map eP.hom ≫ restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P := by
    dsimp only [e, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, asIso_hom]
    simp only [Iso.inv_hom_id_assoc]
  clear_value e
  refine ⟨e, ?_⟩
  intro V s m
  have hn' := sheafification_map_unit_apply (N.val ⊗ M.val)
    ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P)
    eP.hom V ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)
  have hr' := restrictionSheafificationComparison_unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
  change ((tensorPresheafUnit N M ≫ e.hom.val).app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m) = _
  rw [tensorPresheafUnit, Category.assoc, ← SheafOfModules.comp_val, he,
    SheafOfModules.comp_val]
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [restrictedTensorPresheafIso_hom_app] at hn'
  exact (congrArg ((restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V) hn').trans hr'

open CategoryTheory.CochainPullback

private theorem pure_smul (φ : R ⟶ S)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    extensionTmul φ M U s x = s • extensionTmul φ M U 1 x := by
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
    (changeOfRingsPresheaf φ M)).app U _ =
    s • ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (changeOfRingsPresheaf φ M)).app U _
  rw [← map_smul]
  congr 1
  change s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x =
    (s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x
  rw [mul_one]

private theorem extensionTmul_eq (φ : R ⟶ S)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C₀ᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    extensionTmul φ M U s x =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    (𝟙 _) (changeOfRingsPresheaf φ M)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) _

private theorem transpose_pure (φ : R ⟶ S)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (f : (extensionFunctor φ).obj M ⟶ N) (U : C₀ᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) :
    f.val.app U (extensionTmul φ M U s x) =
      s • (show N.val.obj U from ((extensionAdjunction φ).homEquiv M N f).val.app U x) := by
  rw [pure_smul, map_smul, Adjunction.homEquiv_unit]
  change _ = s • f.val.app U (((extensionAdjunction φ).unit.app M).val.app U x)
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique φ)).1 M U x
  change ((extensionAdjunction φ).unit.app M).val.app U x = _ at hu
  rw [hu]

variable [HasSheafify J AddCommGrpCat.{r}]

private theorem restrictionComposition_hom_app {B : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (c : S ⟶ B) (g : R ⟶ B) (hg : g = φ ≫ c)
    (N : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (U : C₀ᵒᵖ) (z : N.val.obj U) :
    (((SheafOfModules.systemScalarRestrictionComposition φ c g hg).hom.app N).val.app U) z =
      z := rfl

attribute [local irreducible] SheafOfModules.systemScalarRestrictionComposition

private noncomputable def extensionComp {B : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (c : S ⟶ B) (g : R ⟶ B) (hg : g = φ ≫ c) :
    extensionFunctor φ ⋙ extensionFunctor c ≅ extensionFunctor g :=
  Adjunction.leftAdjointUniq
    (((extensionAdjunction φ).comp (extensionAdjunction c)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition φ c g hg))
    (extensionAdjunction g)

-- Comparing successive scalar adjunctions elaborates three coefficient actions.
private theorem extensionComp_pure {B : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (c : S ⟶ B) (g : R ⟶ B) (hg : g = φ ≫ c)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : C₀ᵒᵖ) (z : B.obj.obj U) (s : S.obj.obj U) (x : M.val.obj U) :
    ((extensionComp φ c g hg).hom.app M).val.app U
      (extensionTmul c ((extensionFunctor φ).obj M) U z (extensionTmul φ M U s x)) =
      extensionTmul g M U (z * c.hom.app U s) x := by
  let f := (extensionComp φ c g hg).hom.app M
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((extensionAdjunction φ).comp (extensionAdjunction c)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition φ c g hg)) (extensionAdjunction g) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  have hx := congrArg (fun k ↦ k.val.app U x) h
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    restrictionComposition_hom_app] at hx
  change (((extensionAdjunction φ).homEquiv M _
    ((extensionAdjunction c).homEquiv _ _ f)).val.app U x) =
      ((extensionAdjunction g).unit.app M).val.app U x at hx
  change f.val.app U _ = _
  have hc := transpose_pure c ((extensionFunctor φ).obj M) _ f U z
    (extensionTmul φ M U s x)
  erw [hc]
  have ha := transpose_pure φ M _ ((extensionAdjunction c).homEquiv _ _ f) U s x
  erw [ha, hx]
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique g)).1 M U x
  change ((extensionAdjunction g).unit.app M).val.app U x = _ at hu
  rw [hu]
  change z • (c.hom.app U s • extensionTmul g M U 1 x) = _
  rw [pure_smul g M U (z * c.hom.app U s) x, mul_smul]

attribute [local irreducible] extensionComp

private theorem laxMonoidal_unit_iso
    {A₁ A₂ : Type*} [Category A₁] [Category A₂]
    [MonoidalCategory A₁] [MonoidalCategory A₂]
    (F : A₁ ⥤ A₂) [F.LaxMonoidal] (N : A₁) {M : A₂} (e : F.obj N ≅ M) :
    ((CategoryTheory.Functor.LaxMonoidal.ε F ⊗ₘ e.inv) ≫
      CategoryTheory.Functor.LaxMonoidal.μ F (𝟙_ A₁) N ≫ F.map (λ_ N).hom) ≫ e.hom =
        (λ_ M).hom := by
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.LaxMonoidal.left_unitality_assoc]
  rw [← Category.assoc, leftUnitor_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem tensor_unit_hom
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    let A := PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let ε := asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit
    (tensorObjIsoSheafification (SheafOfModules.unit _) M).hom ≫ A.map (λ_ M.val).hom ≫
      (ε.app M).hom = (λ_ M).hom := by
  dsimp only
  let A := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let ε := asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit
  have hu : (ε.app (SheafOfModules.unit _)).inv = CategoryTheory.Functor.LaxMonoidal.ε A := rfl
  change ((ε.app (SheafOfModules.unit _)).inv ⊗ₘ (ε.app M).inv) ≫
    CategoryTheory.Functor.LaxMonoidal.μ A _ _ ≫ A.map (λ_ M.val).hom ≫ (ε.app M).hom = _
  rw [hu]
  exact laxMonoidal_unit_iso A M.val (ε.app M)

private theorem tensorPresheafUnit_naturality
    {M M' N N' : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorPresheafUnit M N ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ tensorPresheafUnit M' N' := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have h : (tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (f.val ⊗ₘ g.val) ≫ (tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← SheafOfModules.changeOfRingsTensorIso_naturality_independentCoefficients R,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold tensorPresheafUnit
  rw [Category.assoc, ← comp_val, h, comp_val, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (tensorObjIsoSheafification M' N').inv.val)
    (adj.unit.naturality (f.val ⊗ₘ g.val)).symm

private noncomputable def regularIso
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.unit _ ⊗ M ≅ M :=
  tensorObjIsoSheafification (SheafOfModules.unit _) M ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).app M

private theorem regularIso_eq
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    regularIso M = λ_ M := by
  apply Iso.ext
  exact tensor_unit_hom M

private theorem unit_inv_apply
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C₀ᵒᵖ) (x : M.val.obj V) :
    (λ_ M).inv.val.app V x =
      (tensorPresheafUnit (SheafOfModules.unit _) M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  rw [← regularIso_eq]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := (asIso adj.counit).app M
  let f := (SheafOfModules.forget _).mapIso e
  have hc : e.inv.val = adj.unit.app M.val := by
    apply (cancel_mono f.hom).1
    change e.inv.val ≫ e.hom.val = adj.unit.app M.val ≫ e.hom.val
    have h := adj.right_triangle_components M
    exact (congrArg SheafOfModules.Hom.val e.inv_hom_id).trans h.symm
  have hn := adj.unit.naturality (λ_ M.val).inv
  have h := congrArg (fun f ↦ f.app V x) hn
  simp only [regularIso, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv, comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [hc]
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  erw [← h]
  rfl

private theorem exists_levelIso {B : Sheaf J CommRingCat.{r}}
    (φ : R ⟶ S) (c : S ⟶ B) (g : R ⟶ B) (hg : g = φ ≫ c)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N Q : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (eN : N ≅ changeOfRings φ M)
    (p : SheafOfModules.unit _ ⟶ Q)
    (eQ : Q ≅ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map c)).obj
        (SheafOfModules.unit _))
    (hQ : ∀ U, eQ.hom.val.app U (p.val.app U (1 : S.obj.obj U)) = (1 : B.obj.obj U)) :
    ∃ e : Q ⊗ N ≅ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map c)).obj (changeOfRings g M),
      ∀ U (s : S.obj.obj U) (x : M.val.obj U),
        (((λ_ N).inv ≫ p ▷ N ≫ e.hom).val.app U)
          (eN.inv.val.app U (extensionTmul φ M U s x)) =
            extensionTmul g M U (c.hom.app U s) x := by
  obtain ⟨a, ha⟩ := exists_extensionTensorComparison c (changeOfRings φ M)
  let b := (restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map c)).mapIso
      ((extensionComp φ c g hg).app M)
  let e := (eQ ⊗ᵢ eN) ≪≫ a ≪≫ b
  refine ⟨e, ?_⟩
  intro U s x
  let y := extensionTmul φ M U s x
  have he : eN.hom.val.app U (eN.inv.val.app U y) = y :=
    congrArg (fun k ↦ k.val.app U y) eN.inv_hom_id
  have hn := tensorPresheafUnit_naturality (p ≫ eQ.hom) eN.hom
  have hn' := congrArg (fun k ↦ k.app U
    ((1 : S.obj.obj U) ⊗ₜ[S.obj.obj U] eN.inv.val.app U y)) hn
  change (b.hom.val.app U) (a.hom.val.app U
    (((p ▷ N ≫ (eQ ⊗ᵢ eN).hom).val.app U)
      ((λ_ N).inv.val.app U (eN.inv.val.app U y)))) = _
  rw [unit_inv_apply]
  have ht : p ▷ N ≫ (eQ ⊗ᵢ eN).hom = (p ≫ eQ.hom) ⊗ₘ eN.hom := by
    simp only [tensorIso_hom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht]
  change (b.hom.val.app U) (a.hom.val.app U
    (((tensorPresheafUnit (SheafOfModules.unit _) N ≫
      (((p ≫ eQ.hom) ⊗ₘ eN.hom).val)).app U)
      ((1 : S.obj.obj U) ⊗ₜ[S.obj.obj U] eN.inv.val.app U y))) = _
  rw [hn]
  change b.hom.val.app U (a.hom.val.app U
    ((tensorPresheafUnit _ _).app U
      (eQ.hom.val.app U (p.val.app U (1 : S.obj.obj U)) ⊗ₜ[S.obj.obj U]
        eN.hom.val.app U (eN.inv.val.app U y)))) = _
  rw [hQ, he]
  erw [ha U 1 y]
  change ((extensionComp φ c g hg).hom.app M).val.app U
    (extensionTmul c (changeOfRings φ M) U 1 (extensionTmul φ M U s x)) = _
  simpa only [one_mul, extensionFunctor] using extensionComp_pure φ c g hg M U 1 s x

attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private noncomputable def quotientDegreeIso
    (t₀ : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℕ) (i : ℤ) :
    ((((PrincipalQuotientCompletion.quotientTower R t₀).obj P).X i).obj (op n)) ≅
      principalQuotient R t₀ n ⊗ P.X i :=
  HomologicalComplex.Hom.isoApp
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) (principalQuotient R t₀ n) P) i

private theorem quotientMap_degree
    (t₀ : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℕ) (i : ℤ) :
    (PrincipalQuotientCompletion.quotientMap R t₀ P n).f i =
      (λ_ (P.X i)).inv ≫
        cokernel.π (endoPow (globalSectionMultiplication R t₀) (n + 1)) ▷ P.X i ≫
          (quotientDegreeIso t₀ P n i).inv := by
  change ((λ_ (P.X i)).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (SheafOfModules.unit _)).inv ▷ P.X i ≫
    HomologicalComplex.ιMapBifunctor _ P (curriedTensor _) (.up ℤ) 0 i i (zero_add i)) ≫
    (HomologicalComplex.mapBifunctorMap
      ((CochainComplex.singleFunctor _ 0).map
        (cokernel.π (endoPow (globalSectionMultiplication R t₀) (n + 1))))
      (𝟙 P) (curriedTensor _) (.up ℤ)).f i = _
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp]
  dsimp only [quotientDegreeIso, HomologicalComplex.Hom.isoApp,
    HomologicalComplex.eval_map, CategoryTheory.Functor.mapIso_inv]
  (simp only [HomologicalComplex.eval_map, CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.single_map_f_self, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    curriedTensor_map_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    comp_whiskerRight, inv_hom_whiskerRight_assoc]; rfl)

private theorem quotientMap_degree_epi
    (t₀ : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℕ) (i : ℤ) :
    Epi ((PrincipalQuotientCompletion.quotientMap R t₀ P n).f i) := by
  letI := SheafOfModules.symmetricCategory R
  have (M : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  rw [quotientMap_degree]
  have : Epi ((tensorRight (P.X i)).map
      (cokernel.π (endoPow (globalSectionMultiplication R t₀) (n + 1)))) :=
    CategoryTheory.Functor.map_epi _ _
  have hp : Epi (cokernel.π (endoPow (globalSectionMultiplication R t₀) (n + 1)) ▷
      P.X i) := this
  infer_instance

private theorem quotientProduct_π_degree
    (t₀ : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℕ) (i : ℤ) :
    (PrincipalQuotientCompletion.quotientProduct R t₀ P).f i ≫
      (Pi.π (fun m ↦ ((PrincipalQuotientCompletion.quotientTower R t₀).obj P).asFunctor.obj
        (op m)) n).f i = (PrincipalQuotientCompletion.quotientMap R t₀ P n).f i :=
  congrArg (fun f ↦ f.f i) (Pi.lift_comp_π (PrincipalQuotientCompletion.quotientMap R t₀ P) n)

private theorem extension_ext (φ : R ⟶ S)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (f g : changeOfRings φ M ⟶ N)
    (h : ∀ U (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
        g.val.app U ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) : f = g := by
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).homEquiv _ _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change f.val.app U (extensionTmul φ M U 1 x) =
    g.val.app U (extensionTmul φ M U 1 x)
  simpa only [extensionTmul_eq] using h U 1 x

private noncomputable def roosTransposeIso :
    PrincipalQuotientCompletion.transpose R ⋙ roosF ≅ integralOperationsRoosFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    dsimp only [CategoryTheory.Functor.comp_map, NatTrans.id_app,
      Category.id_comp, Category.comp_id,
      integralOperationsRoosFunctor, integralOperationsRoosMap]
    rw [WeilConjectures.cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square f)]
    rfl)

private theorem roosTransposeIso_hom_app
    (T : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    (roosTransposeIso (R := R)).hom.app T = 𝟙 _ := rfl

private noncomputable def roosTowerIso {D : Type*} [Category D]
    (X : D ⥤ CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (W : D ⥤ (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ))
    (τ : X ≅ W ⋙ PrincipalQuotientCompletion.transpose R) :
    X ⋙ roosF ≅ W ⋙ integralOperationsRoosFunctor :=
  CategoryTheory.Functor.isoWhiskerRight τ roosF ≪≫
    CategoryTheory.Functor.associator W (PrincipalQuotientCompletion.transpose R) roosF ≪≫
    CategoryTheory.Functor.isoWhiskerLeft W (roosTransposeIso (R := R))

private theorem roosTowerIso_hom_app {D : Type*} [Category D]
    (X : D ⥤ CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (W : D ⥤ (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ))
    (τ : X ≅ W ⋙ PrincipalQuotientCompletion.transpose R) (P : D) :
    (roosTowerIso X W τ).hom.app P = roosF.map (τ.hom.app P) := by
  dsimp only [roosTowerIso, Iso.trans_hom, NatTrans.comp_app,
    CategoryTheory.Functor.isoWhiskerRight_hom, CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.associator_hom_app]
  rw [roosTransposeIso_hom_app]
  exact Category.comp_id _

attribute [local irreducible] roosTransposeIso quotientDegreeIso roosTowerIso

private theorem towerFactorIso
    {A D : Type*} [Category A] [Abelian A] [Category D]
    (K : D ⥤ CochainComplex A ℤ)
    (X Y : D ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q : ∀ P n, K.obj P ⟶ (X.obj P).asFunctor.obj (op n))
    (a : ∀ P n, K.obj P ⟶ (Y.obj P).asFunctor.obj (op n))
    (qstep : ∀ P n, q P (n + 1) ≫
      (X.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op = q P n)
    (astep : ∀ P n, a P (n + 1) ≫
      (Y.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op = a P n)
    (qnat : ∀ {P P'} (f : P ⟶ P') n, K.map f ≫ q P' n = q P n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (X.map f)).app (op n))
    (anat : ∀ {P P'} (f : P ⟶ P') n, K.map f ≫ a P' n = a P n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (Y.map f)).app (op n))
    (e : ∀ P n i, ((X.obj P).X i).obj (op n) ≅ ((Y.obj P).X i).obj (op n))
    (he : ∀ P n i, (q P n).f i ≫ (e P n i).hom = (a P n).f i)
    (hq : ∀ P n i, Epi ((q P n).f i)) :
    ∃ τ : X ≅ Y, ∀ P n i,
      (q P n).f i ≫ ((τ.hom.app P).f i).app (op n) = (a P n).f i := by
  letI := hq
  have hs (P : D) (n : ℕ) (i : ℤ) :
      ((X.obj P).X i).map (homOfLE (Nat.le_succ n)).op ≫ (e P n i).hom =
        (e P (n + 1) i).hom ≫ ((Y.obj P).X i).map (homOfLE (Nat.le_succ n)).op := by
    apply (cancel_epi ((q P (n + 1)).f i)).1
    have hq := congrArg (fun f ↦ f.f i) (qstep P n)
    have ha := congrArg (fun f ↦ f.f i) (astep P n)
    change (q P (n + 1)).f i ≫
      ((X.obj P).X i).map (homOfLE (Nat.le_succ n)).op = (q P n).f i at hq
    change (a P (n + 1)).f i ≫
      ((Y.obj P).X i).map (homOfLE (Nat.le_succ n)).op = (a P n).f i at ha
    rw [← Category.assoc, hq, he, ← ha, ← he P (n + 1) i, Category.assoc]
  let e₀ (P : D) (i : ℤ) : (X.obj P).X i ≅ (Y.obj P).X i :=
    NatIso.ofComponents (fun n ↦ e P n.unop i)
      (fun {_ _} f ↦
        (NatTrans.ofOpSequence (fun n ↦ (e P n i).hom) (hs P · i)).naturality f)
  have hd (P : D) (i j : ℤ) :
      (e₀ P i).hom ≫ (Y.obj P).d i j = (X.obj P).d i j ≫ (e₀ P j).hom := by
    ext n
    apply (cancel_epi ((q P n.unop).f i)).1
    change (q P n.unop).f i ≫ (e P n.unop i).hom ≫ _ =
      (q P n.unop).f i ≫ ((X.obj P).d i j).app n ≫ (e P n.unop j).hom
    have hq : (q P n.unop).f i ≫ ((X.obj P).d i j).app n =
        (K.obj P).d i j ≫ (q P n.unop).f j := (q P n.unop).comm i j
    have ha : (a P n.unop).f i ≫ ((Y.obj P).d i j).app n =
        (K.obj P).d i j ≫ (a P n.unop).f j := (a P n.unop).comm i j
    rw [← Category.assoc, he, ha, ← Category.assoc, hq, Category.assoc, he]
  let e₁ (P : D) : X.obj P ≅ Y.obj P :=
    HomologicalComplex.Hom.isoOfComponents (e₀ P) (fun i j _ ↦ hd P i j)
  have hn {P P' : D} (f : P ⟶ P') : X.map f ≫ (e₁ P').hom =
      (e₁ P).hom ≫ Y.map f := by
    ext i n
    apply (cancel_epi ((q P n.unop).f i)).1
    change (q P n.unop).f i ≫ ((X.map f).f i).app n ≫ (e P' n.unop i).hom =
      (q P n.unop).f i ≫ (e P n.unop i).hom ≫ ((Y.map f).f i).app n
    have hq := congrArg (fun z ↦ z.f i) (qnat f n.unop)
    have ha := congrArg (fun z ↦ z.f i) (anat f n.unop)
    change (K.map f).f i ≫ (q P' n.unop).f i =
      (q P n.unop).f i ≫ ((X.map f).f i).app n at hq
    change (K.map f).f i ≫ (a P' n.unop).f i =
      (a P n.unop).f i ≫ ((Y.map f).f i).app n at ha
    rw [← Category.assoc, ← hq, Category.assoc, he,
      ← Category.assoc, he, ha]
  exact ⟨NatIso.ofComponents e₁ hn, he⟩

private theorem roosSnd_f {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (roosχ X p).hom ≫ biprod.fst =
      (CochainComplex.mappingCocone.snd (roosU X)).v (p + 1) p (by omega) := by
  have hs (r q : ℤ) (hq : (ComplexShape.up ℤ).Rel r q) :
      HomologicalComplex.homotopyCofiber.sndX (roosU X) r =
        (HomologicalComplex.homotopyCofiber.XIsoBiprod (roosU X) r q hq).hom ≫
          biprod.snd := by
    obtain rfl := (ComplexShape.up ℤ).next_eq' hq
    dsimp only [HomologicalComplex.homotopyCofiber.sndX]
    rw [dite_eq_left hq]
  simp [roosχ, CochainComplex.mappingCocone.snd,
    CochainComplex.HomComplex.Cochain.leftShift_v, CochainComplex.mappingCone.snd,
    show Int.negOnePow 2 = 1 by rfl, hs p (p + 1) rfl]

private theorem complexProduct_hom_ext
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (X : ℕ → CochainComplex A ℤ) (i : ℤ) {M : A}
    (f g : M ⟶ (∏ᶜ X).X i)
    (h : ∀ n, f ≫ (Pi.π X n).f i = g ≫ (Pi.π X n).f i) : f = g := by
  apply (isLimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i)
    (limit.isLimit (Discrete.functor X))).hom_ext
  intro n
  exact h n.as

private theorem roosComparison {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] (P : CochainComplex A ℤ)
    (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (α : P ⟶ roosF.obj X) (β : P ⟶ roosF.obj Y) (f : X ⟶ Y)
    (u : P ⟶ roosP X)
    (hα : ∀ p : ℤ, α.f (p + 1) ≫ (roosχ X p).hom =
      biprod.lift 0 (u.f (p + 1)))
    (hβ : ∀ i : ℤ, β.f i ≫
      (CochainComplex.mappingCocone.snd (roosU Y)).v i (i - 1) (by omega) = 0)
    (h : ∀ i n, (u.f i ≫
      (Pi.π (fun m ↦ X.asFunctor.obj (op m)) n).f i) ≫ (f.f i).app (op n) =
        (β ≫ roosEval Y n).f i) : α ≫ roosF.map f = β := by
  apply HomologicalComplex.hom_ext
  intro i
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (roosχ Y p).hom).1
  rw [HomologicalComplex.comp_f, Category.assoc, roosF_map_χ, ← Category.assoc, hα]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, zero_comp]
    rw [roosSnd_f]
    have hz := hβ (p + 1)
    have h := congrArg (fun f ↦ f ≫
      (HomologicalComplex.XIsoOfEq (roosP Y) (show p + 1 - 1 = p by omega)).hom) hz
    rw [Category.assoc, CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom,
      zero_comp] at h
    exact h.symm
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
    rw [← roosProj_f]
    apply complexProduct_hom_ext
    intro n
    rw [Category.assoc, ← HomologicalComplex.comp_f, roosPmap, Pi.map_π,
      HomologicalComplex.comp_f]
    simpa only [roosEval, HomologicalComplex.comp_f, Category.assoc,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f] using h (p + 1) n

private noncomputable def isoOfComponentIsos {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (η : F ⟶ G) (h : ∀ P, IsIso (η.app P)) : F ≅ G := by
  letI := h
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

private theorem isoOfComponentIsos_hom {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (η : F ⟶ G) (h : ∀ P, IsIso (η.app P)) :
    (isoOfComponentIsos η h).hom = η := rfl

attribute [local irreducible] isoOfComponentIsos

private theorem normalizedComparison_unit {A : Type*} [Category A]
    {X X' Y Y' Z T : A} (a : Z ≅ Y) (e : Y ≅ T) (d : Z ≅ T)
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (c : Y' ⟶ T) (b : X' ⟶ T)
    (hd : a.hom ≫ e.hom = d.hom) (he : e.hom = g ≫ c)
    (hu : u ≫ g = f ≫ v) (hc : v ≫ c = b) :
    u ≫ a.inv ≫ d.hom = f ≫ b := by
  rw [← hd, a.inv_hom_id_assoc, he, ← Category.assoc, hu, Category.assoc, hc]

private theorem normalizedFunctorDescent
    {A B D E G : Type*} [Category A] [Category B] [Category D] [Category E] [Category G]
    (i : G ⥤ A) (Q : A ⥤ D) (H : B ⥤ E) (K : A ⥤ B)
    (T : D ⥤ E) (U : E ⥤ E) (V : B ⥤ B) (S : A ⥤ B) (Ω : D ⥤ E)
    (ε : Q ⋙ T ⟶ K ⋙ H) (ν : H ⋙ U ⟶ V ⋙ H) (μ : 𝟭 E ⟶ U)
    (α : ∀ b : B, b ⟶ V.obj b) (β : K ⟶ S) (δ : K ⋙ V ≅ S)
    (d : (i ⋙ Q) ⋙ Ω ≅ i ⋙ S ⋙ H)
    (unique : ∀ (Z : D ⥤ E) (e : (i ⋙ Q) ⋙ Z ≅ i ⋙ S ⋙ H),
      ∃ a : Ω ≅ Z, CategoryTheory.Functor.isoWhiskerLeft (i ⋙ Q) a ≪≫ e = d)
    (hε : ∀ g : G, IsIso (ε.app (i.obj g)))
    (hν : ∀ g : G, IsIso (ν.app (K.obj (i.obj g))))
    (hμ : ∀ b : B, μ.app (H.obj b) ≫ ν.app b = H.map (α b))
    (hδ : ∀ a : A, α (K.obj a) ≫ δ.hom.app a = β.app a) :
    ∃ c : T ⋙ U ≅ Ω, ∀ g : G,
      μ.app (T.obj (Q.obj (i.obj g))) ≫ c.hom.app (Q.obj (i.obj g)) ≫ d.hom.app g =
        ε.app (i.obj g) ≫ H.map (β.app (i.obj g)) := by
  classical
  let η : (i ⋙ Q) ⋙ (T ⋙ U) ⟶ i ⋙ S ⋙ H :=
    CategoryTheory.Functor.whiskerLeft i
      (CategoryTheory.Functor.whiskerRight ε U ≫
        CategoryTheory.Functor.whiskerLeft K ν ≫ CategoryTheory.Functor.whiskerRight δ.hom H)
  have hη (g : G) : IsIso (η.app g) := by
    letI := hε g
    letI := hν g
    exact (U.mapIso (asIso (ε.app (i.obj g))) ≪≫
      asIso (ν.app (K.obj (i.obj g))) ≪≫ H.mapIso (δ.app (i.obj g))).isIso_hom
  let e := isoOfComponentIsos η hη
  obtain ⟨a, ha⟩ := unique (T ⋙ U) e
  refine ⟨a.symm, ?_⟩
  intro g
  have haG := congrArg (fun z ↦ z.hom.app g) ha
  change a.hom.app (Q.obj (i.obj g)) ≫ e.hom.app g = d.hom.app g at haG
  have hd : μ.app (H.obj (K.obj (i.obj g))) ≫ ν.app (K.obj (i.obj g)) ≫
      H.map (δ.hom.app (i.obj g)) = H.map (β.app (i.obj g)) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ H.map (δ.hom.app (i.obj g))) (hμ _)).trans
        ((H.map_comp _ _).symm.trans (congrArg H.map (hδ _))))
  exact normalizedComparison_unit (a.app (Q.obj (i.obj g))) (e.app g) (d.app g)
    (μ.app (T.obj (Q.obj (i.obj g)))) (μ.app (H.obj (K.obj (i.obj g))))
    (ε.app (i.obj g)) (U.map (ε.app (i.obj g)))
    (ν.app (K.obj (i.obj g)) ≫ H.map (δ.hom.app (i.obj g)))
    (H.map (β.app (i.obj g))) haG
    (congrArg (fun z ↦ z.app g) (isoOfComponentIsos_hom η hη))
    (μ.naturality (ε.app (i.obj g))).symm hd

end CompletedIntegralComparisonProof

namespace CompletedIntegralComparisonProof

section Integral

attribute [local irreducible] limit

open MonoidalCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})

private local instance : EssentiallySmall.{max u (t + 1)} Y.ProEt :=
  essentiallySmallSelf.{u} _
private local instance : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
private local instance : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory

private theorem integralLevelIso_exists
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n)
    (M : integralTowerModules l E Y) (N : integralTowerModules l L Y)
    (hN : N = SheafOfModules.changeOfRings φ M) (n : ℕ) :
    ∃ e : principalQuotient (completedIntegralCommRingSheafUnrestricted l L Y)
        (PrincipalKoszulStrictReplacement.uniformizer l L Y) n ⊗ N ≅
          (integralScalarOrdinaryLevel l E L ι Y n).obj M,
      ∀ U s x,
        (((λ_ N).inv ≫
          cokernel.π (PrincipalKoszulStrictReplacement.multiplication l L Y n) ▷ N ≫
            e.hom).val.app U)
          ((eqToHom hN.symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
              (φ.hom.app U).hom] x))) =
          integralScalarTensorSection l E L ι Y n M U
            ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x := by
  haveI := (PrincipalKoszulStrictReplacement.completed_exact l L Y n).2
  let eQ := asIso (PrincipalKoszulStrictReplacement.quotientComparison l L Y n)
  have hQ : ∀ U, eQ.hom.val.app U
      ((cokernel.π (PrincipalKoszulStrictReplacement.multiplication l L Y n)).val.app U
        (1 : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U))
        = (1 : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) := by
    intro U
    have h := cokernel.π_desc
      (PrincipalKoszulStrictReplacement.multiplication l L Y n)
      (PrincipalKoszulStrictReplacement.projection l L Y n)
      (PrincipalKoszulStrictReplacement.multiplication_projection l L Y n)
    have hh := congrArg (fun f ↦ f.val.app U
      (1 : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)) h
    change eQ.hom.val.app U _ = _ at hh
    refine hh.trans ?_
    change ((PrincipalKoszulStrictReplacement.residue l L Y n).unitHomEquiv
      ((PrincipalKoszulStrictReplacement.residue l L Y n).unitHomEquiv.symm _)).val U =
        (1 : (integralCoefficientCommRingSheaf l L Y n).obj.obj U)
    rw [Equiv.apply_symm_apply]
    rfl
  obtain ⟨e, he⟩ := exists_levelIso φ
    (completedIntegralCommRingProjectionUnrestricted l L Y n)
    (integralScalarRho l E L ι Y n) (hφ n).symm M N _
    (eqToIso hN) (cokernel.π (PrincipalKoszulStrictReplacement.multiplication l L Y n)) eQ hQ
  let a := (integralScalarRestrict l L Y n).mapIso
    (eqToIso (integralScalarReduction_obj l E L ι Y n M)).symm
  refine ⟨e ≪≫ a, ?_⟩
  intro U s x
  change a.hom.val.app U (((λ_ N).inv ≫
    cokernel.π (PrincipalKoszulStrictReplacement.multiplication l L Y n) ▷ N ≫
      e.hom).val.app U _) = _
  have hh := congrArg (a.hom.val.app U) (he U s x)
  have hs := congrArg (fun z ↦ a.hom.val.app U (((λ_ N).inv ≫
      cokernel.π (PrincipalKoszulStrictReplacement.multiplication l L Y n) ▷ N ≫
        e.hom).val.app U ((eqToHom hN.symm).val.app U z)))
    (extensionTmul_eq φ M U s x)
  have ht := congrArg (a.hom.val.app U)
    (extensionTmul_eq (integralScalarRho l E L ι Y n) M U
      ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x)
  refine hs.symm.trans (hh.trans (ht.trans ?_))
  dsimp only [a, integralScalarTensorSection, integralScalarReductionIso,
    integralScalarReduction_obj]
  simp only [CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, eqToIso.inv, eqToHom_app]
  rfl

private theorem completedProjection_step (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U) :
    (integralCoefficientSheafTransition l L Y n).hom.app U
      ((completedIntegralCommRingProjectionUnrestricted l L Y (n + 1)).hom.app U s) =
        (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s := by
  change ((limit.π (integralCoefficientSheafSystem l L Y) (op (n + 1))).hom.app U ≫
    (integralCoefficientSheafTransition l L Y n).hom.app U) s =
      (limit.π (integralCoefficientSheafSystem l L Y) (op n)).hom.app U s
  have hp := limit.w (integralCoefficientSheafSystem l L Y)
    (homOfLE (Nat.le_succ n)).op
  rw [show (integralCoefficientSheafSystem l L Y).map
      (homOfLE (Nat.le_succ n)).op = integralCoefficientSheafTransition l L Y n
    from CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n] at hp
  exact congrArg (fun f ↦ (f.hom.app U).hom s) hp

end Integral

end CompletedIntegralComparisonProof

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

attribute [local irreducible] limit
  PrincipalQuotientCompletion.quotientTower PrincipalQuotientCompletion.quotientRoos
  integralScalarReductionWitness

private theorem integralScalarComparison_unique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
    (T : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y))
    (e : integralOperationsGoodLocalization l E Y ⋙ T ≅ integralScalarOnGood l E L ι Y) :
    ∃ a : integralScalarExtensionOfUniverses l E L ι Y ≅ T,
      CategoryTheory.Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) a ≪≫
        e = integralScalarExtensionComparisonOfUniverses l E L ι Y := by
  exact ((integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.1
    T e).exists

attribute [local irreducible] integralScalarExtensionOfUniverses
  integralScalarExtensionComparisonOfUniverses

-- The comparison combines two derived counits across independent coefficient universes.
private theorem completedIntegralComparison_descent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n)
    (F : @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
      max u (t + 1) + 1, max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (integralCoefficientAbSheafify.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l L Y) φ
      (integralTowerHasDerivedCategory l E Y) (integralTowerHasDerivedCategory l L Y))
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l L Y)
      (integralTowerHasDerivedCategory l L Y)
      (PrincipalKoszulStrictReplacement.uniformizer l L Y))
    (β : F.E.mapHomologicalComplex (.up ℤ) ⟶ integralScalarComplexFunctor l E L ι Y)
    (D : F.E.mapHomologicalComplex (.up ℤ) ⋙
      PrincipalQuotientCompletion.quotientRoos
        (completedIntegralCommRingSheafUnrestricted l L Y)
        (PrincipalKoszulStrictReplacement.uniformizer l L Y) ≅
      integralScalarComplexFunctor l E L ι Y)
    (hD : ∀ P, C.augmentation ((F.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      D.hom.app P = β.app P) :
    ∃ c : F.T ⋙ C.completion ≅ integralScalarExtensionOfUniverses l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        C.unit.app (F.T.obj (DerivedCategory.Q.obj P.obj)) ≫
            c.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P =
          F.ε.app P.obj ≫ DerivedCategory.Q.map (β.app P.obj) := by
  apply CompletedIntegralComparisonProof.normalizedFunctorDescent
    (integralOperationsGoodComplex l E Y).ι DerivedCategory.Q DerivedCategory.Q
    (F.E.mapHomologicalComplex (.up ℤ)) F.T C.completion
    (PrincipalQuotientCompletion.quotientRoos
      (completedIntegralCommRingSheafUnrestricted l L Y)
      (PrincipalKoszulStrictReplacement.uniformizer l L Y))
    (integralScalarComplexFunctor l E L ι Y)
    (integralScalarExtensionOfUniverses l E L ι Y)
    F.ε C.counit C.unit C.augmentation β D
    (integralScalarExtensionComparisonOfUniverses l E L ι Y)
    (integralScalarComparison_unique l E L ι Y)
  · intro P
    exact F.computes P.obj P.property.1
  · intro P
    exact C.computes _ (SheafOfModules.changeOfRings_isKFlat_independentCoefficients
      φ P.obj F.E F.obj_eq F.map_eq P.property.1)
  · exact C.unit_computes
  · exact hD

attribute [local semireducible] PrincipalQuotientCompletion.quotientRoos

-- The normalized tower and cone comparisons involve independent site/coefficient sizes.
/-- Completing ordinary extension is the actual coefficient-reduction Roos functor,
with the specified scalar augmentation, on every input.

Source: Stacks Project, Tags 093M, 03EK, 06YT and 08TC;
Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-quotient-model-comparison).

Proof: on a flat K-flat representative P, ordinary scalar extension is again flat
and K-flat. The normalized completed quotient presentation identifies the target
principal cokernel with its actual constant residue module. Tensor associativity
then identifies (P tensor S) tensor B_n with P tensor B_n: on local pure tensors it
sends (s tensor x) tensor z to residue(s) z tensor x. The inverse sends z tensor x
to (1 tensor x) tensor z. Balancing makes these maps inverse; equality on presheaf
tensors followed by sheafification proves the identities for arbitrary sheaf sections.
The same formulas commute with the quotient transitions and the chain differentials,
so they give an isomorphism of strict towers. Apply the termwise products and the
signed mapping cocone. Both cone blocks use that same tower isomorphism; the quotient
augmentation maps to the displayed scalar augmentation, with zero shifted component.
The counit of C computes on the extended K-flat complex. Its universal property and
that of the ordinary change-of-rings model descend this comparison. On the resolving
subcategory the other side is exactly integralScalarOnGood; its normalized localization
comparison therefore supplies the displayed natural isomorphism on the full derived
category. The two-coordinate uniqueness of the strict cone lift identifies its unit
with any beta satisfying the stated equations. This proof uses no completeness of P,
no finite basis and no boundedness. It also covers the identity inclusion, P=0 and
the empty site. -/
theorem completedIntegralQuotientModelComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n)
    (F : @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
      max u (t + 1) + 1, max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (integralCoefficientAbSheafify.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l L Y) φ
      (integralTowerHasDerivedCategory l E Y) (integralTowerHasDerivedCategory l L Y))
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l L Y)
      (integralTowerHasDerivedCategory l L Y)
      (PrincipalKoszulStrictReplacement.uniformizer l L Y))
    (β : F.E.mapHomologicalComplex (.up ℤ) ⟶ integralScalarComplexFunctor l E L ι Y)
    (hβ :
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((β.app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).f i ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i).val.app U)
          ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  (φ.hom.app U).hom] x))) =
            integralScalarTensorSection l E L ι Y n (P.X i) U
              ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (β.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).v
                i (i - 1) (by omega) = 0)) :
    ∃ c : F.T ⋙ C.completion ≅ integralScalarExtensionOfUniverses l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        C.unit.app (F.T.obj (DerivedCategory.Q.obj P.obj)) ≫
            c.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P =
          F.ε.app P.obj ≫ DerivedCategory.Q.map (β.app P.obj) := by
  classical
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf.{u} _
  letI : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  letI : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let R := completedIntegralCommRingSheafUnrestricted l L Y
  let t₀ : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R)).sections :=
    PrincipalKoszulStrictReplacement.uniformizer l L Y
  let K : CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (ringedSiteModules.{max u (t + 1)}
        (SheafOfModules.derivedChangeRingIndependentCoefficients
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R)) ℤ :=
    F.E.mapHomologicalComplex (.up ℤ)
  let X := K ⋙ PrincipalQuotientCompletion.quotientTower R t₀
  let V := integralScalarTowerFunctor l E L ι Y ⋙ PrincipalQuotientCompletion.transpose R
  let q (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :=
    PrincipalQuotientCompletion.quotientMap R t₀ (K.obj P) n
  let a (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
      K.obj P ⟶ (V.obj P).asFunctor.obj (op n) := β.app P ≫ roosEval (V.obj P) n
  have hβa : ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
      (U : Y.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
      (x : (P.X i).val.obj U),
      ((a P n).f i).val.app U
        ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
            (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
              (φ.hom.app U).hom] x))) =
        integralScalarTensorSection l E L ι Y n (P.X i) U
          ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x :=
    hβ.1
  choose e he using fun (P : CochainComplex (integralTowerModules l E Y) ℤ) n i ↦
    CompletedIntegralComparisonProof.integralLevelIso_exists l E L ι Y φ hφ
      (P.X i) (F.E.obj (P.X i)) (F.obj_eq (P.X i)) n
  let σ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ) :
      ((X.obj P).X i).obj (op n) ≅ ((V.obj P).X i).obj (op n) :=
    CompletedIntegralComparisonProof.quotientDegreeIso (R := R) t₀ (K.obj P) n i ≪≫ e P n i
  have hσ : ∀ P n i, (q P n).f i ≫ (σ P n i).hom = (a P n).f i := by
    intro P n i
    apply (cancel_epi (eqToHom (F.obj_eq (P.X i)).symm)).1
    apply CompletedIntegralComparisonProof.extension_ext φ (P.X i)
    intro U s x
    change (((q P n).f i ≫ (σ P n i).hom).val.app U)
        ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
            (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
              (φ.hom.app U).hom] x))) = _
    dsimp only [σ, Iso.trans_hom, q]
    rw [CompletedIntegralComparisonProof.quotientMap_degree (R := R)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (he P n i U s x).trans (hβa P i n U s x).symm
  have hq (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ) :
      Epi ((q P n).f i) :=
    CompletedIntegralComparisonProof.quotientMap_degree_epi (R := R) t₀ (K.obj P) n i
  have ha : ∀ P n, a P (n + 1) ≫
      (V.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op = a P n := by
    intro P n
    have hstep : (V.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op =
        (integralScalarTransition l E L ι Y n).app P := by
      change ((CategoryTheory.Functor.ofOpSequence (X := fun m ↦ integralScalarLevel l E L ι Y m)
        (integralScalarTransition l E L ι Y)).map (homOfLE (Nat.le_succ n)).op).app P = _
      rw [CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ]
    rw [hstep]
    apply HomologicalComplex.hom_ext
    intro i
    apply (cancel_epi (eqToHom (F.obj_eq (P.X i)).symm)).1
    apply CompletedIntegralComparisonProof.extension_ext φ (P.X i)
    intro U s x
    change (((integralScalarTransition l E L ι Y n).app P).f i).val.app U
      (((a P (n + 1)).f i).val.app U
        ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
            (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
              (φ.hom.app U).hom] x)))) =
      ((a P n).f i).val.app U
        ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
          ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
            (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
              (φ.hom.app U).hom] x)))
    have ht := (integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec
      P i U ((completedIntegralCommRingProjectionUnrestricted l L Y (n + 1)).hom.app U s) x
    exact (congrArg ((((integralScalarTransition l E L ι Y n).app P).f i).val.app U)
      (hβa P i (n + 1) U s x)).trans (ht.trans
        ((congrArg (fun z ↦ integralScalarTensorSection l E L ι Y n (P.X i) U z x)
          (CompletedIntegralComparisonProof.completedProjection_step l L Y n U s)).trans
            (hβa P i n U s x).symm))
  have hn : ∀ {P P'} (f : P ⟶ P') n, K.map f ≫ a P' n = a P n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (V.map f)).app (op n) := by
    intro P P' f n
    have h := β.naturality f
    have hr := (CompletedIntegralComparisonProof.roosTransposeIso (R := R)).hom.naturality
      ((integralScalarTowerFunctor l E L ι Y).map f)
    simp only [CompletedIntegralComparisonProof.roosTransposeIso_hom_app,
      Category.comp_id, Category.id_comp, CategoryTheory.Functor.comp_map] at hr
    change roosF.map (V.map f) = (integralScalarComplexFunctor l E L ι Y).map f at hr
    dsimp only [a]
    rw [← Category.assoc, h, Category.assoc, ← hr, roosEval_natural]
    simp only [Category.assoc]
  obtain ⟨τ, hτ⟩ := CompletedIntegralComparisonProof.towerFactorIso
    (A := ringedSiteModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R)) K X V q a
    (fun P n ↦ PrincipalQuotientCompletion.quotient_transition R t₀ (K.obj P) n) ha
    (fun f n ↦ PrincipalQuotientCompletion.quotient_natural R t₀ (K.map f) n) hn σ hσ hq
  let D : K ⋙ PrincipalQuotientCompletion.quotientRoos R t₀ ≅
      integralScalarComplexFunctor l E L ι Y :=
    CompletedIntegralComparisonProof.roosTowerIso (R := R) X
      (integralScalarTowerFunctor l E L ι Y) τ
  have hDapp P : D.hom.app P = roosF.map (τ.hom.app P) :=
    CompletedIntegralComparisonProof.roosTowerIso_hom_app (R := R) X
      (integralScalarTowerFunctor l E L ι Y) τ P
  apply completedIntegralComparison_descent l E L ι Y φ hφ F C β D
  intro P
  have hr : C.augmentation (K.obj P) ≫ roosF.map (τ.hom.app P) = β.app P := by
    apply CompletedIntegralComparisonProof.roosComparison (K.obj P) (X.obj P) (V.obj P)
      (C.augmentation (K.obj P)) (β.app P) (τ.hom.app P)
      (PrincipalQuotientCompletion.quotientProduct R t₀ (K.obj P))
    · exact C.coordinates (K.obj P)
    · exact hβ.2 P
    · intro i n
      exact (congrArg (fun f ↦ f ≫ ((τ.hom.app P).f i).app (op n))
        (CompletedIntegralComparisonProof.quotientProduct_π_degree
          (R := R) t₀ (K.obj P) n i)).trans (hτ P n i)
  exact (congrArg (fun f ↦ C.augmentation (K.obj P) ≫ f) (hDapp P)).trans hr

end WeilConjectures
