/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientHomZeroClass
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
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
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite

/-! # The coefficient ringed sequence site and canonical functors

Source: Stacks Project, Tags 0941, 06YY, 079P and 07A6
(blueprint: def-coef-ringed-sequence-site).

## Main definitions

- `coefficientSequenceTopology`: the product sequence site with vertical covers.
- `coefficientSequenceCommRingSheaf`: the actual quotient coefficient ring sheaf.
- `coefficientSequenceModules`: module sheaves on this ringed site.
- `coefficientSequenceEvaluation`: exact restriction to the nth vertical slice.
- `coefficientSequenceLimit`: total derived limit after exact scalar restriction.
- `coefficientSequenceProjection`: its canonical, resolution-normalized projections.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Use coefficient-universe sheafification: the generic instance requires a successor.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u c v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

set_option backward.defeqAttrib.useBackward true in
private theorem sequenceInclusion_continuous {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (n : ℕ) :
    (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J) := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro G Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
    have h := hx f₁.2 f₂.2 hg₁ hg₂ (congrArg (fun f ↦ f.2) he)
    have h' := congrArg (G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op) h
    change G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
      (G.obj.map (Prod.mkHom (𝟙 n) f₁.2).op (x g₁ hg₁)) =
        G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
          (G.obj.map (Prod.mkHom (𝟙 n) f₂.2).op (x g₂ hg₂)) at h'
    have he₁ : Prod.mkHom f₁.1 (𝟙 X.2) ≫ Prod.mkHom (𝟙 n) f₁.2 = f₁ := by
      ext <;> simp
    have he₂ : Prod.mkHom f₁.1 (𝟙 X.2) ≫ Prod.mkHom (𝟙 n) f₂.2 = f₂ := by
      ext
      · exact Subsingleton.elim _ _
      · simp
    have hp₁ : G.obj.map f₁.op (x g₁ hg₁) =
        G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
          (G.obj.map (Prod.mkHom (𝟙 n) f₁.2).op (x g₁ hg₁)) := by
      conv_lhs => rw [← he₁, op_comp, G.obj.map_comp]
      rfl
    have hp₂ : G.obj.map f₂.op (x g₂ hg₂) =
        G.obj.map (Prod.mkHom f₁.1 (𝟙 X.2)).op
          (G.obj.map (Prod.mkHom (𝟙 n) f₂.2).op (x g₂ hg₂)) := by
      conv_lhs => rw [← he₂, op_comp, G.obj.map_comp]
      rfl
    exact hp₁.trans (h'.trans hp₂.symm)
  · constructor
    intro X S hS
    change (S.functorPushforward (Prod.sectR n C)).functorPullback
      (Prod.sectR n C) ∈ J X
    exact J.superset_covering
      (fun _ _ hf ↦ Sieve.image_mem_functorPushforward (Prod.sectR n C) S hf) hS

private theorem sequence_isSheaf_of_slices {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type u)
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

set_option backward.defeqAttrib.useBackward true in
private theorem uncurry_slice_eq {C : Type c} [Category.{v} C]
    {A : Type t} [Category.{u} A] (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ A) (n : ℕ) :
    (Prod.sectR n C).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
      Functor.uncurry.obj F = F.obj (op n) := by
  apply CategoryTheory.Functor.ext
    (F := (Prod.sectR n C).op ⋙ (prodOpEquiv (C := ℕ) (D := C)).functor ⋙
      Functor.uncurry.obj F) (G := F.obj (op n)) (fun _ ↦ rfl)

private theorem sequenceEvaluation_exact
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    [HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v u}]
    [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (n : ℕ) {S : Sheaf J RingCat.{max c v u}}
    {R : Sheaf (coefficientSequenceTopology J) RingCat.{max c v u}}
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR n C).sheafPushforwardContinuous
      RingCat.{max c v u} J (coefficientSequenceTopology J)).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{max c v u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{max c v u} φ) := by
  constructor
  · let T := SheafOfModules.forget.{max c v u} S ⋙ PresheafOfModules.toPresheaf S.obj
    have : PreservesFiniteLimits (SheafOfModules.pushforward.{max c v u} φ ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{max c v u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (Prod.sectR n C).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ T
  · let : (Prod.sectR n C).IsCocontinuous J (coefficientSequenceTopology J) :=
      ⟨fun hS ↦ hS⟩
    let H := (Prod.sectR n C).sheafPushforwardContinuous
      AddCommGrpCat.{max c v u} J (coefficientSequenceTopology J)
    have : PreservesColimitsOfSize.{0, 0} H :=
      ((Prod.sectR n C).sheafAdjunctionCocontinuous AddCommGrpCat.{max c v u}
        J (coefficientSequenceTopology J)).leftAdjoint_preservesColimits
    let T := SheafOfModules.toSheaf.{max c v u} S
    have : PreservesFiniteColimits (SheafOfModules.pushforward.{max c v u} φ ⋙ T) := by
      change PreservesFiniteColimits (SheafOfModules.toSheaf.{max c v u} R ⋙ H)
      infer_instance
    have : ReflectsFiniteColimits T :=
      { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves _ T

private theorem diagrams_isGrothendieckAbelian
    (A : Type c) [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    (D : Type u) [SmallCategory D] : IsGrothendieckAbelian.{u} (D ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : D ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (D ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{u, u} (D ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u, u} (D ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact {}

private theorem transition_generic
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u})
    {m n : ℕ} (_h : n ≤ m) (S T : Sheaf J RingCat.{u})
    [Functor.IsContinuous (Prod.sectR m C) J (coefficientSequenceTopology J)]
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR m C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (ψ : T ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (κ : S ⟶ T)
    (α : Prod.sectR n C ⟶ Prod.sectR m C)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat J
      (coefficientSequenceTopology J)).app R = κ ≫ ψ)
    (hm : ∀ (M : SheafOfModules.{u} R) (U : Cᵒᵖ),
      ((SheafOfModules.pushforward φ).obj M).val.presheaf.obj U =
        M.val.presheaf.obj (op (m, U.unop)))
    (hn : ∀ (M : SheafOfModules.{u} R) (U : Cᵒᵖ),
      ((SheafOfModules.restrictScalars κ).obj
        ((SheafOfModules.pushforward ψ).obj M)).val.presheaf.obj U =
          M.val.presheaf.obj (op (n, U.unop))) :
    ∃! τ : SheafOfModules.pushforward.{u} φ ⟶
        SheafOfModules.pushforward.{u} ψ ⋙ SheafOfModules.restrictScalars κ,
      ∀ (M : SheafOfModules.{u} R) (U : Cᵒᵖ),
        eqToHom (hm M U).symm ≫
          (forget₂ (ModuleCat.{u} (S.obj.obj U)) AddCommGrpCat.{u}).map
            ((τ.app M).val.app U) ≫ eqToHom (hn M U) =
          M.val.presheaf.map (α.app U.unop).op := by
  let τ := SheafOfModules.pushforwardNatTrans φ α ≫
    (SheafOfModules.pushforwardCongr he).hom
  refine ⟨τ, ?_, ?_⟩
  · intro M U
    rfl
  · intro σ hσ
    apply NatTrans.ext
    funext M
    ext U x
    exact congrArg (fun f ↦ f x) (hσ M U)

-- Match named functor endpoints before inspecting their concrete construction.
private theorem transition_presented
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u})
    {m n : ℕ} (_h : n ≤ m) (S T : Sheaf J RingCat.{u})
    [Functor.IsContinuous (Prod.sectR m C) J (coefficientSequenceTopology J)]
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (φ : S ⟶ ((Prod.sectR m C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (ψ : T ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (κ : S ⟶ T)
    (α : Prod.sectR n C ⟶ Prod.sectR m C)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat J
      (coefficientSequenceTopology J)).app R = κ ≫ ψ)
    (Fm : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    (Fn : SheafOfModules.{u} R ⥤ SheafOfModules.{u} T)
    (H : SheafOfModules.{u} T ⥤ SheafOfModules.{u} S)
    (hFm : Fm = SheafOfModules.pushforward φ)
    (hFn : Fn = SheafOfModules.pushforward ψ)
    (hH : H = SheafOfModules.restrictScalars κ)
    (hm : ∀ (M : SheafOfModules.{u} R) (U : Cᵒᵖ),
      (Fm.obj M).val.presheaf.obj U =
        M.val.presheaf.obj (op (m, U.unop)))
    (hn : ∀ (M : SheafOfModules.{u} R) (U : Cᵒᵖ),
      (H.obj (Fn.obj M)).val.presheaf.obj U =
          M.val.presheaf.obj (op (n, U.unop))) :
    ∃! τ : Fm ⟶ Fn ⋙ H,
      ∀ (M : SheafOfModules.{u} R) (U : Cᵒᵖ),
        eqToHom (hm M U).symm ≫
          (forget₂ (ModuleCat.{u} (S.obj.obj U)) AddCommGrpCat.{u}).map
            ((τ.app M).val.app U) ≫ eqToHom (hn M U) =
          M.val.presheaf.map (α.app U.unop).op := by
  subst Fm
  subst Fn
  subst H
  exact transition_generic J R _h S T φ ψ κ α he hm hn

private theorem horizontal_map
    {C : Type c} [Category.{v} C] {A : Type*} [Category* A]
    (F : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ A) {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    ((prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj F).map
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op = (F.map (homOfLE h).op).app U := by
  dsimp
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem map_opSequence {A B : Type*} [Category* A] [Category* B]
    (G : A ⥤ B) {X : ℕ → A} (f : ∀ k, X (k + 1) ⟶ X k)
    {m n : ℕ} (h : n ≤ m) :
    G.map ((Functor.ofOpSequence f).map (homOfLE h).op) =
      (Functor.ofOpSequence (X := fun k ↦ G.obj (X k))
        (fun k ↦ G.map (f k))).map (homOfLE h).op := by
  let ε : Functor.ofOpSequence f ⋙ G ⟶
      Functor.ofOpSequence (X := fun k ↦ G.obj (X k)) (fun k ↦ G.map (f k)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun k ↦ by
      dsimp only [Functor.comp_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      simp only [Category.comp_id, Category.id_comp])
  have he := ε.naturality (homOfLE h).op
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at he
  simpa only [Category.comp_id, Category.id_comp, Functor.comp_map] using he

private def verticalNat {C : Type c} [Category.{v} C]
    {m n : ℕ} (h : n ≤ m) : Prod.sectR n C ⟶ Prod.sectR m C where
  app U := Prod.mkHom (homOfLE h) (𝟙 U)
  naturality := fun {_ _} f ↦ by ext <;> simp

private theorem pushforward_restrict_obj
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u})
    {A B : Sheaf J RingCat.{u}} (n : ℕ)
    [Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (p : A ⟶ B)
    (φ : B ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R) (M : SheafOfModules.{u} R) :
    (SheafOfModules.pushforward (p ≫ φ)).obj M =
      (SheafOfModules.restrictScalars p).obj ((SheafOfModules.pushforward φ).obj M) := by
  rfl

private theorem towers_generic
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{u}) (A : Sheaf J RingCat.{u})
    [∀ n : ℕ, Functor.IsContinuous (Prod.sectR n C) J (coefficientSequenceTopology J)]
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat J
      (coefficientSequenceTopology J)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m),
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans (verticalNat h) RingCat J
        (coefficientSequenceTopology J)).app R = ρ n) :
    ∃ U : SheafOfModules.{u} R ⥤ (ℕᵒᵖ ⥤ SheafOfModules.{u} A),
      (∀ (M : SheafOfModules.{u} R) (n : ℕ),
        (U.obj M).obj (op n) = (SheafOfModules.pushforward (ρ n)).obj M) ∧
      (∀ (M : SheafOfModules.{u} R) (m n : ℕ) (h : n ≤ m) (V : Cᵒᵖ),
        HEq (fun x : ((U.obj M).obj (op m)).val.obj V ↦
          (((U.obj M).map (homOfLE h).op).val.app V) x)
          (fun x : M.val.obj (op (m, V.unop)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x)) ∧
      (∀ {M N : SheafOfModules.{u} R} (f : M ⟶ N) (n : ℕ) (V : Cᵒᵖ),
        HEq (fun x : ((U.obj M).obj (op n)).val.obj V ↦
          (((U.map f).app (op n)).val.app V) x)
          (fun x : M.val.obj (op (n, V.unop)) ↦ f.val.app (op (n, V.unop)) x)) := by
  let τ {m n : ℕ} (h : n ≤ m) :
      SheafOfModules.pushforward.{u} (ρ m) ⟶ SheafOfModules.pushforward.{u} (ρ n) :=
    SheafOfModules.pushforwardNatTrans (ρ m) (verticalNat h) ≫
      (SheafOfModules.pushforwardCongr (hρ h)).hom
  let U : SheafOfModules.{u} R ⥤ (ℕᵒᵖ ⥤ SheafOfModules.{u} A) :=
    { obj M :=
        { obj n := (SheafOfModules.pushforward (ρ n.unop)).obj M
          map {m n} f := (τ (leOfHom f.unop)).app M
          map_id n := by
            ext V x
            change M.val.presheaf.map _ x = x
            have he : (verticalNat (Nat.le_refl n.unop)).app V.unop = 𝟙 _ := by
              apply Prod.hom_ext
              · apply Subsingleton.elim
              · rfl
            change M.val.presheaf.map ((verticalNat _).app V.unop).op x = x
            rw [he, op_id, M.val.presheaf.map_id]
            rfl
          map_comp {k m n} f g := by
            ext V x
            change M.val.presheaf.map _ x = M.val.presheaf.map _
              (M.val.presheaf.map _ x)
            rw [← Functor.map_comp_apply]
            congr 3
            apply Quiver.Hom.unop_inj
            apply Prod.hom_ext
            · apply Subsingleton.elim
            · simp [verticalNat] }
      map f :=
        { app n := (SheafOfModules.pushforward (ρ n.unop)).map f
          naturality {m n} g := by
            ext V x
            exact congrArg (fun k ↦ k x) (f.val.naturality
              ((verticalNat (leOfHom g.unop)).app V.unop).op) }
      map_id M := by ext n V x; rfl
      map_comp f g := by ext n V x; rfl }
  exact ⟨U, fun _ _ ↦ rfl, fun _ _ _ _ _ ↦ HEq.rfl, fun {_ _} _ _ _ ↦ HEq.rfl⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The same quotient transition with its commutative structure retained.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingTransition (n : ℕ) :
    integralCoefficientCommRingSheaf l E W (n + 1) ⟶
      integralCoefficientCommRingSheaf l E W n where
  hom :=
    { app := fun U ↦ CommRingCat.ofHom
        ((integralCoefficientSheafTransition l E W n).hom.app U).hom
      naturality := fun {_ _} f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((integralCoefficientSheafTransition l E W n).hom.naturality f) }

/-- The commutative coefficient sequence, with precisely the recorded quotient maps.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingSystem :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)} :=
  Functor.ofOpSequence (coefficientSequenceCommRingTransition l E W)

/-- The actual sectionwise commutative ring presheaf on the sequence site.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingPresheaf :
    (ℕ × W.ProEt)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)} :=
  (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor ⋙ Functor.uncurry.obj
    (coefficientSequenceCommRingSystem l E W ⋙
      sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)})

/-- The commutative sequence ring is a sheaf for the vertical topology.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: glue in the recorded finite coefficient sheaves:
use the vertical covering slice to glue in B_n, then use separatedness on its
pullbacks to verify compatibility with every horizontal arrow. All ring operations
are preserved because they are preserved by the recorded coefficient restrictions. -/
theorem coefficientSequenceCommRingPresheaf_isSheaf :
    Presheaf.IsSheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingPresheaf l E W) := by
  intro A
  apply sequence_isSheaf_of_slices
  intro n
  dsimp only [coefficientSequenceCommRingPresheaf]
  rw [← Functor.assoc, uncurry_slice_eq]
  exact ((coefficientSequenceCommRingSystem l E W).obj (op n)).property A

/-- The same sequence ring sheaf with commutativity retained.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceCommRingSheaf :
    Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
      CommRingCat.{max u (t + 1)} :=
  ⟨coefficientSequenceCommRingPresheaf l E W,
    coefficientSequenceCommRingPresheaf_isSheaf l E W⟩

/-- Strict semilinear systems as modules over the actual commutative sequence ring.
The vertical sheaf condition is exactly the component sheaf condition; horizontal
restrictions are quotient-linear transition maps.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientSequenceModules :=
  ringedSiteModules.{max u (t + 1)}
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E W))

/-- The ordinary unbounded localization of strict coefficient systems.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
@[reducible]
noncomputable def coefficientSequenceDerived :=
  @DerivedCategory (coefficientSequenceModules l E W) _ _ (HasDerivedCategory.standard _)

/-- The standard localization instance for strict coefficient-system modules.
Source: Stacks 05RU, 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceHasDerived :
    HasDerivedCategory (coefficientSequenceModules l E W) := HasDerivedCategory.standard _

/-- The recorded derived scalar extension with its finite-category codomain displayed.
Source: Stacks 06YY, 07A6 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteDerivedExtension (n : ℕ) :
    DerivedCategory (scalarReductionSource l E W) ⥤ normalizedDVRDerived l E W n :=
  scalarReductionDerivedExtension l E W n

/-- The recorded derived restriction with its finite-category domain displayed.
Source: Stacks 03CZ, 07A6 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteDerivedRestriction (n : ℕ) :
    normalizedDVRDerived l E W n ⥤ DerivedCategory (scalarReductionSource l E W) :=
  scalarReductionDerivedRestriction l E W n

/-- The existing scalar adjunction with its specified K-flat unit normalization.
Source: Stacks 07A6 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteAdjunction (n : ℕ) :
    coefficientFiniteDerivedExtension l E W n ⊣ coefficientFiniteDerivedRestriction l E W n :=
  (derivedScalarExtensionRestrictionAdjunction l E W n).choose

/-- Derived internal Hom taken on the actual sequence site before evaluation.
Source: Stacks 0A95 and 0941
(blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceInternalHom :
    (coefficientSequenceDerived l E W)ᵒᵖ × coefficientSequenceDerived l E W ⥤
      coefficientSequenceDerived l E W :=
  @derivedInternalHomOfUniverses.{t + 1, t, u}
    _ _ (coefficientSequenceTopology (Scheme.ProEt.topology W)) _ _
      (coefficientSequenceCommRingSheaf l E W) (HasDerivedCategory.standard _)

/-- Evaluation of the actual sequence ring is the recorded finite coefficient sheaf.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the object at (n,U) is B_n(U). Its vertical restriction is B_n(f), since the
horizontal quotient along the identity is the identity. Functor extensionality
identifies the underlying presheaves; sheaf-condition proofs are irrelevant. -/
theorem coefficientSequenceEvaluationRing_eq (n : ℕ) :
    ((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat.{max u (t + 1)}
      (Scheme.ProEt.topology W) (coefficientSequenceTopology (Scheme.ProEt.topology W))).obj
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            (coefficientSequenceCommRingSheaf l E W)) = integralCoefficientSheaf l E W n := by
  apply ObjectProperty.FullSubcategory.ext
  change (Prod.sectR n W.ProEt).op ⋙
    (coefficientSequenceCommRingPresheaf l E W ⋙ forget₂ CommRingCat RingCat) = _
  rw [← Functor.assoc]
  change ((Prod.sectR n W.ProEt).op ⋙
    (prodOpEquiv (C := ℕ) (D := W.ProEt)).functor ⋙
      Functor.uncurry.obj (coefficientSequenceCommRingSystem l E W ⋙
        sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat)) ⋙
          forget₂ CommRingCat RingCat = _
  rw [uncurry_slice_eq]
  rfl

/-- Evaluation of a strict coefficient system, with the canonical ring identification.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceEvaluation (n : ℕ) :
    coefficientSequenceModules l E W ⥤ normalizedDVRModules l E W n :=
  SheafOfModules.pushforward (F := Prod.sectR n W.ProEt)
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)

/-- Componentwise exactness of coefficient evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: kernels of module presheaves are sectionwise; cokernels are their sectionwise
cokernels followed by sheafification. Vertical gluing computes the same sheafification
at each level. Hence both kernel and cokernel comparisons are isomorphisms at every
level, and the additive evaluation functor preserves finite limits and colimits. -/
theorem coefficientSequenceEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (coefficientSequenceEvaluation l E W n) ∧
      PreservesFiniteColimits (coefficientSequenceEvaluation l E W n) := by
  exact sequenceEvaluation_exact.{u, t+1, t} (C := W.ProEt) (Scheme.ProEt.topology W) n
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm)

/-- The finite-limit part of componentwise exact evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluation_limits (n : ℕ) :
    PreservesFiniteLimits (coefficientSequenceEvaluation l E W n) :=
  (coefficientSequenceEvaluation_exact l E W n).1

/-- The finite-colimit part of componentwise exact evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluation_colimits (n : ℕ) :
    PreservesFiniteColimits (coefficientSequenceEvaluation l E W n) :=
  (coefficientSequenceEvaluation_exact l E W n).2

/-- Evaluation is additive because addition of module maps is componentwise.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: both sides of preservation of addition have at (n,U) the sum of the same
underlying linear maps. Module-sheaf morphism extensionality gives equality. -/
theorem coefficientSequenceEvaluation_additive (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).Additive := by
  constructor
  intro M N f g
  ext U x
  rfl

/-- The additive structure of canonical evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceEvaluation_additiveInstance (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).Additive :=
  coefficientSequenceEvaluation_additive l E W n

/-- Ordinary derived evaluation descended from exact sequence evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
@[reducible]
noncomputable def coefficientSequenceDerivedEvaluation (n : ℕ) :
    coefficientSequenceDerived l E W ⥤ normalizedDVRDerived l E W n :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  (coefficientSequenceEvaluation l E W n).mapDerivedCategory

/-- Evaluation retains the actual underlying abelian section object.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: unfold the continuous module pushforward. Scalar restriction changes the
module action only, so forgetting the action gives exactly the section at (n,U). -/
theorem coefficientSequenceEvaluationAb_eq
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    ((coefficientSequenceEvaluation l E W n).obj M).val.presheaf.obj U =
      M.val.presheaf.obj (op (n, U.unop)) := by
  rfl

private theorem restrictScalars_presheaf_obj
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (f : R ⟶ S) (M : SheafOfModules.{t} S)
    (U : Cᵒᵖ) :
    ((SheafOfModules.restrictScalars f).obj M).val.presheaf.obj U =
      M.val.presheaf.obj U := rfl

/-- Restricting a finite evaluation retains the same underlying abelian sections.
Source: Stacks 0941, 03CZ (blueprint: def-coef-ringed-sequence-site).
Proof: the finite quotient restriction leaves the abelian presheaf unchanged.
Then apply the preceding evaluation equality. -/
theorem coefficientSequenceRestrictedEvaluationAb_eq
    (M : coefficientSequenceModules l E W) {m n : ℕ} (h : n ≤ m) (U : W.ProEtᵒᵖ) :
    ((normalizedDVRModuleRes l E W h).obj
      ((coefficientSequenceEvaluation l E W n).obj M)).val.presheaf.obj U =
        M.val.presheaf.obj (op (n, U.unop)) := by
  exact (restrictScalars_presheaf_obj (normalizedDVRQuotient l E W h)
    ((coefficientSequenceEvaluation l E W n).obj M) U).trans
      (coefficientSequenceEvaluationAb_eq l E W M n U)

-- The concrete quotient tower comparison unfolds several scalar restriction interfaces.
private theorem coefficientSequenceRingHorizontal {m n : ℕ} (h : n ≤ m) :
    eqToHom (coefficientSequenceEvaluationRing_eq l E W m).symm ≫
      (Functor.sheafPushforwardContinuousNatTrans (verticalNat h) RingCat
        (Scheme.ProEt.topology W)
        (coefficientSequenceTopology (Scheme.ProEt.topology W))).app
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
            RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E W)) =
      normalizedDVRQuotient l E W h ≫
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
  have hsys :
    (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((coefficientSequenceCommRingSystem l E W).map (homOfLE h).op) =
      normalizedDVRQuotient l E W h := by
    exact map_opSequence (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat RingCat)) (coefficientSequenceCommRingTransition l E W) h
  let α := verticalNat (C := W.ProEt) h
  let φm := eqToHom (coefficientSequenceEvaluationRing_eq l E W m).symm
  let φn := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  have he : φm ≫ (Functor.sheafPushforwardContinuousNatTrans α RingCat.{max u (t + 1)}
      (Scheme.ProEt.topology W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))).app
        ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          (coefficientSequenceCommRingSheaf l E W)) =
      normalizedDVRQuotient l E W h ≫ φn := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have hm : φm.hom.app U = 𝟙 _ := by
      dsimp only [φm]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    have hn : φn.hom.app U = 𝟙 _ := by
      dsimp only [φn]
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change φm.hom.app U ≫ _ = _ ≫ φn.hom.app U
    rw [hm, hn, Category.id_comp, Category.comp_id]
    change (((coefficientSequenceCommRingPresheaf l E W) ⋙
      forget₂ CommRingCat RingCat).map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op) = _
    exact (congrArg (fun f ↦ (forget₂ CommRingCat RingCat).map f)
      (horizontal_map (coefficientSequenceCommRingSystem l E W ⋙
        sheafToPresheaf (Scheme.ProEt.topology W) CommRingCat) h U)).trans
      (congrArg (fun f ↦ f.hom.app U) hsys)
  exact he

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Comparing the concrete pushforward and scalar-restriction interfaces is expensive.
/-- The actual quotient transition, characterized on every section of every system.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the horizontal restriction in the module presheaf is linear over B_m with
its target action restricted by B_m→B_n. Its site naturality gives a module-sheaf
map, and naturality in the input module gives the displayed transformation.
Extensionality on all sections proves uniqueness. -/
theorem coefficientSequenceTransition_exists {m n : ℕ} (h : n ≤ m) :
    ∃! τ : coefficientSequenceEvaluation l E W m ⟶
      coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h,
      ∀ (M : coefficientSequenceModules l E W) (U : W.ProEtᵒᵖ),
        eqToHom (coefficientSequenceEvaluationAb_eq l E W M m U).symm ≫
          (forget₂ (ModuleCat.{max u (t+1)}
            ((integralCoefficientSheaf l E W m).obj.obj U))
              AddCommGrpCat.{max u (t+1)}).map ((τ.app M).val.app U) ≫
          eqToHom (coefficientSequenceRestrictedEvaluationAb_eq l E W M h U) =
        M.val.presheaf.map
          ((Prod.mkHom (homOfLE h) (𝟙 U.unop) : (n, U.unop) ⟶ (m, U.unop))).op := by
  let α := verticalNat (C := W.ProEt) h
  let φm := eqToHom (coefficientSequenceEvaluationRing_eq l E W m).symm
  let φn := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  have he := coefficientSequenceRingHorizontal l E W h
  have hgeneric := transition_presented (Scheme.ProEt.topology W)
    ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)) h
    (integralCoefficientSheaf l E W m) (integralCoefficientSheaf l E W n)
    φm φn (normalizedDVRQuotient l E W h) α he
    (coefficientSequenceEvaluation l E W m) (coefficientSequenceEvaluation l E W n)
    (normalizedDVRModuleRes l E W h) (by rfl) (by rfl) (by rfl)
    (fun M U ↦ coefficientSequenceEvaluationAb_eq l E W M m U)
    (fun M U ↦ coefficientSequenceRestrictedEvaluationAb_eq l E W M h U)
  exact hgeneric

/-- The canonical quotient transition, chosen by its unique actual restriction formula.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceTransition {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceEvaluation l E W m ⟶
      coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h :=
  (coefficientSequenceTransition_exists l E W h).exists.choose

/-- The same transition descended to the ordinary derived system category.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceDerivedTransition {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedEvaluation l E W m ⟶
      coefficientSequenceDerivedEvaluation l E W n ⋙ normalizedDVRRes l E W h :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W m)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (ComplexShape.up ℤ))
    _ _ (coefficientSequenceEvaluation l E W m).mapDerivedCategory
    ((coefficientSequenceEvaluation l E W n ⋙ normalizedDVRModuleRes l E W h).mapDerivedCategory)
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (coefficientSequenceTransition l E W h)
        (ComplexShape.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E W n)
      (normalizedDVRModuleRes l E W h)).inv

/-- Normalization of an actual derived semilinear system, using the dependency's
universal derived tensor/restriction criterion for its specified transitions.
Source: Stacks 0941, normalized coefficient systems
(blueprint: def-coef-ringed-sequence-site). -/
def IsNormalizedCoefficientSequence (N : coefficientSequenceDerived l E W) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m) (P : normalizedDVRDerived l E W n),
    Function.Bijective
      (fun f : (coefficientSequenceDerivedEvaluation l E W n).obj N ⟶ P ↦
        (coefficientSequenceDerivedTransition l E W h).app N ≫
          (normalizedDVRRes l E W h).map f)

private theorem moduleSheaf_hom_eq_of_heq
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M M' N N' : SheafOfModules.{t} R}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : ∀ V : Cᵒᵖ, HEq (fun x ↦ f.val.app V x) (fun x ↦ g.val.app V x)) :
    f = eqToHom hM ≫ g ≫ eqToHom hN.symm := by
  subst M' N'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext V x
  exact congrFun (eq_of_heq (h V)) x

-- Comparing composite module pushforwards with restriction uses concrete quotient actions.
/-- Exact restriction of scalars as an actual strict tower, with unchanged sections.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: restrict the action at n by the actual completed coefficient projection.
The limit cone equations make every horizontal restriction completed-linear.
Use the original module-presheaf restrictions for the tower arrows and original
component maps for morphisms. Their functor equations are those of the presheaves.
Extensionality on objects and section maps proves uniqueness of this functor. -/
theorem coefficientSequenceRestriction_exists :
    ∃! U : coefficientSequenceModules l E W ⥤
      (ℕᵒᵖ ⥤ scalarReductionSource l E W),
      (∀ (M : coefficientSequenceModules l E W) (n : ℕ),
        (U.obj M).obj (op n) = (scalarReductionRestriction l E W n).obj
          ((coefficientSequenceEvaluation l E W n).obj M)) ∧
      (∀ (M : coefficientSequenceModules l E W) (m n : ℕ) (h : n ≤ m)
        (V : W.ProEtᵒᵖ),
        HEq (fun x : ((U.obj M).obj (op m)).val.obj V ↦
          (((U.obj M).map (homOfLE h).op).val.app V) x)
          (fun x : M.val.obj (op (m, V.unop)) ↦
            M.val.map
        (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x)) ∧
      (∀ {M N : coefficientSequenceModules l E W} (f : M ⟶ N) (n : ℕ)
        (V : W.ProEtᵒᵖ),
        HEq (fun x : ((U.obj M).obj (op n)).val.obj V ↦
          (((U.map f).app (op n)).val.app V) x)
          (fun x : M.val.obj (op (n, V.unop)) ↦ f.val.app (op (n, V.unop)) x)) := by
  let R := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      (coefficientSequenceCommRingSheaf l E W)
  let A := SheafOfModules.derivedChangeRingIndependentCoefficients
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)
  let p (n : ℕ) : A ⟶ integralCoefficientSheaf l E W n :=
    (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)
  let φ (n : ℕ) := eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm
  let ρ (n : ℕ) : A ⟶ ((Prod.sectR n W.ProEt).sheafPushforwardContinuous RingCat
      (Scheme.ProEt.topology W)
      (coefficientSequenceTopology (Scheme.ProEt.topology W))).obj R := p n ≫ φ n
  have hp (m n : ℕ) (h : n ≤ m) :
      p m ≫ normalizedDVRQuotient l E W h = p n := by
    exact limit.w (integralCoefficientSheafSystem l E W) (homOfLE h).op
  have hρ {m n : ℕ} (h : n ≤ m) :
      ρ m ≫ (Functor.sheafPushforwardContinuousNatTrans (verticalNat h) RingCat
        (Scheme.ProEt.topology W)
        (coefficientSequenceTopology (Scheme.ProEt.topology W))).app R = ρ n := by
    dsimp only [ρ]
    rw [Category.assoc, coefficientSequenceRingHorizontal, ← Category.assoc, hp]
  obtain ⟨U, hU⟩ := towers_generic (Scheme.ProEt.topology W) R A ρ (fun h ↦ hρ h)
  have hobj (M : coefficientSequenceModules l E W) (n : ℕ) :
      (U.obj M).obj (op n) = (scalarReductionRestriction l E W n).obj
        ((coefficientSequenceEvaluation l E W n).obj M) := by
    exact (hU.1 M n).trans
      (pushforward_restrict_obj (Scheme.ProEt.topology W) R n (p n) (φ n) M)
  refine ⟨U, ⟨hobj, hU.2⟩, ?_⟩
  intro V hV
  have hVU (M : coefficientSequenceModules l E W) : V.obj M = U.obj M := by
    refine CategoryTheory.Functor.ext (fun n ↦ (hV.1 M n.unop).trans
      (hobj M n.unop).symm) ?_
    intro m n f
    refine moduleSheaf_hom_eq_of_heq
      ((hV.1 M m.unop).trans (hobj M m.unop).symm)
      ((hV.1 M n.unop).trans (hobj M n.unop).symm) _ _ ?_
    intro X
    exact (hV.2.1 M m.unop n.unop (leOfHom f.unop) X).trans
      (hU.2.1 M m.unop n.unop (leOfHom f.unop) X).symm
  refine CategoryTheory.Functor.ext hVU ?_
  intro M N f
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, eqToHom_app]
  refine moduleSheaf_hom_eq_of_heq
    ((hV.1 M n.unop).trans (hobj M n.unop).symm)
    ((hV.1 N n.unop).trans (hobj N n.unop).symm) _ _ ?_
  intro X
  exact (hV.2.2 f n.unop X).trans (hU.2.2 f n.unop X).symm

/-- Termwise restriction is fixed by the actual quotient projections and section maps.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceRestriction : coefficientSequenceModules l E W ⥤
    (ℕᵒᵖ ⥤ scalarReductionSource l E W) :=
  (coefficientSequenceRestriction_exists l E W).exists.choose

/-- Restriction followed by evaluation agrees with actual scalar restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: the object equality is the first characterization of coefficientSequenceRestriction.
The morphism equality is its sectionwise characterization. Module-sheaf extensionality
and functor extensionality give the asserted equality, including the specified maps. -/
theorem coefficientSequenceRestriction_evaluation (n : ℕ) :
    coefficientSequenceRestriction l E W ⋙
      (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) =
    coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n := by
  have h := (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine CategoryTheory.Functor.ext (fun M ↦ h.1 M n) ?_
  intro M N f
  refine moduleSheaf_hom_eq_of_heq (h.1 M n) (h.1 N n) _ _ ?_
  intro V
  exact h.2.2 f n V

/-- Exactness of termwise restriction: underlying abelian sheaves do not change.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: kernels and cokernels are computed levelwise in the system category and
in the constant-coefficient tower category. Restriction changes only the scalar
action, so preserves these computations and componentwise addition. -/
theorem coefficientSequenceRestriction_exact :
    (coefficientSequenceRestriction l E W).Additive ∧
      PreservesFiniteLimits (coefficientSequenceRestriction l E W) ∧
      PreservesFiniteColimits (coefficientSequenceRestriction l E W) := by
  have hlim : PreservesFiniteLimits (coefficientSequenceRestriction l E W) := by
    constructor
    intro J _ _
    apply preservesLimitsOfShape_of_evaluation
    intro n
    rw [coefficientSequenceRestriction_evaluation]
    have := (scalarReductionRestriction_exact l E W n.unop).1
    infer_instance
  have hcolim : PreservesFiniteColimits (coefficientSequenceRestriction l E W) := by
    constructor
    intro J _ _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    rw [coefficientSequenceRestriction_evaluation]
    have := (scalarReductionRestriction_exact l E W n.unop).2
    infer_instance
  refine ⟨?_, hlim, hcolim⟩
  exact leftExactFunctor_le_additiveFunctor _ _ _ (by rw [leftExactFunctor_iff]; infer_instance)

/-- Additivity of exact coefficient restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceRestriction_additive :
    (coefficientSequenceRestriction l E W).Additive :=
  (coefficientSequenceRestriction_exact l E W).1

/-- Finite-limit preservation for exact coefficient restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceRestriction_limits :
    PreservesFiniteLimits (coefficientSequenceRestriction l E W) :=
  (coefficientSequenceRestriction_exact l E W).2.1

/-- Finite-colimit preservation for exact coefficient restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable instance coefficientSequenceRestriction_colimits :
    PreservesFiniteColimits (coefficientSequenceRestriction l E W) :=
  (coefficientSequenceRestriction_exact l E W).2.2

/-- The standard unbounded derived category of completed-coefficient towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
@[reducible]
noncomputable def coefficientSequenceRestrictedDerived :=
  @DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E W) _ _ (HasDerivedCategory.standard _)

/-- The exact functor U_W on ordinary unbounded derived system categories.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
@[reducible]
noncomputable def coefficientSequenceDerivedRestriction :
    coefficientSequenceDerived l E W ⥤ coefficientSequenceRestrictedDerived l E W :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  (coefficientSequenceRestriction l E W).mapDerivedCategory

/-- Canonical total inverse limit of strict completed-coefficient towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientConstantTowerLimit :
    coefficientSequenceRestrictedDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W) :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W).rightDerivedFunctor

/-- The specified total limit after exact termwise scalar restriction.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceLimit :
    coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W) :=
  coefficientSequenceDerivedRestriction l E W ⋙ coefficientConstantTowerLimit l E W

/-- The exact evaluation of a constant-coefficient derived tower.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientConstantTowerEvaluation (n : ℕ) :
    coefficientSequenceRestrictedDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W) :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategory

/-- The localization comparison for exact constant-tower evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable abbrev coefficientConstantTowerEvaluationFactors (n : ℕ) :=
  ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategoryFactors

private theorem derived_projection_exists
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : F ⟶ G) :
    ∃! π : F.rightDerivedFunctor ⟶ G.mapDerivedCategory,
      ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
        π.app (DerivedCategory.Q.obj I) ≫ G.mapDerivedCategoryFactors.hom.app I =
          (F.rightDerivedFunctorObjQIso I).hom ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I) := by
  let β := Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ))
    DerivedCategory.Qh ≫ G.mapDerivedCategoryFactorsh.inv
  let π := F.rightDerivedFunctor.rightDerivedDesc F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso A (.up ℤ)) G.mapDerivedCategory β
  have hπ (I : CochainComplex A ℤ) [I.IsKInjective] :
      π.app (DerivedCategory.Q.obj I) ≫ G.mapDerivedCategoryFactors.hom.app I =
        (F.rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I) := by
    have h := Functor.rightDerived_fac_app F.rightDerivedFunctor
      F.rightDerivedFunctorUnit (HomotopyCategory.quasiIso A (.up ℤ))
      G.mapDerivedCategory β ((HomotopyCategory.quotient A (.up ℤ)).obj I)
    have hqA : (DerivedCategory.quotientCompQhIso A).hom.app I = 𝟙 _ := by
      simp [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom]
      rfl
    have hqAi : (DerivedCategory.quotientCompQhIso A).inv.app I = 𝟙 _ := by
      simp [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_inv]
      rfl
    have hqB (K : CochainComplex B ℤ) :
        (DerivedCategory.quotientCompQhIso B).hom.app K = 𝟙 _ := by
      simp [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom]
      rfl
    have hqBi (K : CochainComplex B ℤ) :
        (DerivedCategory.quotientCompQhIso B).inv.app K = 𝟙 _ := by
      simp [DerivedCategory.quotientCompQhIso,
        HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_inv]
      rfl
    have hf : G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj I) =
          G.mapDerivedCategoryFactors.hom.app I := by
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      erw [hqA, hqBi, G.mapDerivedCategory.map_id, Category.id_comp]
      have hg : (G.mapHomotopyCategoryFactors (.up ℤ)).inv.app I = 𝟙 _ := rfl
      erw [hg, DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
    have hu : F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
          (F.rightDerivedFunctorObjQIso I).hom = 𝟙 _ := by
      dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, asIso_inv, Iso.app]
      erw [hqAi, hqB, F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
      exact IsIso.hom_inv_id _
    apply (cancel_epi (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I))).mp
    change F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
        π.app (DerivedCategory.Q.obj I) = _ at h
    erw [← Category.assoc, ← hf, h]
    rw [← Category.assoc, hu]
    simp only [Category.id_comp]
    dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    have ht := DerivedCategory.quotientCompQhIso_hom_naturality
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I)
    erw [hqB, hqB, Category.comp_id, Category.id_comp] at ht
    exact ht.symm
  refine ⟨π, hπ, ?_⟩
  intro γ hγ
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  let : I.IsKInjective := hI
  have hcomp : γ.app (DerivedCategory.Q.obj I) = π.app (DerivedCategory.Q.obj I) := by
    apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app I)).mp
    exact (hγ I).trans (hπ I).symm
  apply (cancel_mono (G.mapDerivedCategory.map e.hom)).mp
  rw [← γ.naturality, ← π.naturality, hcomp]

/-- Actual total-limit projections, characterized on simultaneous K-injective towers.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site).
Proof: apply the ordinary limit projection to a K-injective tower resolution.
Exact evaluation identifies its localization with the derived evaluation. The
right-derived universal property descends these natural chain maps; every object
has a K-injective representative, so the normalization determines the map uniquely. -/
theorem coefficientConstantTowerProjection_exists (n : ℕ) :
    ∃! π : coefficientConstantTowerLimit l E W ⟶ coefficientConstantTowerEvaluation l E W n,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective],
        π.app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app I =
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).hom ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (lim.π (op n)) (ComplexShape.up ℤ)).app I) := by
  exact derived_projection_exists
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)) (lim.π (op n))

/-- Canonical total-limit projection, not a lift selected after evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientConstantTowerProjection (n : ℕ) :=
  (coefficientConstantTowerProjection_exists l E W n).choose

/-- The actual derived global sections on completed coefficients, with displayed categories.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientIntegralSections :
    DerivedCategory (scalarReductionSource l E W) ⥤
      @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  coefficientGlobalSections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- The actual derived global sections at a positive finite coefficient level.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteSections (n : ℕ) :
    normalizedDVRDerived l E W n ⥤
      @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  coefficientGlobalSections.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)

/-- Integral global derived Hom, retaining the full mapping complex.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientIntegralGlobalHom :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      DerivedCategory (scalarReductionSource l E W) ⥤
        @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
      (completedIntegralCommRingSheafUnrestricted l E W) (HasDerivedCategory.standard _) ⋙
    coefficientIntegralSections l E W

/-- Finite global derived Hom, retaining the full mapping complex.
Source: Stacks 08JA (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteGlobalHom (n : ℕ) :
    (normalizedDVRDerived l E W n)ᵒᵖ × normalizedDVRDerived l E W n ⥤
        @DerivedCategory AddCommGrpCat.{max u (t+1)} _ _ (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (integralCoefficientCommRingSheaf l E W n)))
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
      (integralCoefficientCommRingSheaf l E W n) (HasDerivedCategory.standard _) ⋙
    coefficientFiniteSections l E W n

/-- The integral derived internal-Hom bifunctor used in the calculus.
Source: Stacks 0A95 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientIntegralInternalHom :
    (DerivedCategory (scalarReductionSource l E W))ᵒᵖ ×
      DerivedCategory (scalarReductionSource l E W) ⥤
        DerivedCategory (scalarReductionSource l E W) :=
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
    (completedIntegralCommRingSheafUnrestricted l E W) (HasDerivedCategory.standard _)

/-- The finite derived internal-Hom bifunctor used in the calculus.
Source: Stacks 0A95 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientFiniteInternalHom (n : ℕ) :
    (normalizedDVRDerived l E W n)ᵒᵖ × normalizedDVRDerived l E W n ⥤
      normalizedDVRDerived l E W n :=
  @derivedInternalHomOfUniverses.{t+1, t, u} _ _ (Scheme.ProEt.topology W) _ _
    (integralCoefficientCommRingSheaf l E W n) (HasDerivedCategory.standard _)

/-- The canonical derived identification of restricted evaluation.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientRestrictedEvaluationIso (n : ℕ) :
    coefficientSequenceDerivedRestriction l E W ⋙ coefficientConstantTowerEvaluation l E W n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteDerivedRestriction l E W n :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := (scalarReductionRestriction_exact l E W n).1
  letI := (scalarReductionRestriction_exact l E W n).2
  Functor.mapDerivedCategoryCompIso (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) ≪≫
    (Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E W n)
      (scalarReductionRestriction l E W n)).symm

/-- The actual projection L N to the restricted nth coefficient component.
Source: Stacks 0941 (blueprint: def-coef-ringed-sequence-site). -/
noncomputable def coefficientSequenceProjection (n : ℕ) :
    coefficientSequenceLimit l E W ⟶
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteDerivedRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceDerivedRestriction l E W)
    (coefficientConstantTowerProjection l E W n) ≫
    (coefficientRestrictedEvaluationIso l E W n).hom

end WeilConjectures
