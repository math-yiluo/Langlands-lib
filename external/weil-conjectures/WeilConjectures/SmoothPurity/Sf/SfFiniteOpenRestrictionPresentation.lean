/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralCompactSupportTower
public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # A section-normalized comparison of finite open restriction

Source: Stacks Tags 098K, 03DI and 03DJ.
(blueprint: lem-sf-finite-open-restriction-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Keep the chosen valuation ring abstract during coefficient-category comparisons.
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

/-- The section map from the fixed-scalar presentation to its intrinsic realization.
Both factors are the actual realization unit and counit; no section is chosen.
Source: Stacks 00YV (blueprint: lem-sf-finite-open-restriction-presentation). -/
@[irreducible] def sfFixedToIntrinsicSection (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (N : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEtᵒᵖ)
    (x : ((sfIntrinsicModuleEquivalence T A).inverse.obj N).obj.obj V) : N.val.obj V :=
  (((sfIntrinsicModuleEquivalence T A).counitIso.hom.app N).val.app V)
    (((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.app
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} A)).obj
          ((sfIntrinsicModuleEquivalence T A).inverse.obj N).obj)).app V x)

private def fixedEmbedding (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) ⋙
    ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} A)

private def fixedRestriction (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  SheafOfModules.forget.{u + 1} _ ⋙
    PresheafOfModules.restrictScalars (ProEtale.finiteCoefficientIntrinsicScalarMap T A)

private def fixedUnitIso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    fixedEmbedding T A ≅ (sfIntrinsicModuleEquivalence T A).functor ⋙
      fixedRestriction T A := by
  let η := Functor.whiskerLeft (fixedEmbedding T A)
    (PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change IsIso ((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap T A)).unit.app
        ((fixedEmbedding T A).obj M))
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) AddCommGrpCat.{u + 1})).obj M).property
  exact asIso η

private def fixedSectionIso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicModuleEquivalence T A).inverse ⋙ fixedEmbedding T A ≅
      fixedRestriction T A :=
  isoWhiskerLeft _ (fixedUnitIso T A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence T A).counitIso _ ≪≫
    Functor.leftUnitor _

private theorem fixedSection_apply (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (N : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEtᵒᵖ)
    (x : ((sfIntrinsicModuleEquivalence T A).inverse.obj N).obj.obj V) :
    ((fixedSectionIso T A).hom.app N).app V x = sfFixedToIntrinsicSection T A N V x := by
  rw [sfFixedToIntrinsicSection]
  rfl

private def constantPushforwardIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (A : Type (u + 1)) [CommRing A]
    {S : Sheaf J RingCat.{u + 1}} {R : Sheaf K RingCat.{u + 1}}
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ S.obj)
    (β : (Functor.const Dᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (h : α ≫ φ.hom = Functor.whiskerLeft F.op β) :
    SheafOfModules.pushforward.{u + 1} φ ⋙
        (SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars α) ≅
      (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars β) ⋙
        PresheafOfModules.pushforward₀ F ((Functor.const Dᵒᵖ).obj (RingCat.of A)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let L := (SheafOfModules.pushforward.{u + 1} φ ⋙
        (SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars α)).obj M
    let R' := ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars β) ⋙
      PresheafOfModules.pushforward₀ F ((Functor.const Dᵒᵖ).obj (RingCat.of A))).obj M
    change L ≅ R'
    refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
    · let g : L.obj V ≃ₗ[A] R'.obj V :=
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            exact congrArg (fun b ↦ b • (show M.val.obj (F.op.obj V) from x))
              (congrArg (fun f ↦ (f.app V).hom a) h) }
      exact g.toModuleIso
    · intro V W f
      ext x
      rfl
  · intro M N f
    ext V x
    rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]

/-- Recomposition of an object of the open slice gives its original ambient object.
Source: Stacks 098K (blueprint: lem-sf-finite-open-restriction-presentation). -/
@[irreducible] def sfFiniteOpenSliceObjectIso (V : Over (IntegralOpenReduction.openObject j)) :
    ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
      ((IntegralOpenReduction.sliceSite j).obj V)) ≅ V.left :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change V.left.hom = V.hom.left ≫ j
    exact (MorphismProperty.Over.w V.hom).symm)

variable (o : IntegralOpenReduction.Operations l E j)

private def sliceScalar (n : ℕ) :
    (Functor.const (Over (IntegralOpenReduction.openObject j))ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) ⟶
      ((integralCoefficientSheaf l E Z n).over (IntegralOpenReduction.openObject j)).obj :=
  Functor.whiskerLeft (Over.forget (IntegralOpenReduction.openObject j)).op
    (ProEtale.finiteCoefficientIntrinsicScalarMap Z (Padic.coefficientExtensionRing l E (n + 1)))

private instance sliceScalarInjective (n : ℕ) :
    Presheaf.IsLocallyInjective ((ProEt.topology Z).over (IntegralOpenReduction.openObject j))
      (sliceScalar l E j n) :=
  Presheaf.isLocallyInjective_whisker
    ((ProEt.topology Z).over (IntegralOpenReduction.openObject j)) (ProEt.topology Z)
    (Over.forget (IntegralOpenReduction.openObject j))
    (ProEtale.finiteCoefficientIntrinsicScalarMap Z (Padic.coefficientExtensionRing l E (n + 1)))

private instance sliceScalarSurjective (n : ℕ) :
    Presheaf.IsLocallySurjective ((ProEt.topology Z).over (IntegralOpenReduction.openObject j))
      (sliceScalar l E j n) :=
  Presheaf.isLocallySurjective_whisker
    ((ProEt.topology Z).over (IntegralOpenReduction.openObject j)) (ProEt.topology Z)
    (Over.forget (IntegralOpenReduction.openObject j))
    (ProEtale.finiteCoefficientIntrinsicScalarMap Z (Padic.coefficientExtensionRing l E (n + 1)))

private def sliceFixedRestriction (n : ℕ) :=
  SheafOfModules.forget.{u + 1}
      ((integralCoefficientSheaf l E Z n).over (IntegralOpenReduction.openObject j)) ⋙
    PresheafOfModules.restrictScalars (sliceScalar l E j n)

private def finiteConstantPushforward (n : ℕ) :
    (o.finite n).functor ⋙ sliceFixedRestriction l E j n ≅
      fixedRestriction X (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        PresheafOfModules.pushforward₀ (IntegralOpenReduction.sliceSite j)
          ((Functor.const X.ProEtᵒᵖ).obj
            (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) := by
  refine isoWhiskerRight (eqToIso (o.finiteFunctor n)) _ ≪≫ ?_
  apply constantPushforwardIso
  apply NatTrans.ext
  funext V
  exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map f)
    (o.finiteConstants n V.unop)

private def sliceRecomposition (A : Type u) [CommRing A] [Finite A] :
    ((sfIntrinsicModuleEquivalence Z A).inverse ⋙ fixedEmbedding Z A) ⋙
        PresheafOfModules.pushforward₀ (Over.forget (IntegralOpenReduction.openObject j))
          ((Functor.const Z.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      ((sfIntrinsicModuleEquivalence Z A).inverse ⋙
        ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j ⋙
          fixedEmbedding X A) ⋙
        PresheafOfModules.pushforward₀ (IntegralOpenReduction.sliceSite j)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · refine PresheafOfModules.isoMk (fun V ↦
      ((sfIntrinsicModuleEquivalence Z A).inverse.obj N).obj.mapIso
        (sfFiniteOpenSliceObjectIso j V.unop).op) ?_
    intro V W f
    ext x
    change (((sfIntrinsicModuleEquivalence Z A).inverse.obj N).obj.map f.unop.left.op ≫
      ((sfIntrinsicModuleEquivalence Z A).inverse.obj N).obj.map
        (sfFiniteOpenSliceObjectIso j W.unop).hom.op) x = _
    rw [← Functor.map_comp]
    change (((sfIntrinsicModuleEquivalence Z A).inverse.obj N).obj.map _) x =
      ((((sfIntrinsicModuleEquivalence Z A).inverse.obj N).obj.map
        (sfFiniteOpenSliceObjectIso j V.unop).hom.op) ≫
        ((sfIntrinsicModuleEquivalence Z A).inverse.obj N).obj.map _) x
    rw [← Functor.map_comp]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    simp only [sfFiniteOpenSliceObjectIso]
    change (𝟙 _ ≫ f.unop.left.left) = (f.unop.left.left ≫ 𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
  · intro M N f
    ext V x
    exact ConcreteCategory.congr_hom
      (((sfIntrinsicModuleEquivalence Z A).inverse.map f).hom.naturality
        (sfFiniteOpenSliceObjectIso j V.unop).hom.op) x |>.symm

private def sliceComparisonBeforeTransport (n : ℕ) :
    SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
        (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j) ⋙
          sliceFixedRestriction l E j n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        fixedRestriction X (Padic.coefficientExtensionRing l E (n + 1)) ⋙
          PresheafOfModules.pushforward₀ (IntegralOpenReduction.sliceSite j)
            ((Functor.const X.ProEtᵒᵖ).obj
              (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let P := PresheafOfModules.pushforward₀ (Over.forget (IntegralOpenReduction.openObject j))
    ((Functor.const Z.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)))
  let Q := PresheafOfModules.pushforward₀ (IntegralOpenReduction.sliceSite j)
    ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)))
  let I := (sfIntrinsicModuleEquivalence Z A).inverse
  let J := ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  let R := sfIntrinsicOpenRestriction j A
  let H := sliceFixedRestriction l E j n
  let h₀ : SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j) ⋙ H ≅
        fixedRestriction Z A ⋙ P := Iso.refl _
  let h₁ := isoWhiskerRight (fixedSectionIso Z A).symm P
  let h₂ := sliceRecomposition j A
  let h₃ : ((I ⋙ J ⋙ fixedEmbedding X A) ⋙ Q) ≅ (R ⋙ fixedRestriction X A) ⋙ Q :=
    isoWhiskerRight (isoWhiskerLeft I (isoWhiskerLeft J (fixedUnitIso X A))) Q
  exact h₀ ≪≫ h₁ ≪≫ h₂ ≪≫ h₃ ≪≫ Functor.associator _ _ _

private def sliceComparisonConstants (n : ℕ) :
    SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
        (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j) ⋙
          sliceFixedRestriction l E j n ≅
      (sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        (o.finite n).functor) ⋙ sliceFixedRestriction l E j n :=
  sliceComparisonBeforeTransport l E j n ≪≫
    isoWhiskerLeft _ (finiteConstantPushforward l E j o n).symm ≪≫
      (Functor.associator _ _ _).symm

private instance sliceFixedRestrictionFull (n : ℕ) :
    (sliceFixedRestriction l E j n).Full := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    ((ProEt.topology Z).over (IntegralOpenReduction.openObject j))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    ((ProEt.topology Z).over (IntegralOpenReduction.openObject j))
  exact (PresheafOfModules.sheafificationAdjunction
    (sliceScalar l E j n)).fullyFaithfulROfIsIsoCounit.full

private instance sliceFixedRestrictionFaithful (n : ℕ) :
    (sliceFixedRestriction l E j n).Faithful := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    ((ProEt.topology Z).over (IntegralOpenReduction.openObject j))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    ((ProEt.topology Z).over (IntegralOpenReduction.openObject j))
  exact (PresheafOfModules.sheafificationAdjunction
    (sliceScalar l E j n)).fullyFaithfulROfIsIsoCounit.faithful

private def sliceComparison (n : ℕ) :
    SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
        (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j) ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        (o.finite n).functor := by
  let := sliceFixedRestrictionFull l E j n
  let := sliceFixedRestrictionFaithful l E j n
  exact Functor.fullyFaithfulCancelRight (sliceFixedRestriction l E j n)
    (sliceComparisonConstants l E j o n)

private def restrictionComparison (n : ℕ) :
    IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)) :=
  Functor.fullyFaithfulCancelRight (o.finite n).functor
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (o.finite n).counitIso ≪≫
      Functor.rightUnitor _ ≪≫ sliceComparison l E j o n)

private theorem fixedSection_bijective (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (N : proEtaleRingModules T (proEtaleConstantRing T A)) (V : T.ProEtᵒᵖ) :
    Function.Bijective (sfFixedToIntrinsicSection T A N V) := by
  unfold sfFixedToIntrinsicSection
  change Function.Bijective (((fixedSectionIso T A).hom.app N).app V)
  exact ConcreteCategory.bijective_of_isIso
    ((PresheafOfModules.evaluation _ V).map ((fixedSectionIso T A).hom.app N))

private theorem sliceComparison_forward (n : ℕ) (N : normalizedDVRModules l E Z n) :
    (sliceFixedRestriction l E j n).map ((sliceComparison l E j o n).hom.app N) ≫
      (finiteConstantPushforward l E j o n).hom.app
        ((sfIntrinsicOpenRestriction j
          (Padic.coefficientExtensionRing l E (n + 1))).obj N) =
      (sliceComparisonBeforeTransport l E j n).hom.app N := by
  let := sliceFixedRestrictionFull l E j n
  let := sliceFixedRestrictionFaithful l E j n
  change (sliceFixedRestriction l E j n).map
    ((sliceFixedRestriction l E j n).preimage _) ≫ _ = _
  rw [Functor.map_preimage]
  simp [sliceComparisonConstants]

private theorem restrictionComparison_forward (n : ℕ) (N : normalizedDVRModules l E Z n) :
    (o.finite n).functor.map ((restrictionComparison l E j o n).hom.app N) =
      (o.finite n).counitIso.hom.app
        ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
          (IntegralOpenReduction.rings l E Z n)
          (IntegralOpenReduction.openObject j)).obj N) ≫
        (sliceComparison l E j o n).hom.app N := by
  change (o.finite n).functor.map ((o.finite n).functor.preimage _) = _
  rw [Functor.map_preimage]
  simp

/-- The finite open adjunction, with the recorded direct-sum unit.
Source: Stacks 03DI (blueprint: lem-sf-finite-open-restriction-presentation). -/
@[irreducible] def sfFiniteOpenAdjunction (n : ℕ) :
    IntegralOpenReduction.finiteExtension l E j o n ⊣
      IntegralOpenReduction.finiteRestriction l E j o n :=
  (o.finite n).toAdjunction.comp
    (SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1}
      (IntegralOpenReduction.rings l E Z n) (IntegralOpenReduction.openObject j))

/-- A right-adjoint comparison preserves the concrete underlying sections. To state
this without arbitrary inverses on sections, test on the fixed-scalar realization:
its unit and counit supply every section. Transport out of the chosen slice inverse
uses its actual counit, and `finiteFunctor` identifies its forward transport.
Source: Stacks 098K, 00YV (blueprint: lem-sf-finite-open-restriction-presentation). -/
@[irreducible] def SfFiniteOpenRestrictionNormalized (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1))) : Prop :=
  ∀ (N : normalizedDVRModules l E Z n)
    (V : Over (IntegralOpenReduction.openObject j))
    (x : ((sfIntrinsicModuleEquivalence Z
      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj N).obj.obj
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
          ((IntegralOpenReduction.sliceSite j).obj V)))),
    (((o.finite n).functor.map (r.hom.app N) ≫
      (eqToHom (o.finiteFunctor n)).app
        ((sfIntrinsicOpenRestriction j
          (Padic.coefficientExtensionRing l E (n + 1))).obj N)).val.app (op V))
      ((((o.finite n).counitIso.inv.app
        ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
          (IntegralOpenReduction.rings l E Z n)
          (IntegralOpenReduction.openObject j)).obj N)).val.app (op V))
        (N.val.map (sfFiniteOpenSliceObjectIso j V).inv.op
          (sfFixedToIntrinsicSection Z (Padic.coefficientExtensionRing l E (n + 1)) N
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
              ((IntegralOpenReduction.sliceSite j).obj V))) x))) =
    (((PresheafOfModules.sheafificationAdjunction
      (ProEtale.finiteCoefficientIntrinsicScalarMap X
        (Padic.coefficientExtensionRing l E (n + 1)))).unit.app
          ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).obj
              ((ProEtale.openImmersionRestriction
                (ModuleCat.{u + 1} (ULift.{u + 1}
                  (Padic.coefficientExtensionRing l E (n + 1)))) j).obj
                    ((sfIntrinsicModuleEquivalence Z
                      (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj N)).obj)).app
                        (op ((IntegralOpenReduction.sliceSite j).obj V)) x)

/-- At one coefficient, the slice and intrinsic right restrictions have a unique
section-preserving comparison. This asserts neither extension comparisons nor a
coefficient square.
Source: Stacks 098K, 00YV, 03DI and 03DJ
(blueprint: lem-sf-finite-open-restriction-presentation).

Proof: the slice-to-open equivalence identifies both restrictions with evaluation
on the same underlying scheme. On fixed-scalar sheaves its comparison is the identity
on sections, followed by the realization unit. The constant-presheaf unit equation
`o.finiteConstants` makes this map linear for the restricted coefficient sheaf:
action by a locally constant scalar is determined locally by its action on constants.
The equation `o.finiteFunctor` identifies the forward module transport. Its counit
then transports this comparison back through the slice equivalence, giving r.
The realization unit on a fixed-scalar sheaf is invertible on underlying abelian
sheaves, as is the realization counit, so the component maps are invertible.
Naturality follows from the naturality of the two units and the slice counit.
For uniqueness, forward transport is faithful, and the realization section maps
are bijective; the displayed equation therefore determines each component on every
section. This includes the empty open and requires no quasi-compactness. -/
theorem sfFiniteOpenRestriction_presentation (n : ℕ) :
    ∃! r : IntegralOpenReduction.finiteRestriction l E j o n ≅
        sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1)),
      SfFiniteOpenRestrictionNormalized l E j o n r := by
  have hnorm : SfFiniteOpenRestrictionNormalized l E j o n
      (restrictionComparison l E j o n) := by
    rw [SfFiniteOpenRestrictionNormalized]
    intro N V x
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let M := (sfIntrinsicModuleEquivalence Z A).inverse.obj N
    let W := op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
      ((IntegralOpenReduction.sliceSite j).obj V))
    let y := N.val.map (sfFiniteOpenSliceObjectIso j V).inv.op
      (sfFixedToIntrinsicSection Z A N W x)
    change ((
      (o.finite n).counitIso.inv.app
        ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
          (IntegralOpenReduction.rings l E Z n)
          (IntegralOpenReduction.openObject j)).obj N) ≫
      (o.finite n).functor.map ((restrictionComparison l E j o n).hom.app N) ≫
      (eqToHom (o.finiteFunctor n)).app
        ((sfIntrinsicOpenRestriction j A).obj N)).val.app (op V)) y = _
    rw [restrictionComparison_forward]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    have hq := congrArg (fun f ↦ f.app (op V) y)
      (sliceComparison_forward l E j o n N)
    change (((sliceComparison l E j o n).hom.app N ≫
      (eqToHom (o.finiteFunctor n)).app
        ((sfIntrinsicOpenRestriction j A).obj N)).val.app (op V)) y =
      ((sliceComparisonBeforeTransport l E j n).hom.app N).app (op V) y at hq
    refine hq.trans ?_
    let uX := ((fixedUnitIso X A).hom.app
      ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).obj M)).app
        (op ((IntegralOpenReduction.sliceSite j).obj V))
    change uX (M.obj.map (sfFiniteOpenSliceObjectIso j V).hom.op
      (((fixedSectionIso Z A).inv.app N).app (op V.left) y)) = uX x
    have hi : ((fixedSectionIso Z A).inv.app N).app W
        (sfFixedToIntrinsicSection Z A N W x) = x := by
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun f ↦ f.app W) ((fixedSectionIso Z A).hom_inv_id_app N)) x
      change ((fixedSectionIso Z A).inv.app N).app W
        (((fixedSectionIso Z A).hom.app N).app W x) = x at hh
      rw [fixedSection_apply] at hh
      exact hh
    have hn := ConcreteCategory.congr_hom
      (((fixedSectionIso Z A).inv.app N).naturality
        (sfFiniteOpenSliceObjectIso j V).inv.op)
      (sfFixedToIntrinsicSection Z A N W x)
    change ((fixedSectionIso Z A).inv.app N).app (op V.left) y =
      M.obj.map (sfFiniteOpenSliceObjectIso j V).inv.op
        (((fixedSectionIso Z A).inv.app N).app W
          (sfFixedToIntrinsicSection Z A N W x)) at hn
    have hs := hn.trans (congrArg
      (fun z ↦ M.obj.map (sfFiniteOpenSliceObjectIso j V).inv.op z) hi)
    refine (congrArg
      (fun z ↦ uX (M.obj.map (sfFiniteOpenSliceObjectIso j V).hom.op z)) hs).trans ?_
    exact congrArg uX (ConcreteCategory.congr_hom
      (M.obj.mapIso (sfFiniteOpenSliceObjectIso j V).op).inv_hom_id x)
  refine ⟨restrictionComparison l E j o n, hnorm, ?_⟩
  intro r hr
  rw [SfFiniteOpenRestrictionNormalized] at hr hnorm
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (o.finite n).functor.map_injective
  apply (cancel_mono ((eqToIso (o.finiteFunctor n)).hom.app
    ((sfIntrinsicOpenRestriction j
      (Padic.coefficientExtensionRing l E (n + 1))).obj N))).mp
  apply (cancel_epi ((o.finite n).counitIso.inv.app
    ((SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1}
      (IntegralOpenReduction.rings l E Z n)
      (IntegralOpenReduction.openObject j)).obj N))).mp
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext y
  have hs : Function.Surjective (fun x ↦
      N.val.map (sfFiniteOpenSliceObjectIso j V.unop).inv.op
        (sfFixedToIntrinsicSection Z (Padic.coefficientExtensionRing l E (n + 1)) N
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
            ((IntegralOpenReduction.sliceSite j).obj V.unop))) x)) :=
    (ConcreteCategory.bijective_of_isIso
      (N.val.presheaf.map (sfFiniteOpenSliceObjectIso j V.unop).inv.op)).surjective.comp
        (fixedSection_bijective Z (Padic.coefficientExtensionRing l E (n + 1)) N _).surjective
  obtain ⟨x, rfl⟩ := hs y
  exact (hr N V.unop x).trans (hnorm N V.unop x).symm

/-- The left comparison is constructed by adjunction uniqueness from a supplied
right comparison. No choice of a left comparison or unproved datum occurs here.
Source: Stacks 03DI (blueprint: lem-sf-finite-open-restriction-presentation). -/
@[irreducible] def sfFiniteOpenLeftComparison (n : ℕ)
    (r : IntegralOpenReduction.finiteRestriction l E j o n ≅
      sfIntrinsicOpenRestriction j (Padic.coefficientExtensionRing l E (n + 1))) :
    IntegralOpenReduction.finiteExtension l E j o n ≅
      sfIntrinsicExtensionByZero j (Padic.coefficientExtensionRing l E (n + 1)) :=
  ((sfFiniteOpenAdjunction l E j o n).ofNatIsoRight r).leftAdjointUniq
    (sfIntrinsicExtensionByZeroAdjunction j (Padic.coefficientExtensionRing l E (n + 1)))

end WeilConjectures
