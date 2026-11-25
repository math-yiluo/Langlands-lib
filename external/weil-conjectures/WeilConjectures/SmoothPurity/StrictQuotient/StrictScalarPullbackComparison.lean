/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
import all WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorCoherence
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Scalar extension commutes with finite coefficient pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  WeilConjectures.coefficientFiniteQuotientExistence
  WeilConjectures.coefficientFiniteQuotientExtension
  WeilConjectures.coefficientFiniteQuotientUnitSection
  WeilConjectures.normalizedDVRQuotient
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem quotient_horizontal (W : Scheme.{t}) {m n : ℕ} (hmn : n ≤ m)
    (U : W.ProEtᵒᵖ) :
    (forget₂ CommRingCat RingCat).map
        ((coefficientSequenceCommRingPresheaf l E W).map
          (Prod.mkHom (homOfLE hmn) (𝟙 U.unop)).op) =
      (normalizedDVRQuotient l E W hmn).hom.app U := by
  have h := congrArg (fun f ↦ f.hom.app U)
    (coefficientSequenceRingHorizontal l E W hmn)
  have hm : (eqToHom (coefficientSequenceEvaluationRing_eq l E W m).symm).hom.app U =
      𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  have hn : (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U =
      𝟙 _ := by
    rw [ObjectProperty.eqToHom_hom, eqToHom_app]
    rfl
  change _ ≫ _ = _ ≫ _ at h
  rw [hm, hn, Category.id_comp, Category.comp_id] at h
  exact h

private theorem ringSquare {V W : Scheme.{t}} (g : V ⟶ W)
    {m n : ℕ} (hmn : n ≤ m) :
    normalizedDVRQuotient l E W hmn ≫ AmbientPullbackTensor.moduleRingUnit l E g (some n) =
      AmbientPullbackTensor.moduleRingUnit l E g (some m) ≫
        ((Scheme.proEtaleBaseChange g).sheafPushforwardContinuous RingCat
          (Scheme.ProEt.topology W) (Scheme.ProEt.topology V)).map
            (normalizedDVRQuotient l E V hmn) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have h := congrArg ((forget₂ CommRingCat RingCat).map)
    (integralComparisonSequenceRing_naturality l E g
      (Prod.mkHom (homOfLE hmn) (𝟙 U.unop)).op)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  rw [quotient_horizontal] at h
  change _ = _ ≫ (forget₂ CommRingCat RingCat).map
    ((coefficientSequenceCommRingPresheaf l E V).map
      (Prod.mkHom (homOfLE hmn) ((Scheme.proEtaleBaseChange g).map (𝟙 U.unop))).op) at h
  rw [CategoryTheory.Functor.map_id, quotient_horizontal] at h
  exact h

private def push_restrict_iso.{r, c, v, d, w}
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {J : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J JD]
    {A B : Sheaf J RingCat.{r}} {A' B' : Sheaf JD RingCat.{r}}
    (φA : A ⟶ (F.sheafPushforwardContinuous RingCat J JD).obj A')
    (φB : B ⟶ (F.sheafPushforwardContinuous RingCat J JD).obj B')
    (q : A ⟶ B) (q' : A' ⟶ B')
    (hc : q ≫ φB = φA ≫ (F.sheafPushforwardContinuous RingCat J JD).map q') :
    SheafOfModules.restrictScalars.{r} q' ⋙ SheafOfModules.pushforward φA ≅
      SheafOfModules.pushforward φB ⋙ SheafOfModules.restrictScalars.{r} q :=
  SheafOfModules.pushforwardComp (F := F) (G := 𝟭 D)
      (J := J) (K := JD) (K' := JD) (R' := B') φA q' ≪≫
    SheafOfModules.pushforwardCongr hc.symm ≪≫
      (SheafOfModules.pushforwardComp (F := 𝟭 C) (G := F)
        (J := J) (K := J) (K' := JD) (R' := B') q φB).symm

private theorem scalar_comparison_unit.{r, c, v, d, w}
    {C : Type c} [Category.{v} C] {D : Type d} [Category.{w} D]
    {J : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J JD]
    {A B : Sheaf J RingCat.{r}} {A' B' : Sheaf JD RingCat.{r}}
    (φA : A ⟶ (F.sheafPushforwardContinuous RingCat J JD).obj A')
    (φB : B ⟶ (F.sheafPushforwardContinuous RingCat J JD).obj B')
    (q : A ⟶ B) (q' : A' ⟶ B')
    (hc : q ≫ φB = φA ≫ (F.sheafPushforwardContinuous RingCat J JD).map q')
    (Lm : SheafOfModules.{r} A ⥤ SheafOfModules.{r} A')
    (Ln : SheafOfModules.{r} B ⥤ SheafOfModules.{r} B')
    (EW : SheafOfModules.{r} A ⥤ SheafOfModules.{r} B)
    (EV : SheafOfModules.{r} A' ⥤ SheafOfModules.{r} B')
    (am : Lm ⊣ SheafOfModules.pushforward φA)
    (an : Ln ⊣ SheafOfModules.pushforward φB)
    (aW : EW ⊣ SheafOfModules.restrictScalars q)
    (aV : EV ⊣ SheafOfModules.restrictScalars q')
    (jW : ∀ (M : SheafOfModules.{r} A) (U : Cᵒᵖ), M.val.obj U → (EW.obj M).val.obj U)
    (jV : ∀ (M : SheafOfModules.{r} A') (U : Dᵒᵖ), M.val.obj U → (EV.obj M).val.obj U)
    (hW : ∀ M U x, coefficientRestrictionSection q (EW.obj M) U
      ((aW.unit.app M).val.app U x) = jW M U x)
    (hV : ∀ M U x, coefficientRestrictionSection q' (EV.obj M) U
      ((aV.unit.app M).val.app U x) = jV M U x)
    (M : SheafOfModules.{r} A) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((((am.comp aV).leftAdjointUniq ((aW.comp an).ofNatIsoRight
      (push_restrict_iso F φA φB q q' hc).symm)).hom.app M).val.app (F.op.obj U))
      (jV (Lm.obj M) (F.op.obj U) ((am.unit.app M).val.app U x)) =
    (an.unit.app (EW.obj M)).val.app U (jW M U x) := by
  have h := congrArg (fun f ↦ f.val.app U x)
    (Adjunction.unit_leftAdjointUniq_hom_app (am.comp aV)
      ((aW.comp an).ofNatIsoRight (push_restrict_iso F φA φB q q' hc).symm) M)
  change ((((am.comp aV).leftAdjointUniq ((aW.comp an).ofNatIsoRight
      (push_restrict_iso F φA φB q q' hc).symm)).hom.app M).val.app (F.op.obj U))
      (coefficientRestrictionSection q' _ (F.op.obj U)
        ((aV.unit.app (Lm.obj M)).val.app (F.op.obj U) ((am.unit.app M).val.app U x))) =
    (an.unit.app (EW.obj M)).val.app U
      (coefficientRestrictionSection q _ U ((aW.unit.app M).val.app U x)) at h
  erw [hW, hV] at h
  exact h

private def pushRestriction {V W : Scheme.{t}} (g : V ⟶ W)
    {m n : ℕ} (hmn : n ≤ m) :
    normalizedDVRModuleRes l E V hmn ⋙ AmbientPullbackTensor.push l E g (some m) ≅
      AmbientPullbackTensor.push l E g (some n) ⋙ normalizedDVRModuleRes l E W hmn := by
  let : (Scheme.proEtaleBaseChange g).IsContinuous
      (AmbientPullbackTensor.topology W (some m))
      (AmbientPullbackTensor.topology V (some m)) :=
    AmbientPullbackTensor.baseContinuous g (some m)
  exact push_restrict_iso.{max u (t + 1), t + 1, t, t + 1, t} (Scheme.proEtaleBaseChange g)
    (AmbientPullbackTensor.moduleRingUnit l E g (some m))
    (AmbientPullbackTensor.moduleRingUnit l E g (some n))
    (normalizedDVRQuotient l E W hmn) (normalizedDVRQuotient l E V hmn)
    (ringSquare l E g hmn)

private theorem sheaf_hom_congr.{r, c, v}
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {M N : SheafOfModules.{r} R} {a b : M ⟶ N} (h : a = b)
    (U : Cᵒᵖ) (x : M.val.obj U) : a.val.app U x = b.val.app U x :=
  congrArg (fun f ↦ f.val.app U x) h

private def finiteAdjunction {V W : Scheme.{t}} (g : V ⟶ W) (n : ℕ) :
    integralOperationsLevelPullback l E g n ⊣
      Scheme.coefficientProEtaleModuleDirectImage.{t, u} g
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  Scheme.coefficientProEtaleModuleAdjunction.{t, u} g _

private def scalarPullbackComparison {V W : Scheme.{t}} (g : V ⟶ W)
    (SW : CoefficientDerivedSystemTensors l E W)
    (DW : CoefficientFiniteQuotientCalculus l E W SW)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m) :
    integralOperationsLevelPullback l E g m ⋙ coefficientFiniteQuotientExtension l E V hmn ≅
      coefficientFiniteQuotientExtension l E W hmn ⋙ integralOperationsLevelPullback l E g n :=
  ((finiteAdjunction l E g m).comp (DV.ordinaryAdjunction hmn)).leftAdjointUniq
    (((DW.ordinaryAdjunction hmn).comp (finiteAdjunction l E g n)).ofNatIsoRight
      (pushRestriction l E g hmn).symm)

private theorem scalarPullbackComparison_generator {V W : Scheme.{t}} (g : V ⟶ W)
    (SW : CoefficientDerivedSystemTensors l E W)
    (DW : CoefficientFiniteQuotientCalculus l E W SW)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m)
    (M : normalizedDVRModules l E W m) (U : W.ProEt) (x : M.val.obj (op U)) :
    ((scalarPullbackComparison l E g SW DW SV DV hmn).hom.app M).val.app
        (op ((Scheme.proEtaleBaseChange g).obj U))
        (coefficientFiniteQuotientUnitSection l E V hmn
          ((integralOperationsLevelPullback l E g m).obj M)
          (op ((Scheme.proEtaleBaseChange g).obj U))
          (integralOperationsPullbackGenerator l E g m M U x)) =
      integralOperationsPullbackGenerator l E g n
        ((coefficientFiniteQuotientExtension l E W hmn).obj M) U
        (coefficientFiniteQuotientUnitSection l E W hmn M (op U) x) := by
  let : (Scheme.proEtaleBaseChange g).IsContinuous
      (AmbientPullbackTensor.topology W (some m))
      (AmbientPullbackTensor.topology V (some m)) :=
    AmbientPullbackTensor.baseContinuous g (some m)
  exact scalar_comparison_unit (Scheme.proEtaleBaseChange g)
    (AmbientPullbackTensor.moduleRingUnit l E g (some m))
    (AmbientPullbackTensor.moduleRingUnit l E g (some n))
    (normalizedDVRQuotient l E W hmn) (normalizedDVRQuotient l E V hmn)
    (ringSquare l E g hmn)
    (integralOperationsLevelPullback l E g m) (integralOperationsLevelPullback l E g n)
    (coefficientFiniteQuotientExtension l E W hmn)
    (coefficientFiniteQuotientExtension l E V hmn)
    (finiteAdjunction l E g m) (finiteAdjunction l E g n)
    (DW.ordinaryAdjunction hmn) (DV.ordinaryAdjunction hmn)
    (coefficientFiniteQuotientUnitSection l E W hmn)
    (coefficientFiniteQuotientUnitSection l E V hmn)
    (DW.ordinary_unit hmn) (DV.ordinary_unit hmn) M (op U) x

attribute [local irreducible] scalarPullbackComparison

private def scalarPullbackComplexComparison {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (SW : CoefficientDerivedSystemTensors l E W)
    (DW : CoefficientFiniteQuotientCalculus l E W SW)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m) :
    ((coefficientFiniteQuotientExtension l E V hmn).mapHomologicalComplex (.up ℤ)).obj
        ((finitePull l E g m).obj (level l E K m)) ≅
      (finitePull l E g n).obj
        (((coefficientFiniteQuotientExtension l E W hmn).mapHomologicalComplex (.up ℤ)).obj
          (level l E K m)) := by
  let : (integralOperationsLevelPullback l E g m).Additive :=
    integralOperationsLevelPullback_additive l E g m
  let : (integralOperationsLevelPullback l E g n).Additive :=
    integralOperationsLevelPullback_additive l E g n
  let : (coefficientFiniteQuotientExtension l E V hmn).Additive :=
    coefficientFiniteQuotientExtensionAdditive l E V hmn
  let : (coefficientFiniteQuotientExtension l E W hmn).Additive :=
    coefficientFiniteQuotientExtensionAdditive l E W hmn
  let : (integralOperationsLevelPullback l E g m ⋙
      coefficientFiniteQuotientExtension l E V hmn).Additive := inferInstance
  let : (coefficientFiniteQuotientExtension l E W hmn ⋙
      integralOperationsLevelPullback l E g n).Additive := inferInstance
  exact (NatIso.mapHomologicalComplex
    (scalarPullbackComparison l E g SW DW SV DV hmn) (.up ℤ)).app (level l E K m)

private theorem scalarPullbackIdentification {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (SW : CoefficientDerivedSystemTensors l E W)
    (DW : CoefficientFiniteQuotientCalculus l E W SW)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m) :
    ScalarPullbackIdentification l E g K hmn
      (scalarPullbackComplexComparison l E g K SW DW SV DV hmn) := by
  intro k U x
  exact scalarPullbackComparison_generator l E g SW DW SV DV hmn ((level l E K m).X k) U x

private theorem normalized_unit_map.{r, c, v}
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S)
    (a : F ⊣ SheafOfModules.restrictScalars φ)
    (j : ∀ (M : SheafOfModules.{r} R) (U : Cᵒᵖ), M.val.obj U → (F.obj M).val.obj U)
    (hj : ∀ M U x, coefficientRestrictionSection φ (F.obj M) U
      ((a.unit.app M).val.app U x) = j M U x)
    {M N : SheafOfModules.{r} R} (f : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (F.map f).val.app U (j M U x) = j N U (f.val.app U x) := by
  have h := congrArg (fun f ↦ f.val.app U x) (a.unit.naturality f)
  change coefficientRestrictionSection φ (F.obj N) U
      ((a.unit.app N).val.app U (f.val.app U x)) =
    (F.map f).val.app U (coefficientRestrictionSection φ (F.obj M) U
      ((a.unit.app M).val.app U x)) at h
  erw [hj, hj] at h
  exact h.symm

private theorem normalized_homEquiv_apply.{r, c, v}
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (F : SheafOfModules.{r} R ⥤ SheafOfModules.{r} S)
    (a : F ⊣ SheafOfModules.restrictScalars φ)
    (j : ∀ (M : SheafOfModules.{r} R) (U : Cᵒᵖ), M.val.obj U → (F.obj M).val.obj U)
    (hj : ∀ M U x, coefficientRestrictionSection φ (F.obj M) U
      ((a.unit.app M).val.app U x) = j M U x)
    {M : SheafOfModules.{r} R} {N : SheafOfModules.{r} S} (f : F.obj M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    coefficientRestrictionSection φ N U (((a.homEquiv M N) f).val.app U x) =
      f.val.app U (j M U x) := by
  rw [a.homEquiv_unit]
  change f.val.app U (coefficientRestrictionSection φ _ U
    ((a.unit.app M).val.app U x)) = _
  erw [hj]

private theorem scalar_restriction_section_injective.{r, c, v}
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (φ : R ⟶ S)
    (M : SheafOfModules.{r} S) (U : Cᵒᵖ) :
    Function.Injective (coefficientRestrictionSection φ M U) := fun _ _ h ↦ h

private theorem scalar_map_unit (W : Scheme.{t})
    (S : CoefficientDerivedSystemTensors l E W)
    (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
    {M N : normalizedDVRModules l E W m} (f : M ⟶ N) (U : W.ProEtᵒᵖ)
    (x : M.val.obj U) :
    ((coefficientFiniteQuotientExtension l E W hmn).map f).val.app U
        (coefficientFiniteQuotientUnitSection l E W hmn M U x) =
      coefficientFiniteQuotientUnitSection l E W hmn N U (f.val.app U x) :=
  normalized_unit_map (normalizedDVRQuotient l E W hmn)
    (coefficientFiniteQuotientExtension l E W hmn) (D.ordinaryAdjunction hmn)
    (coefficientFiniteQuotientUnitSection l E W hmn) (D.ordinary_unit hmn) f U x

/-- Scalar extension and the actual finite inverse image commute, with their
comparison fixed on the scalar and inverse-image unit generators.
Source: Stacks Project, sites-modules.tex, Tag 03EL.
(blueprint: lem-pur-strict-scalar-pullback-comparison).

Proof: naturality of the sequence coefficient ring map gives the square of the
actual quotient ring maps. Composition of module direct images around this square
identifies restriction followed by direct image with direct image followed by
restriction. Uniqueness of left adjoints supplies the comparison. Its unit identity
sends scalar insertion after the mth inverse-image unit to the nth inverse-image
unit after scalar insertion. Mapping to complexes preserves that formula in each
degree. This uses no flatness assumption on the input complex or quotient ring. -/
theorem strictScalarPullbackComparison {V W : Scheme.{t}} (g : V ⟶ W)
    (K : Complex l E W) (SW : CoefficientDerivedSystemTensors l E W)
    (DW : CoefficientFiniteQuotientCalculus l E W SW)
    (SV : CoefficientDerivedSystemTensors l E V)
    (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m) :
    ∃ χ, ScalarPullbackIdentification l E g K hmn χ := by
  exact ⟨scalarPullbackComplexComparison l E g K SW DW SV DV hmn,
    scalarPullbackIdentification l E g K SW DW SV DV hmn⟩

end WeilConjectures.StrictQuotient
