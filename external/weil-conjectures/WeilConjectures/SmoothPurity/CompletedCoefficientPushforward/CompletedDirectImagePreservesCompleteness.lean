/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardModels
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientStructureMap
import all WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products

/-! # Derived direct image preserves completed-coefficient completeness

Source: Stacks proetale.tex Tag 099N (1),(3), and algebraization.tex Tags 0A0E and 099B.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a av b bv
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem complete_iff_local
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) (K : IntegralOnSlice.D l E T none) :
    IsDerivedCompleteUnrestricted l E T K ↔
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K := by
  classical
  let : HasExactLimitsOfShape (Discrete ℕ) (IntegralOnSlice.Mod l E T none) :=
    IntegralOnSlice.sliceProductsExact l E T none
  let : HasFiniteBiproducts (IntegralOnSlice.Mod l E T none) :=
    Abelian.hasFiniteBiproducts
  let : CountableAB4Star (IntegralOnSlice.Mod l E T none) :=
    CountableAB4Star.of_hasExactLimitsOfShape_nat (IntegralOnSlice.Mod l E T none)
  let : HasCountableProducts (IntegralOnSlice.D l E T none) :=
    derivedCategory_hasCountableProducts (IntegralOnSlice.Mod l E T none)
  constructor
  · rintro ⟨D, hl, P₀, G, q, hq, e₀, hprod, δ, hδ⟩
    let := hprod
    let C : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none :=
      Functor.ofOpSequence (X := fun n ↦ integralTowerComplex l E T D hl n P₀)
        (fun n ↦ integralTowerTransition l E T D hl P₀ n)
    obtain ⟨ε, hε⟩ := integralStrictRoosTriangle (A := IntegralOnSlice.Mod l E T none) C
    simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ] at hδ
    have hε' := hε
    simp only [integralOperationsTowerStep, C,
      Functor.ofOpSequence_map_homOfLE_succ] at hε'
    set_option backward.isDefEq.respectTransparency true in
    obtain ⟨i⟩ := integralRoosIso _ _ _ δ ε hδ hε'
    have hc₀ := integralQuotientLocallyComplete l E T P₀ hq.2
    have hC : (IntegralOnSlice.tower l E T none).obj P₀ = C := by
      rw [integralGlobalTower]
      simp only [C, integralTowerTransition_eq, integralTowerComplex]
      rfl
    have hc₁ := (congrArg (fun B : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E T none ↦
      IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T)
        (DerivedCategory.Q.obj (integralOperationsRoos B))) hC).mp hc₀
    change IntegralPrincipalCone.locallyComplete l E T (integralCompletionScalarValue l E T) K
    exact integralLocallyComplete_iso l E T (integralCompletionScalarValue l E T) i.symm hc₁
  · intro hK
    let := IntegralOnSlice.goodLocalization l E T none
    let := Localization.essSurj (IntegralOnSlice.qGood l E T none)
      ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E T none) (.up ℤ)).inverseImage
        (IntegralOnSlice.Good l E T none).ι)
    let P := (IntegralOnSlice.qGood l E T none).objPreimage K
    let e : DerivedCategory.Q.obj P.obj ≅ K :=
      (IntegralOnSlice.qGood l E T none).objObjPreimageIso K
    have hμ := (integralKoszulScalar_existsUnique l E T P.obj).exists.choose_spec
    have hunit := (IntegralPrincipalCone.localCriterion l E T
      (integralCompletionScalarValue l E T) (integralScalar_natural l E T)
      P.obj (integralKoszulScalar l E T P.obj) hμ K e).2.mp hK
    obtain ⟨c, hc⟩ := integralPrincipalConeQuotientComparison l E T P.obj P.property.1
      (integralKoszulScalar l E T P.obj) hμ
    let D := integralAuxiliaryDatum p
    have hl : l ≠ D.p := hpl.symm
    let C := integralLegacyComplexTower l E T D hl P.obj
    let j := DerivedCategory.Q.mapIso (eqToIso (congrArg integralOperationsRoos
      (integralLegacyTower_eq l E T D hl P.obj)))
    let κ₀ := e.inv ≫ DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none P.obj)
    have hκ₀ : IsIso κ₀ := by
      dsimp only [κ₀]
      rw [← hc, ← Category.assoc]
      have := hunit
      infer_instance
    let κ : K ⟶ DerivedCategory.Q.obj (integralOperationsRoos C) := κ₀ ≫ j.hom
    have hκ : IsIso κ := by dsimp only [κ]; infer_instance
    have hκπ (n : ℕ) :
        κ ≫ DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun k ↦ C.obj (op k))
              (integralOperationsTowerStep C)) ≫ Pi.π (fun k ↦ C.obj (op k)) n) =
          e.inv ≫ DerivedCategory.Q.map (integralTowerUnit l E T D hl P.obj n) := by
      simp only [κ, κ₀, j, Functor.mapIso_hom, eqToIso.hom,
        Category.assoc, ← Functor.map_comp]
      rw [roosProjection_cast _ _ (integralLegacyTower_eq l E T D hl P.obj) n,
        ← Category.assoc, integralRoosUnit_projection, integralAugmentation_cast]
    obtain ⟨δ, hδ⟩ := integralStrictRoosTriangle (A := IntegralOnSlice.Mod l E T none) C
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    have h := integralRoosTransport
      (C := IntegralOnSlice.D l E T none)
      (X := fun n : ℕ ↦
        (DerivedCategory.Q (C := IntegralOnSlice.Mod l E T none)).obj (C.obj (op n)))
      (fun (n : ℕ) ↦
        (DerivedCategory.Q (C := IntegralOnSlice.Mod l E T none)).map
          (integralOperationsTowerStep C n))
      (asIso κ) _ δ hδ
    let ε : (∏ᶜ fun n ↦ DerivedCategory.Q.obj (C.obj (op n))) ⟶
        (shiftFunctor (IntegralOnSlice.D l E T none) (1 : ℤ)).obj K :=
      δ ≫ (shiftFunctor (IntegralOnSlice.D l E T none) (1 : ℤ)).map (asIso κ).inv
    have hqid : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := IntegralOnSlice.ring l E T none) (𝟙 P.obj) :=
      ⟨inferInstance, P.property.1⟩
    let : HasCountableProducts (completedIntegralDerivedCategory l E T D hl) :=
      inferInstanceAs (HasCountableProducts (IntegralOnSlice.D l E T none))
    have hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheaf l E T D hl) (𝟙 P.obj) :=
      hqid
    change IsDerivedCompleteUnrestricted l E T K
    refine ⟨D, hl, ?_⟩
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    refine ⟨P.obj, P.obj, 𝟙 P.obj, hq, e, ?_⟩
    dsimp only
    refine ⟨inferInstance, ?_⟩
    have hstep (n : ℕ) :
        DerivedCategory.Q.map (integralOperationsTowerStep C n) =
          (integralReductionTower l E T D hl P.obj).map (homOfLE n.le_succ).op := by
      simp only [C, integralLegacyComplexTower, integralOperationsTowerStep,
        integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ]
      erw [Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    refine ⟨ε, ?_⟩
    have hπ : (Pi.lift (fun n ↦
        ((integralReductionTowerCone l E T D hl (𝟙 P.obj) hq).extend e.inv).π.app (op n))) =
        κ ≫ Pi.lift (fun n ↦ DerivedCategory.Q.map
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism (K := fun k ↦ C.obj (op k))
              (integralOperationsTowerStep C)) ≫ Pi.π (fun k ↦ C.obj (op k)) n)) := by
      exact productLift_transport κ _ _ (fun n ↦
        (integralLegacyIdentityLeg l E T D hl P.obj hq K e n).trans (hκπ n).symm)
    rw [funext hstep] at h
    rw [hπ]
    exact h

private theorem complete_iff_principalUnit
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (hpl : p ≠ l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) (P : IntegralOnSlice.Cx l E T none) :
    IsDerivedCompleteUnrestricted l E T (DerivedCategory.Q.obj P) ↔
      QuasiIso (CochainComplex.PrincipalCone.unit (integralKoszulScalar l E T P)) := by
  rw [complete_iff_local p l hpl E T]
  have h := (IntegralPrincipalCone.localCriterion l E T
    (integralCompletionScalarValue l E T) (integralScalar_natural l E T)
    P (integralKoszulScalar l E T P)
    (integralKoszulScalar_existsUnique l E T P).exists.choose_spec
    (DerivedCategory.Q.obj P) (Iso.refl _)).2
  simpa only [Iso.refl_inv, Category.id_comp, DerivedCategory.isIso_Q_map_iff_quasiIso] using h

section PrincipalTransport
variable {A : Type a} [Category.{av} A] [Abelian A]
  {B : Type b} [Category.{bv} B] [Abelian B]

private theorem coneKInjective {P Q : CochainComplex A ℤ}
    [P.IsKInjective] [Q.IsKInjective] (f : P ⟶ Q) :
    (CochainComplex.mappingCone f).IsKInjective := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f) ?_ ?_
  · exact CochainComplex.IsKInjective.rightOrthogonal P
  · exact CochainComplex.IsKInjective.rightOrthogonal Q

private theorem productKInjective [HasCountableProducts A]
    (P : ℕ → CochainComplex A ℤ) [∀ n, (P n).IsKInjective] :
    (∏ᶜ P).IsKInjective := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  exact (HomotopyCategory.subcategoryAcyclic A).rightOrthogonal.prop_of_isLimit
    (HomotopyCategory.isLimitFanQuotient A (.up ℤ) (productIsProduct P))
    (fun n ↦ CochainComplex.IsKInjective.rightOrthogonal (P n.as))

private theorem principalKInjective [HasCountableProducts A]
    (P : CochainComplex A ℤ) [P.IsKInjective] (μ : End P) :
    (CochainComplex.PrincipalCone.completion μ).IsKInjective := by
  let : ∀ n : ℕ, ((CochainComplex.PrincipalCone.tower μ).obj (op n)).IsKInjective :=
    fun n ↦ coneKInjective (μ ^ (n + 1)).asHom
  have : (∏ᶜ fun n : ℕ ↦ (CochainComplex.PrincipalCone.tower μ).obj (op n)).IsKInjective :=
    productKInjective _
  have : (CochainComplex.mappingCone
      (CochainComplex.PrincipalCone.oneSubShift μ)).IsKInjective :=
    coneKInjective (CochainComplex.PrincipalCone.oneSubShift μ)
  exact (CochainComplex.isKInjective_shift_iff
    (CochainComplex.mappingCone (CochainComplex.PrincipalCone.oneSubShift μ)) (-1)).mpr
      inferInstance

private theorem mapKInjectiveQuasiIso (H : A ⥤ B) [H.Additive]
    {P Q : CochainComplex A ℤ} [P.IsKInjective] [Q.IsKInjective]
    (f : P ⟶ Q) (hf : QuasiIso f) :
    QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map f) := by
  have : IsIso ((HomotopyCategory.quotient A (.up ℤ)).map f) :=
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences f).mpr
      ((CochainComplex.IsKInjective.quasiIso_iff f).mp hf)
  have hi := (H.mapHomotopyCategory (.up ℤ)).map_isIso
    ((HomotopyCategory.quotient A (.up ℤ)).map f)
  exact homotopyEquivalences_le_quasiIso _ _ _
    ((HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).mp hi)

private def mapCoconeIso (H : A ⥤ B) [H.Additive]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) :
    (H.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mappingCocone f) ≅
      CochainComplex.mappingCocone ((H.mapHomologicalComplex (.up ℤ)).map f) :=
  ((H.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app
      (CochainComplex.mappingCone f) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f H)

private theorem mapCone_fst (H : A ⥤ B) [H.Additive]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (n : ℤ) :
    (CochainComplex.mappingCone.mapHomologicalComplexIso f H).hom.f n ≫
        (CochainComplex.mappingCone.fst
          ((H.mapHomologicalComplex (.up ℤ)).map f)).1.v n (n + 1) rfl =
      H.map ((CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl) := by
  simp only [CochainComplex.mappingCone.mapHomologicalComplexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_fst_v,
    CochainComplex.mappingCone.inr_f_fst_v,
    Limits.comp_zero, add_zero]
  exact Category.comp_id _

private theorem mapCone_snd (H : A ⥤ B) [H.Additive]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (n : ℤ) :
    (CochainComplex.mappingCone.mapHomologicalComplexIso f H).hom.f n ≫
        (CochainComplex.mappingCone.snd
          ((H.mapHomologicalComplex (.up ℤ)).map f)).v n n (add_zero n) =
      H.map ((CochainComplex.mappingCone.snd f).v n n (add_zero n)) := by
  simp only [CochainComplex.mappingCone.mapHomologicalComplexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_snd_v,
    CochainComplex.mappingCone.inr_f_snd_v,
    Limits.comp_zero, zero_add]
  exact Category.comp_id _

private theorem coneMap_fst {P Q P' Q' : CochainComplex A ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (CochainComplex.mappingCone.map f g a b h).f n ≫
        (CochainComplex.mappingCone.fst g).1.v n (n + 1) rfl =
      (CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  apply CochainComplex.mappingCone.ext_from f (n + 1) n rfl <;>
    simp [CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v, Category.assoc]

private theorem coneMap_snd {P Q P' Q' : CochainComplex A ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (CochainComplex.mappingCone.map f g a b h).f n ≫
        (CochainComplex.mappingCone.snd g).v n n (add_zero n) =
      (CochainComplex.mappingCone.snd f).v n n (add_zero n) ≫ b.f n := by
  apply CochainComplex.mappingCone.ext_from f (n + 1) n rfl <;>
    simp [CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v, Category.assoc]

private theorem mapCone_natural (H : A ⥤ B) [H.Additive]
    {P Q P' Q' : CochainComplex A ℤ} (f : P ⟶ Q) (g : P' ⟶ Q')
    (a : P ⟶ P') (b : Q ⟶ Q') (h : f ≫ b = a ≫ g) :
    (H.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.map f g a b h) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso g H).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso f H).hom ≫
        CochainComplex.mappingCone.map _ _
          ((H.mapHomologicalComplex (.up ℤ)).map a)
          ((H.mapHomologicalComplex (.up ℤ)).map b)
          (by simp only [← Functor.map_comp, h]) := by
  ext n
  apply CochainComplex.mappingCone.ext_to _ n (n + 1) rfl
  · simp only [HomologicalComplex.comp_f, Category.assoc, mapCone_fst, coneMap_fst,
      Functor.mapHomologicalComplex_map_f]
    rw [← H.map_comp, coneMap_fst, H.map_comp]
    simp only [← Category.assoc, mapCone_fst]
  · simp only [HomologicalComplex.comp_f, Category.assoc, mapCone_snd, coneMap_snd,
      Functor.mapHomologicalComplex_map_f]
    rw [← H.map_comp, coneMap_snd, H.map_comp]
    simp only [← Category.assoc, mapCone_snd]

private def coneSquareIso {P Q P' Q' : CochainComplex B ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ≅ P') (b : Q ≅ Q')
    (h : f ≫ b.hom = a.hom ≫ g) :
    CochainComplex.mappingCone f ≅ CochainComplex.mappingCone g where
  hom := CochainComplex.mappingCone.map f g a.hom b.hom h
  inv := CochainComplex.mappingCone.map g f a.inv b.inv (by
    rw [← cancel_epi a.hom, ← cancel_mono b.hom]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, h])
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact CochainComplex.mappingCone.map_id f
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact CochainComplex.mappingCone.map_id g

private theorem coneCast_natural {P Q P' Q' : CochainComplex B ℤ}
    (f f' : P ⟶ Q) (g g' : P' ⟶ Q') (hf : f = f') (hg : g = g')
    (a : P ⟶ P') (b : Q ⟶ Q') (h : f ≫ b = a ≫ g) (h' : f' ≫ b = a ≫ g') :
    CochainComplex.mappingCone.map f g a b h ≫
        (eqToIso (congrArg (fun z : P' ⟶ Q' ↦ CochainComplex.mappingCone z) hg)).hom =
      (eqToIso (congrArg (fun z : P ⟶ Q ↦ CochainComplex.mappingCone z) hf)).hom ≫
        CochainComplex.mappingCone.map f' g' a b h' := by
  subst f'; subst g'
  simp

private theorem mapEnd_pow (G : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (P : CochainComplex A ℤ) (μ : End P) (n : ℕ) :
    G.map (μ ^ n).asHom = (((G.mapEnd P) μ) ^ n).asHom :=
  congrArg End.asHom (map_pow (G.mapEnd P) μ n)

private def principalLevelIso (H : A ⥤ B) [H.Additive]
    {P : CochainComplex A ℤ} (μ : End P) (n : ℕ) :
    (H.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.PrincipalCone.level μ n) ≅
      CochainComplex.PrincipalCone.level
        (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) n :=
  CochainComplex.mappingCone.mapHomologicalComplexIso (μ ^ (n + 1)).asHom H ≪≫
    eqToIso (congrArg
      (fun z : (H.mapHomologicalComplex (.up ℤ)).obj P ⟶
        (H.mapHomologicalComplex (.up ℤ)).obj P ↦ CochainComplex.mappingCone z)
      (mapEnd_pow (H.mapHomologicalComplex (.up ℤ)) P μ (n + 1)))

private theorem principalLevelIso_step (H : A ⥤ B) [H.Additive]
    {P : CochainComplex A ℤ} (μ : End P) (n : ℕ) :
    (H.mapHomologicalComplex (.up ℤ)).map (CochainComplex.PrincipalCone.step μ n) ≫
        (principalLevelIso H μ n).hom =
      (principalLevelIso H μ (n + 1)).hom ≫
        CochainComplex.PrincipalCone.step
          (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) n := by
  simp only [principalLevelIso, Iso.trans_hom, CochainComplex.PrincipalCone.step]
  rw [← Category.assoc, mapCone_natural]
  rw [Category.assoc, coneCast_natural _ _ _ _
    (mapEnd_pow (H.mapHomologicalComplex (.up ℤ)) P μ (n + 1 + 1))
    (mapEnd_pow (H.mapHomologicalComplex (.up ℤ)) P μ (n + 1)) _ _ _
    (by
      rw [(H.mapHomologicalComplex (.up ℤ)).map_id P]
      exact CochainComplex.PrincipalCone.square
        (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) n)]
  simp only [(H.mapHomologicalComplex (.up ℤ)).map_id P, Category.assoc]
  rfl

private def towerProductIso (H : A ⥤ B) [H.Additive]
    [HasCountableProducts A] [HasCountableProducts B]
    [PreservesLimitsOfShape (Discrete ℕ) H]
    (K : ℕ → CochainComplex A ℤ) (L : ℕ → CochainComplex B ℤ)
    (e : ∀ n, (H.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ L n) :
    (H.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ K) ≅ ∏ᶜ L :=
  PreservesProduct.iso (H.mapHomologicalComplex (.up ℤ)) K ≪≫ Pi.mapIso e

private theorem towerProductIso_π (H : A ⥤ B) [H.Additive]
    [HasCountableProducts A] [HasCountableProducts B]
    [PreservesLimitsOfShape (Discrete ℕ) H]
    (K : ℕ → CochainComplex A ℤ) (L : ℕ → CochainComplex B ℤ)
    (e : ∀ n, (H.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ L n) (n : ℕ) :
    (towerProductIso H K L e).hom ≫ Pi.π L n =
      (H.mapHomologicalComplex (.up ℤ)).map (Pi.π K n) ≫ (e n).hom := by
  simp [towerProductIso, Category.assoc]

private theorem towerProductIso_transition (H : A ⥤ B) [H.Additive]
    [HasCountableProducts A] [HasCountableProducts B]
    [PreservesLimitsOfShape (Discrete ℕ) H]
    (K : ℕ → CochainComplex A ℤ) (L : ℕ → CochainComplex B ℤ)
    (e : ∀ n, (H.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ L n)
    (τ : ∀ n, K (n + 1) ⟶ K n) (τ' : ∀ n, L (n + 1) ⟶ L n)
    (h : ∀ n, (H.mapHomologicalComplex (.up ℤ)).map (τ n) ≫ (e n).hom =
      (e (n + 1)).hom ≫ τ' n) :
    (H.mapHomologicalComplex (.up ℤ)).map (towerTransitionEndomorphism τ) ≫
        (towerProductIso H K L e).hom =
      (towerProductIso H K L e).hom ≫ towerTransitionEndomorphism τ' := by
  have hs : (H.mapHomologicalComplex (.up ℤ)).map (towerProductShift τ) ≫
      (towerProductIso H K L e).hom =
      (towerProductIso H K L e).hom ≫ towerProductShift τ' := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, towerProductIso_π, towerProductShift, Pi.lift_comp_π]
    rw [← Functor.map_comp_assoc, Pi.lift_comp_π, Functor.map_comp, Category.assoc, h]
    rw [← Category.assoc, ← Category.assoc, towerProductIso_π, Category.assoc]
  simp only [towerTransitionEndomorphism, Functor.map_sub,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id, hs]
  rw [(H.mapHomologicalComplex (.up ℤ)).map_id (∏ᶜ K), Category.id_comp]

private def principalMapIso (H : A ⥤ B) [H.Additive]
    [HasCountableProducts A] [HasCountableProducts B]
    [PreservesLimitsOfShape (Discrete ℕ) H]
    {P : CochainComplex A ℤ} (μ : End P) :
    (H.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.PrincipalCone.completion μ) ≅
      CochainComplex.PrincipalCone.completion
        (End.of ((H.mapHomologicalComplex (.up ℤ)).map μ.asHom)) :=
  mapCoconeIso H (CochainComplex.PrincipalCone.oneSubShift μ) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso
      (coneSquareIso _ _
        (towerProductIso H _ _ (principalLevelIso H μ))
        (towerProductIso H _ _ (principalLevelIso H μ))
        (towerProductIso_transition H _ _ (principalLevelIso H μ) _ _
          (principalLevelIso_step H μ)))

end PrincipalTransport

namespace CompletedCoefficientPushforward
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem push_products {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X)) :
    PreservesLimitsOfShape (Discrete ℕ) (push f c) where
  preservesLimit {D} := by
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
    apply isLimitOfReflects (SheafOfModules.forget (R l E Y))
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    exact isLimitOfPreserves
      (SheafOfModules.evaluation (R l E X) ((proEtaleBaseChange f).op.obj U) ⋙
        ModuleCat.restrictScalars (c.hom.app U).hom) (limit.isLimit D)

private theorem scalar_push {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n) (U : Y.ProEtᵒᵖ) :
    c.hom.app U (integralCompletionScalarValue l E Y U) =
      integralCompletionScalarValue l E X ((proEtaleBaseChange f).op.obj U) := by
  let B := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))
  have hunit : toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B) ≫
      (commConstantPush.{t, u} f B).hom =
    Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)) := by
    exact ((sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv _ _).apply_symm_apply _
  have hs := congrArg (fun k ↦ k.hom.app U
    ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app U
      (ULift.up (Padic.coefficientExtensionUniformizer l E))))
    (structure_constant (l := l) (E := E) (f := f) c hc)
  change c.hom.app U (integralCompletionScalarValue l E Y U) = _ at hs
  rw [hs]
  change (integralConstantToCompletionOfUniverses l E X).hom.app
    ((proEtaleBaseChange f).op.obj U)
    ((commConstantPush.{t, u} f B).hom.app U
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app U
        (ULift.up (Padic.coefficientExtensionUniformizer l E)))) = _
  have hu := congrArg (fun k ↦ k.app U
    (ULift.up (Padic.coefficientExtensionUniformizer l E))) hunit
  rw [show (commConstantPush.{t, u} f B).hom.app U
      ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj B)).app U
        (ULift.up (Padic.coefficientExtensionUniformizer l E))) =
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)).app
        ((proEtaleBaseChange f).op.obj U)
          (ULift.up (Padic.coefficientExtensionUniformizer l E)) from hu]
  rfl

private theorem scalar_chain_push {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    [hpush : (push f c).Additive] (P : IntegralOnSlice.Cx l E X none) :
    End.of (((push f c).mapHomologicalComplex (.up ℤ)).map
      (integralKoszulScalar l E X P).asHom) =
      integralKoszulScalar l E Y (((push f c).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply End.ext
  apply (integralKoszulScalar_existsUnique l E Y
    (((push f c).mapHomologicalComplex (.up ℤ)).obj P)).unique
  · intro q U x
    let V := (proEtaleBaseChange f).op.obj U
    let x₀ : (P.X q).val.obj V := x
    have hx := (integralKoszulScalar_existsUnique l E X P).exists.choose_spec q V x₀
    have ht := congrArg
      (fun z : (IntegralOnSlice.rings l E X none).obj.obj V ↦ z • x₀)
      (scalar_push l E f c hc U)
    exact hx.trans ht.symm
  · exact (integralKoszulScalar_existsUnique l E Y
      (((push f c).mapHomologicalComplex (.up ℤ)).obj P)).exists.choose_spec

/-- The normalized direct image along the canonical finite-projection structural
map preserves derived completeness, independently of choices of total derived model.

Source: Stacks proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case (1),(3)
(blueprint: lem-pur-completed-direct-image-preserves-completeness).
Proof:
1. Extract the datum-independent local-completeness equivalence from the existing
Roos argument. The converse uses a termwise-flat K-flat representative and the
principal-cone/quotient comparison, retaining the specified quotient augmentation.
2. Represent K by a K-injective complex J. The principal-uniformizer completion unit
of J is a quasi-isomorphism. Its target is also K-injective: each cone level is,
products of K-injectives are K-injective, and the final shifted cone is K-injective.
Thus this unit is a homotopy equivalence, preserved by any additive functor.
3. Module pushforward preserves countable products, as seen after evaluating its
underlying module presheaves: source evaluation and scalar restriction preserve
limits. Its termwise functor commutes with cones and shifts. Naturality of the cone comparison
for the (uniformizer, identity) transition squares gives a product comparison
conjugating one minus the transition shift. Applying the shifted cone comparison
identifies pushforward of the principal completion with completion of the image.
4. The equations hc imply the constant-to-completion square for c. Applying the
constant sheafification unit to the uniformizer shows that the image scalar is
the actual target uniformizer. Its principal completion is locally complete by
the local criterion. Transport completeness through the comparison and the image
of the source unit, then through F's K-injective computation isomorphism.
All countable products and positive powers retain their original transitions;
the argument also applies to empty schemes and zero complexes. -/
theorem directImage_preservesComplete (p : ℕ) [Fact p.Prime] (hlp : l ≠ p)
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (c : R l E Y ⟶ (ringPush.{t, u} f).obj (R l E X))
    (hc : ∀ n, c ≫ (ringPush.{t, u} f).map (projection l E X n) =
      projection l E Y n ≫ finiteStructure l E f n)
    [hpush : (push f c).Additive] (F : RightImage (push f c))
    (K : DerivedCategory (Mod X (R l E X)))
    (hK : IsDerivedCompleteUnrestricted l E X K) :
    IsDerivedCompleteUnrestricted l E Y (F.functor.obj K) := by
  classical
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} X
  let : HasCountableProducts (IntegralOnSlice.Mod l E X none) := inferInstance
  let : HasCountableProducts (IntegralOnSlice.Mod l E Y none) := inferInstance
  let : Abelian (IntegralOnSlice.Mod l E X none) := inferInstance
  let : Abelian (IntegralOnSlice.Mod l E Y none) := inferInstance
  let H : IntegralOnSlice.Mod l E X none ⥤ IntegralOnSlice.Mod l E Y none := push f c
  let G := H.mapHomologicalComplex (.up ℤ)
  have : PreservesLimitsOfShape (Discrete ℕ) H := push_products l E f c
  obtain ⟨_, _, I, η, hI⟩ :=
    SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X)
  let P := DerivedCategory.Q.objPreimage K
  let J := I.obj P
  have : J.IsKInjective := (hI P).2.1
  have : QuasiIso (η.app P) := (hI P).1
  let e : DerivedCategory.Q.obj J ≅ K :=
    (asIso (DerivedCategory.Q.map (η.app P))).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hJ : IsDerivedCompleteUnrestricted l E X (DerivedCategory.Q.obj J) :=
    (complete_iff_local p l hlp.symm E X _).mpr
      (integralLocallyComplete_iso l E X _ e.symm
        ((complete_iff_local p l hlp.symm E X K).mp hK))
  let μ := integralKoszulScalar l E X J
  have hμ : QuasiIso (CochainComplex.PrincipalCone.unit μ) :=
    (complete_iff_principalUnit p l hlp.symm E X J).mp hJ
  have : (CochainComplex.PrincipalCone.completion μ).IsKInjective := principalKInjective J μ
  have : QuasiIso (G.map (CochainComplex.PrincipalCone.unit μ)) :=
    mapKInjectiveQuasiIso H _ hμ
  have hscalar : End.of (G.map μ.asHom) = integralKoszulScalar l E Y (G.obj J) :=
    scalar_chain_push l E f c hc J
  let a : DerivedCategory.Q.obj (G.obj J) ≅
      DerivedCategory.Q.obj
        (CochainComplex.PrincipalCone.completion (integralKoszulScalar l E Y (G.obj J))) :=
    asIso (DerivedCategory.Q.map (G.map (CochainComplex.PrincipalCone.unit μ))) ≪≫
      DerivedCategory.Q.mapIso (principalMapIso H μ) ≪≫
        DerivedCategory.Q.mapIso (eqToIso (congrArg
          (fun z : End (G.obj J) ↦ CochainComplex.PrincipalCone.completion z) hscalar))
  have hcomplete := (IntegralPrincipalCone.localCriterion l E Y
    (integralCompletionScalarValue l E Y) (integralScalar_natural l E Y)
    (G.obj J) (integralKoszulScalar l E Y (G.obj J))
    (integralKoszulScalar_existsUnique l E Y (G.obj J)).exists.choose_spec
    (DerivedCategory.Q.obj (G.obj J)) (Iso.refl _)).1
  have hlocal := integralLocallyComplete_iso l E Y _ a.symm hcomplete
  have : IsIso (F.unit.app J) := F.computes J inferInstance
  exact (complete_iff_local p l hlp.symm E Y _).mpr
    (integralLocallyComplete_iso l E Y _
      (asIso (F.unit.app J) ≪≫ F.functor.mapIso e) hlocal)

end CompletedCoefficientPushforward
end WeilConjectures
