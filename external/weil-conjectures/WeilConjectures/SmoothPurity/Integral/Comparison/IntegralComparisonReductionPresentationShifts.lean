/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonCanonicalShifts
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison

/-! # Reindexing a coherent quotient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

private theorem adjHom_shift
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F : A ⥤ B} {G : B ⥤ A} [F.CommShift ℤ] [G.CommShift ℤ]
    (adj : F ⊣ G) [adj.CommShift ℤ] (n : ℤ) {X : A} {Y : B}
    (a : F.obj X ⟶ Y) :
    adj.homEquiv _ _ ((F.commShiftIso n).hom.app X ≫ a⟦n⟧') =
      (adj.homEquiv X Y a)⟦n⟧' ≫ (G.commShiftIso n).inv.app Y := by
  apply (cancel_mono ((G.commShiftIso n).hom.app Y)).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  rw [Functor.commShiftIso_hom_naturality]
  have hu := adj.unit_app_commShiftIso_hom_app ℤ n X
  simp only [Functor.commShiftIso_comp_hom_app] at hu
  simpa only [Functor.map_comp, Category.comp_id, Category.assoc] using
    congrArg (fun b ↦ b ≫ (G.map a)⟦n⟧') hu

private theorem adjHom_conjugate
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F : A ⥤ B} {G : B ⥤ A} [F.CommShift ℤ] [G.CommShift ℤ]
    (adj : F ⊣ G) [adj.CommShift ℤ] (n : ℤ) {X X' : A} {Y Y' : B}
    (a : F.obj X ⟶ Y) (α : X' ⟶ X⟦n⟧) (β : Y⟦n⟧ ⟶ Y') :
    adj.homEquiv _ _ (F.map α ≫ (F.commShiftIso n).hom.app X ≫ a⟦n⟧' ≫ β) =
      α ≫ (adj.homEquiv X Y a)⟦n⟧' ≫ (G.commShiftIso n).inv.app Y ≫ G.map β := by
  rw [adj.homEquiv_naturality_left, ← Category.assoc,
    adj.homEquiv_naturality_right, adjHom_shift]
  simp only [Category.assoc]

private theorem doubleTranspose_shift
    {A B D : Type*} [Category A] [Category B] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
    (L : A ⥤ B) (H : B ⥤ D) (G : D ⥤ A) (T : A ⥤ D)
    [L.CommShift ℤ] [H.CommShift ℤ] [G.CommShift ℤ] [T.CommShift ℤ]
    (adj : L ⊣ H ⋙ G) (ad : T ⊣ G) [adj.CommShift ℤ] [ad.CommShift ℤ]
    (n : ℤ) {X X' : A} {Y Y' : B} (a : L.obj X ⟶ Y)
    (α : X' ⟶ X⟦n⟧) (β : Y⟦n⟧ ⟶ Y') :
    (ad.homEquiv _ _).symm
      (adj.homEquiv _ _
        (L.map α ≫ (L.commShiftIso n).hom.app X ≫ a⟦n⟧' ≫ β)) =
      T.map α ≫ (T.commShiftIso n).hom.app X ≫
        ((ad.homEquiv _ _).symm (adj.homEquiv X Y a))⟦n⟧' ≫
        (H.commShiftIso n).inv.app Y ≫ H.map β := by
  apply (ad.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  have ht := adjHom_conjugate ad n
    ((ad.homEquiv _ _).symm (adj.homEquiv X Y a)) α
      ((H.commShiftIso n).inv.app Y ≫ H.map β)
  rw [ht, Equiv.apply_symm_apply, adjHom_conjugate]
  simp only [Functor.commShiftIso_comp_inv_app, Functor.comp_map, Functor.map_comp,
    Category.assoc]

private theorem shiftedIso_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (Q₁ : A ⥤ C) (Q₂ : B ⥤ D) (L : C ⥤ D)
    [Q₁.CommShift ℤ] [Q₂.CommShift ℤ] [L.CommShift ℤ]
    (P : A) (K : B) (e : L.obj (Q₁.obj P) ≅ Q₂.obj K) (m : ℤ) :
    (L.mapIso ((Q₁.commShiftIso m).app P) ≪≫
      (L.commShiftIso m).app (Q₁.obj P) ≪≫
        (shiftFunctor _ m).mapIso e ≪≫ ((Q₂.commShiftIso m).app K).symm).hom =
      L.map ((Q₁.commShiftIso m).hom.app P) ≫
        (L.commShiftIso m).hom.app (Q₁.obj P) ≫ e.hom⟦m⟧' ≫
          (Q₂.commShiftIso m).inv.app K := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv]

private theorem localized_shift_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ C) (R : B ⥤ C) (Q : C ⥤ D)
    [F.CommShift ℤ] [R.CommShift ℤ] [Q.CommShift ℤ]
    (P : A) (N : B) (m : ℤ) (b : F.obj P ⟶ R.obj N)
    (bm : F.obj (P⟦m⟧) ⟶ R.obj (N⟦m⟧))
    (hb : bm ≫ (R.commShiftIso m).hom.app N =
      (F.commShiftIso m).hom.app P ≫ b⟦m⟧') :
    Q.map bm ≫ ((R ⋙ Q).commShiftIso m).hom.app N =
      ((F ⋙ Q).commShiftIso m).hom.app P ≫ (Q.map b)⟦m⟧' := by
  simp only [Functor.commShiftIso_comp_hom_app]
  rw [← Q.map_comp_assoc, hb, Q.map_comp, Category.assoc,
    Q.commShiftIso_hom_naturality]
  simp only [Category.assoc]

private theorem localized_conjugate
    {A B C A' B' D : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [HasShift A' ℤ] [HasShift B' ℤ] [HasShift D ℤ]
    (Q₁ : A ⥤ A') (Q₂ : B ⥤ B') (Q₃ : C ⥤ D)
    (F : A ⥤ C) (R : B ⥤ C) (T : A' ⥤ D) (H : B' ⥤ D)
    [Q₁.CommShift ℤ] [Q₂.CommShift ℤ] [Q₃.CommShift ℤ]
    [F.CommShift ℤ] [R.CommShift ℤ] [T.CommShift ℤ] [H.CommShift ℤ]
    (τ : Q₁ ⋙ T ≅ F ⋙ Q₃) (υ : Q₂ ⋙ H ≅ R ⋙ Q₃)
    [NatTrans.CommShift τ.hom ℤ] [NatTrans.CommShift υ.inv ℤ]
    (P : A) (N : B) (m : ℤ) (b : F.obj P ⟶ R.obj N) :
    let bm := (F.commShiftIso m).hom.app P ≫ b⟦m⟧' ≫ (R.commShiftIso m).inv.app N
    τ.hom.app (P⟦m⟧) ≫ Q₃.map bm ≫ υ.inv.app (N⟦m⟧) =
      T.map ((Q₁.commShiftIso m).hom.app P) ≫ (T.commShiftIso m).hom.app (Q₁.obj P) ≫
        (τ.hom.app P ≫ Q₃.map b ≫ υ.inv.app N)⟦m⟧' ≫
        (H.commShiftIso m).inv.app (Q₂.obj N) ≫ H.map ((Q₂.commShiftIso m).inv.app N) := by
  dsimp only
  apply (cancel_mono (((Q₂ ⋙ H).commShiftIso m).hom.app N)).1
  have hb : ((F.commShiftIso m).hom.app P ≫ b⟦m⟧' ≫
      (R.commShiftIso m).inv.app N) ≫ (R.commShiftIso m).hom.app N =
        (F.commShiftIso m).hom.app P ≫ b⟦m⟧' := by simp only [Category.assoc,
          Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  have hQ := localized_shift_square F R Q₃ P N m b _ hb
  have hυ := NatTrans.shift_app_comm υ.inv m N
  have hτ := NatTrans.shift_app_comm τ.hom m P
  simp only [Category.assoc] at hυ hτ ⊢
  rw [← hυ]
  rw [← Category.assoc (Q₃.map _), hQ]
  simp only [Category.assoc]
  rw [← reassoc_of% hτ]
  have hc := Iso.inv_hom_id_app ((Q₂ ⋙ H).commShiftIso m) N
  rw [Functor.commShiftIso_comp_inv_app] at hc
  simp only [Category.assoc] at hc
  rw [hc]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp,
    Category.assoc, Functor.comp_obj, Category.comp_id]

private theorem shifted_transpose_square
    {A B C A' B' D : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [HasShift A' ℤ] [HasShift B' ℤ] [HasShift D ℤ]
    (Q₁ : A ⥤ A') (Q₂ : B ⥤ B') (Q₃ : C ⥤ D)
    (F : A ⥤ C) (R : B ⥤ C) (T : A' ⥤ D) (H : B' ⥤ D)
    (L : A' ⥤ B') (G : D ⥤ A')
    [Q₁.CommShift ℤ] [Q₂.CommShift ℤ] [Q₃.CommShift ℤ]
    [F.CommShift ℤ] [R.CommShift ℤ] [T.CommShift ℤ] [H.CommShift ℤ]
    [L.CommShift ℤ] [G.CommShift ℤ]
    (adj : L ⊣ H ⋙ G) (ad : T ⊣ G) [adj.CommShift ℤ] [ad.CommShift ℤ]
    (τ : Q₁ ⋙ T ≅ F ⋙ Q₃) (υ : Q₂ ⋙ H ≅ R ⋙ Q₃)
    [shiftτ : NatTrans.CommShift τ.hom ℤ] [shiftυ : NatTrans.CommShift υ.inv ℤ]
    (P : A) (K : B) (e : L.obj (Q₁.obj P) ≅ Q₂.obj K)
    (b : F.obj P ⟶ R.obj K)
    (he : (ad.homEquiv _ _).symm (adj.homEquiv _ _ e.hom) =
      τ.hom.app P ≫ Q₃.map b ≫ υ.inv.app K) (m : ℤ) :
    (ad.homEquiv _ _).symm (adj.homEquiv _ _
      (L.mapIso ((Q₁.commShiftIso m).app P) ≪≫
        (L.commShiftIso m).app (Q₁.obj P) ≪≫
          (shiftFunctor _ m).mapIso e ≪≫ ((Q₂.commShiftIso m).app K).symm).hom) =
      τ.hom.app (P⟦m⟧) ≫
        Q₃.map ((F.commShiftIso m).hom.app P ≫ b⟦m⟧' ≫ (R.commShiftIso m).inv.app K) ≫
          υ.inv.app (K⟦m⟧) := by
  rw [shiftedIso_hom, doubleTranspose_shift L H G T adj ad, he]
  exact (localized_conjugate Q₁ Q₂ Q₃ F R T H τ υ P K m b).symm

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem reduction_transpose_eq (Y : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E Y)
    {A : DerivedCategory (scalarReductionSource l E Y)}
    {B : coefficientSequenceDerived l E Y} (a : S.reduction.obj A ⟶ B) :
    (integralComparisonConstantTower l E Y).map
        (S.adjunction.unit.app A ≫ (coefficientSequenceLimit l E Y).map a) ≫
      (integralComparisonTowerCounit l E Y).app
        ((coefficientSequenceDerivedRestriction l E Y).obj B) =
    ((integralComparisonConstantAdjunction l E Y).homEquiv _ _).symm
      (S.adjunction.homEquiv _ _ a) := by
  unfold coefficientSequenceLimit integralComparisonTowerCounit
  erw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit]

private theorem constant_factors_shift (Y : Scheme.{u}) :
    NatTrans.CommShift
      (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E Y).mapDerivedCategoryFactors.hom ℤ := by
  infer_instance

/-- Conjugate a quotient presentation by the fixed adjoint and localization shifts. -/
def integralComparisonShiftedReductionIso (Y : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C) (m : ℤ) :
    S.reduction.obj (DerivedCategory.Q.obj (P⟦m⟧)) ≅ DerivedCategory.Q.obj (C⟦m⟧) :=
  letI := integralComparisonReductionShift l E Y S
  S.reduction.mapIso ((DerivedCategory.Q.commShiftIso m).app P) ≪≫
    (S.reduction.commShiftIso m).app (DerivedCategory.Q.obj P) ≪≫
      (shiftFunctor _ m).mapIso e ≪≫ ((DerivedCategory.Q.commShiftIso m).app C).symm

/-- Finite comparisons shift termwise, by ordinary degree reindexing. -/
def integralComparisonShiftedFiniteIso (Y : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P) (m : ℤ) (n : ℕ) :
    ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj (C⟦m⟧) ≅
      (unrestrictedIntegralFiniteComplex l E Y n).obj (P⟦m⟧) :=
  (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).commShiftIso
    m).app C ≪≫ (shiftFunctor _ m).mapIso (κ n) ≪≫
      (((unrestrictedIntegralFiniteComplex l E Y n).commShiftIso m).app P).symm

/-- A coherent reduction presentation remains coherent under the fixed shifts.

Source: Stacks 014E, 06YY and 0941; step 1 of
lem-sf-integral-pullback-realization-shifts.
(blueprint: lem-sf-integral-reduction-presentation-shifts).

Proof: compute each total-limit projection on a simultaneous K-injective
replacement. Its term in degree j after shifting by m is the original term
in degree j+m. Transpose this equation through the finite scalar adjunction.
The counit_projection identity identifies its mate with reductionEvaluation;
the canonical left-adjoint shift is defined by precisely this mate. The
universal finite scalar counit identifies its representative with termwise
reindexing. Thus the first presentation equation holds after conjugating e
by the reduction and localization shifts and kappa by the ordinary termwise
shifts, exactly as in the two displayed definitions. Apply the shift functor
to the horizontal equation to obtain the second presentation equation.
For whole-system coherence shift its strict tensor-unit map b. Its section
formula is unchanged in degree j+m. The constant-tower/limit adjunction and
its shift-compatible unit and counit give the entire-tower transpose equation,
including the exact localization factors. This proves coherence without using
finite evaluations to detect derived morphisms. Zero shift is identity;
negative shifts and the zero complex use the same reindexing formulas. -/
theorem integralComparisonReductionPresentation_shift (Y : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)
    (hp : CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ)
    (hcoh : IsIntegralComparisonPresentationCoherent l E Y S P.obj C e κ)
    (m : ℤ) (hm : integralOperationsGoodComplex l E Y (P.obj⟦m⟧)) :
    CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      (P.obj⟦m⟧) hm.1 (C⟦m⟧) (integralComparisonShiftedReductionIso l E Y S P.obj C e m)
      (integralComparisonShiftedFiniteIso l E Y P.obj C κ m) ∧
    IsIntegralComparisonPresentationCoherent l E Y S (P.obj⟦m⟧) (C⟦m⟧)
      (integralComparisonShiftedReductionIso l E Y S P.obj C e m)
      (integralComparisonShiftedFiniteIso l E Y P.obj C κ m) := by
  let F₀ : scalarReductionSource l E Y ⥤ ℕᵒᵖ ⥤ scalarReductionSource l E Y :=
    Functor.const ℕᵒᵖ
  let F := F₀.mapHomologicalComplex (.up ℤ)
  let R := (coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ)
  let T := integralComparisonConstantTower l E Y
  let H := coefficientSequenceDerivedRestriction l E Y
  let G := coefficientConstantTowerLimit l E Y
  let instT : T.CommShift ℤ := by dsimp [T, integralComparisonConstantTower]; infer_instance
  let instH : H.CommShift ℤ := by dsimp [H, coefficientSequenceDerivedRestriction]; infer_instance
  let : G.CommShift ℤ := by dsimp [G, coefficientConstantTowerLimit]; infer_instance
  let adj : S.reduction ⊣ H ⋙ G := S.adjunction
  let : S.reduction.CommShift ℤ := adj.leftAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  let ad := integralComparisonConstantAdjunction l E Y
  let : ad.CommShift ℤ := by
    exact canonicalRightDerivedAdjunctionShift
      (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Y))
  have hcm : IsIntegralComparisonPresentationCoherent l E Y S (P.obj⟦m⟧) (C⟦m⟧)
      (integralComparisonShiftedReductionIso l E Y S P.obj C e m)
      (integralComparisonShiftedFiniteIso l E Y P.obj C κ m) := by
    unfold IsIntegralComparisonPresentationCoherent at hcoh ⊢
    obtain ⟨b, hb, he⟩ := hcoh
    let bm := (F.commShiftIso m).hom.app P.obj ≫ b⟦m⟧' ≫
      (R.commShiftIso m).inv.app C
    refine ⟨bm, ?_, ?_⟩
    · intro n i U x
      have hbm : bm.f i = b.f (i + m) := by
        change (𝟙 _ ≫ b.f (i + m) ≫ 𝟙 _) = _
        simp only [Category.id_comp, Category.comp_id]
      rw [hbm]
      change (((b.f (i + m)).app (op n)).val.app U) x = _
      change _ = integralComparisonRestrictedSection l E Y (C.X (i + m)) n U
        (integralComparisonSequenceSection l E Y (C.X (i + m)) n U
          (((κ n).inv.f (i + m)).val.app U
            (unrestrictedIntegralTensorSection l E Y n (P.obj.X (i + m)) U 1 x)))
      exact hb n (i + m) U x
    · apply (reduction_transpose_eq l E Y S
        (integralComparisonShiftedReductionIso l E Y S P.obj C e m).hom).trans
      rw [integralComparisonShiftedReductionIso]
      refine shifted_transpose_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
        F R T H S.reduction G adj ad F₀.mapDerivedCategoryFactors
        (coefficientSequenceRestriction l E Y).mapDerivedCategoryFactors
        (shiftτ := ?_) (shiftυ := ?_)
        P.obj C e b ((reduction_transpose_eq l E Y S e.hom).symm.trans he) m
      · exact constant_factors_shift l E Y
      · dsimp [H, R, coefficientSequenceDerivedRestriction, instH]
        exact NatTrans.CommShift.of_iso_inv _ _
  refine ⟨?_, hcm⟩
  unfold CoefficientReductionPresentation
  constructor
  · obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E Y S
    obtain ⟨a, ha, hκ⟩ := coherentQuotientModelComparison l E Y S M D
      (P.obj⟦m⟧) (C⟦m⟧)
      (integralComparisonShiftedReductionIso l E Y S P.obj C e m)
      (integralComparisonShiftedFiniteIso l E Y P.obj C κ m) hcm
    intro n
    unfold CoefficientComparisonEquation
    dsimp [unrestrictedIntegralFiniteComplex, unrestrictedIntegralReductionFunctor]
    rw [← ha, Functor.map_comp, Category.assoc]
    have hn := (coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.naturality
      a.hom
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, ← DerivedCategory.Q.map_comp]
    have hk := congrArg Iso.hom (hκ n)
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hk
    erw [hk]
    exact D.reduction_evaluation (P.obj⟦m⟧) hm.1 hm.2 n
  · intro a b hab
    have hn := hp.2 a b hab
    unfold CoefficientTransitionEquation at hn ⊢
    apply HomologicalComplex.hom_ext
    intro i
    have hi := congrArg (fun f ↦ f.f (i + m)) hn
    change (coefficientSequenceTransition l E Y hab).app (C.X (i + m)) ≫
        (normalizedDVRModuleRes l E Y hab).map ((κ b).hom.f (i + m)) =
      (κ a).hom.f (i + m) ≫
        (coefficientOrdinaryQuotient l E Y hab).app (P.obj.X (i + m))
    exact hi

end WeilConjectures
