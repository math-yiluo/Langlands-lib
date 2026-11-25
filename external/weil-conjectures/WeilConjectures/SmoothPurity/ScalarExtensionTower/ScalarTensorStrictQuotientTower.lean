/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.SmoothPurity.Scalar.ScalarRoosFunctorNaturality
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import all WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation

/-! # The strict scalar tensor square on quotient towers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

private theorem scalarRoos_iso_quotient
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (t : F ≅ G)
    (C D : ℕᵒᵖ ⥤ CochainComplex A ℤ) (q : C ≅ D)
    (Z : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (a : C ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ Z) :
    (F.mapHomologicalComplex (.up ℤ)).map (integralOperationsRoosMap q.inv) ≫
        (NatIso.mapHomologicalComplex t (.up ℤ)).hom.app (integralOperationsRoos C) ≫
        scalarRoosMap G C ≫ integralOperationsRoosMap a =
      scalarRoosMap F D ≫ integralOperationsRoosMap
        (Functor.whiskerRight q.inv (F.mapHomologicalComplex (.up ℤ)) ≫
          Functor.whiskerLeft C (NatIso.mapHomologicalComplex t (.up ℤ)).hom ≫ a) := by
  have ht := scalarRoos_functor_naturality F G t.hom C
  have hq := scalarRoosNaturality F q.inv
  change _ ≫ (NatTrans.mapHomologicalComplex t.hom (.up ℤ)).app _ ≫ _ = _
  rw [reassoc_of% ht]
  rw [← Category.assoc, hq]
  simp only [Category.assoc, integralOperationsRoosMap_comp]
  rfl

/-- Pasting naturality squares with a normalized tensor coordinate. -/
private theorem normalized_tensor_word {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    (T : 𝒟 ⥤ 𝒞) {X₀ X₁ X₂ Y Z₀ Z₁ : 𝒞} {A₀ A₁ A₂ A₃ A₄ A₅ : 𝒟}
    (s : X₀ ⟶ X₁) (f : X₁ ⟶ X₂) (v₂ : X₂ ⟶ T.obj A₀)
    (v₁ : X₁ ⟶ T.obj A₁) (d : X₁ ⟶ Y) (v : Y ⟶ T.obj A₄)
    (k : A₁ ⟶ A₀) (b : A₀ ⟶ A₂) (y : A₂ ⟶ A₃)
    (c : A₁ ⟶ A₄) (e : A₄ ⟶ A₅) (m : A₅ ⟶ A₃)
    (r : T.obj A₃ ⟶ Z₀) (z : Z₀ ⟶ Z₁) (w : Y ⟶ Z₁)
    (hf : f ≫ v₂ = v₁ ≫ T.map k) (hk : k ≫ b ≫ y = c ≫ e ≫ m)
    (hd : d ≫ v = v₁ ≫ T.map c)
    (hw : v ≫ T.map e ≫ T.map m ≫ r ≫ z = w) :
    s ≫ f ≫ v₂ ≫ T.map b ≫ T.map y ≫ r ≫ z = s ≫ d ≫ w := by
  rw [reassoc_of% hf, ← T.map_comp_assoc, ← T.map_comp_assoc]
  simp only [Category.assoc]
  rw [hk]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hd, hw]

/-- Transport a tensor comparison along two representative isomorphisms. -/
private theorem tensor_comparison_transport
    {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    (A : 𝒞 ⥤ 𝒟) (T : 𝒞 × 𝒞 ⥤ 𝒞) (B : 𝒟 × 𝒟 ⥤ 𝒟)
    (α : T ⋙ A ⟶ A.prod A ⋙ B)
    {c d c' d' h : 𝒞} {s t k k' : 𝒟}
    (f : c ⟶ c') (g : d ⟶ d') (εc : A.obj c' ⟶ s) (εd : A.obj d' ⟶ t)
    (εh : A.obj h ⟶ k) (σ : k ⟶ k') (m : h ≅ T.obj (c', d'))
    (n : k' ≅ B.obj (s, t))
    (hs : A.map m.hom ≫ α.app (c', d') ≫ B.map (Prod.mkHom εc εd) =
      εh ≫ σ ≫ n.hom) :
    α.app (c, d) ≫ (B.map (Prod.mkHom (A.map f ≫ εc) (A.map g ≫ εd)) ≫ n.inv) =
      A.map (T.map (Prod.mkHom f g) ≫ m.inv) ≫ εh ≫ σ := by
  have hn := α.naturality (Prod.mkHom f g)
  change A.map (T.map (Prod.mkHom f g)) ≫ α.app (c', d') =
    α.app (c, d) ≫ B.map (Prod.mkHom (A.map f) (A.map g)) at hn
  have hm : α.app (c', d') ≫ B.map (Prod.mkHom εc εd) ≫ n.inv =
      A.map m.inv ≫ εh ≫ σ := by
    apply (cancel_epi (A.map m.hom)).1
    rw [← A.map_comp_assoc, m.hom_inv_id, A.map_id, Category.id_comp]
    rw [reassoc_of% hs]
    simp only [Iso.hom_inv_id, Category.comp_id]
  have hp : Prod.mkHom (A.map f ≫ εc) (A.map g ≫ εd) =
      Prod.mkHom (A.map f) (A.map g) ≫ Prod.mkHom εc εd := rfl
  rw [hp, B.map_comp, A.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  exact congrArg (A.map (T.map (Prod.mkHom f g)) ≫ ·) hm

/-- Paste the scalar counit square after transport to strict tensor coordinates. -/
private theorem normalized_scalar_word {𝒞 : Type*} [Category* 𝒞]
    {X SX YX YR YA YL RL Z AH ASH YH SY OY OE RE RE' OE' RSH : 𝒞}
    (χX : X ⟶ SX) (sX : SX ⟶ YX) (ar : YX ⟶ YR) (α : YR ⟶ YA)
    (y : YA ⟶ YL) (rL : YL ⟶ RL) (qL : RL ⟶ Z)
    (ax : YR ⟶ AH) (ε : AH ⟶ ASH) (σ : ASH ⟶ YL)
    (rg : YX ⟶ YH) (ac : YH ⟶ AH) (rSH : ASH ⟶ RSH) (τ : RSH ⟶ RL)
    (sg : SX ⟶ SY) (sY : SY ⟶ YH) (og : X ⟶ OY) (χY : OY ⟶ SY)
    (cmp : X ⟶ OE) (iq : OE ⟶ RE) (ir : RE ⟶ OY)
    (dR : RE ⟶ RE') (front : RE' ⟶ RSH) (dT : OE ⟶ OE')
    (start : OE' ⟶ RE') (chain : OE' ⟶ Z)
    (hsq : α ≫ y = ax ≫ ε ≫ σ) (hadj : ar ≫ ax = rg ≫ ac)
    (hb : σ ≫ rL = rSH ≫ τ) (hn : sX ≫ rg = sg ≫ sY)
    (hχ : χX ≫ sg = og ≫ χY) (hg : og = cmp ≫ iq ≫ ir)
    (hc : ir ≫ χY ≫ sY ≫ ac ≫ ε ≫ rSH = dR ≫ front)
    (hf : iq ≫ dR = dT ≫ start) (ht : start ≫ front ≫ τ ≫ qL = chain) :
    χX ≫ sX ≫ ar ≫ α ≫ y ≫ rL ≫ qL = cmp ≫ dT ≫ chain := by
  rw [reassoc_of% hsq, reassoc_of% hadj, reassoc_of% hb,
    reassoc_of% hn, reassoc_of% hχ, hg]
  simp only [Category.assoc]
  rw [reassoc_of% hc, reassoc_of% hf, ht]

attribute [local irreducible] HasDerivedCategory.standard integralOrdinaryScalar
  integralComparisonSequenceScalarModel coefficientSequenceRestriction
  completedIntegralCommRingSheafUnrestricted integralOperationsTensorTowerFunctor
  integralOrdinaryTensorSection unrestrictedIntegralTensorSection comparisons
attribute [local implicit_reducible] integralOperationsRoosFunctor NatIso.mapHomologicalComplex

attribute [-instance] WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived WeilConjectures.integralOperationsSiteSmall
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 50000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private local instance (W : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private local instance (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem bridge_naturality (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W) {C D : Complex l E W} (f : C ⟶ D) :
    (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map f) ≫
        (integralComparisonRoosBridge l E W ρ D).hom =
      (integralComparisonRoosBridge l E W ρ C).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map f))) := by
  let U := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)
  let b := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors
        (coefficientConstantTowerLimit l E W) ≪≫
    Functor.isoWhiskerLeft U ρ.comparison
  with_unfolding_all exact b.hom.naturality f

private theorem presentation_good (W : Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (C : Complex l E W)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P.obj) : Good l E W C := by
  constructor
  · apply WeilConjectures.kflat_of_levels l E W
    intro n
    exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E W n)
      (κ n).symm ((coefficientTensorModelPreservation l E W).1 P.obj P.property.1 n)
  · intro i
    apply WeilConjectures.flat_of_levels l E W
    intro n
    apply SheafOfModules.flatOnSite_of_iso (integralCoefficientCommRingSheaf l E W n)
      ((HomologicalComplex.eval _ _ i).mapIso (κ n)).symm
    exact WeilConjectures.flat_extension l E W n (P.obj.X i) (P.property.2 i)

private theorem section_cast_cancel {A B : AddCommGrpCat.{u + 1}} (h : A = B) (x : A) :
    (eqToHom h.symm) ((eqToHom h) x) = x := by
  subst h
  rfl

private theorem evaluation_sequence_section (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj M).val.obj U) :
    coefficientEvaluationSection l E W M n U
      (integralComparisonSequenceSection l E W M n U x) = x := by
  exact section_cast_cancel _ _

private theorem scalar_tensor_level_ext (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ)
    (H : CochainComplex (integralTowerModules l L W) ℤ)
    (a b : ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj
      ((integralOperationsTensorLevel l E W n).obj (P, Q)) ⟶ H)
    (hab : ∀ (p q : ℤ) (U : W.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (a.f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U 1
          (integralOperationsTotalTensorSection l E W n P Q p q U
            (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y))) =
      (b.f (p + q)).val.app U
        (integralOrdinaryTensorSection l E L ι W _ U 1
          (integralOperationsTotalTensorSection l E W n P Q p q U
            (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)))) : a = b := by
  apply HomologicalComplex.hom_ext
  intro k
  apply ((scalarAdjunction l E L ι W).homEquiv _ _).injective
  apply finite_tensor_ext l E W n P Q k
  intro p q hpq U x y
  subst k
  change (a.f (p + q)).val.app U (((scalarAdjunction l E L ι W).unit.app _).val.app U
      (integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n _ U 1 x)
        (unrestrictedIntegralTensorSection l E W n _ U 1 y))) =
    (b.f (p + q)).val.app U (((scalarAdjunction l E L ι W).unit.app _).val.app U
      (integralOperationsTotalTensorSection l E W n P Q p q U
        (unrestrictedIntegralTensorSection l E W n _ U 1 x)
        (unrestrictedIntegralTensorSection l E W n _ U 1 y)))
  have hs := scalarAdjunction_unit l E L ι W
    (((integralOperationsTensorLevel l E W n).obj (P, Q)).X (p + q)) U
    (integralOperationsTotalTensorSection l E W n P Q p q U
      (unrestrictedIntegralTensorSection l E W n _ U 1 x)
      (unrestrictedIntegralTensorSection l E W n _ U 1 y))
  exact (congrArg ((a.f (p + q)).val.app U) hs).trans
    ((hab p q U x y).trans (congrArg ((b.f (p + q)).val.app U) hs.symm))

/-- The tensor quotient maps and the scalar comparison give the specified strict tower map.
Source: Stacks 03EL, 07A4 and 0941; the pure tensor calculation in
stage3-pur-scalar-tensor-limit-good-representatives.
(blueprint: lem-pur-scalar-tensor-strict-quotient-tower).

Proof: at each level transpose through ordinary scalar extension and test each
homogeneous tensor summand on quotient units. The inverse E tensor identification
sends these units to the tensor of the sections specified by kappa inverse. The
ordinary scalar comparison and the scalar restriction map send its coefficient 1
to 1. Strict sigma separates that unit tensor into the two scalar unit tensors.
The L tensor identification and the two scalar presentation formulas give exactly
the normalized scalarTensorLevel formula. Extensionality gives equality of level
chain maps and then of the strict tower maps, retaining every transition. -/
theorem scalarTensorStrictQuotientTower (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (C D : Complex l E W)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj Q)
    (κSC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj C) ≅
      (unrestrictedIntegralFiniteComplex l L W n).obj
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P))
    (κSD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj D) ≅
      (unrestrictedIntegralFiniteComplex l L W n).obj
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q))
    (hκC : ∀ (n : ℕ) (i : ℤ) (U : W.ProEt) (x : (P.X i).val.obj (op U)),
      ((κSC n).hom.f i).val.app (op U)
        (coefficientEvaluationSection l L W (((scalar l E L ι W).obj C).X i) n (op U)
          (integralComparisonSequenceTensorSection l E L ι W (C.X i) (op (n, U)) 1
            (integralComparisonSequenceSection l E W (C.X i) n (op U)
              (((κC n).inv.f i).val.app (op U)
                (unrestrictedIntegralTensorSection l E W n (P.X i) (op U) 1 x))))) =
      unrestrictedIntegralTensorSection l L W n
        ((integralOrdinaryScalar l E L ι W).obj (P.X i)) (op U) 1
          (integralOrdinaryTensorSection l E L ι W (P.X i) (op U) 1 x))
    (hκD : ∀ (n : ℕ) (i : ℤ) (U : W.ProEt) (x : (Q.X i).val.obj (op U)),
      ((κSD n).hom.f i).val.app (op U)
        (coefficientEvaluationSection l L W (((scalar l E L ι W).obj D).X i) n (op U)
          (integralComparisonSequenceTensorSection l E L ι W (D.X i) (op (n, U)) 1
            (integralComparisonSequenceSection l E W (D.X i) n (op U)
              (((κD n).inv.f i).val.app (op U)
                (unrestrictedIntegralTensorSection l E W n (Q.X i) (op U) 1 x))))) =
      unrestrictedIntegralTensorSection l L W n
        ((integralOrdinaryScalar l E L ι W).obj (Q.X i)) (op U) 1
          (integralOrdinaryTensorSection l E L ι W (Q.X i) (op U) 1 x))
    (qE : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q))
    (hqE : ∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
      (x : (C.X p).val.obj (op (n, U.unop)))
      (y : (D.X r).val.obj (op (n, U.unop))),
      ((qE.hom.app (op n)).f (p + r)).val.app U
        (integralComparisonRestrictedSection l E W
          (((tensor l E W).obj (C, D)).X (p + r)) n U
          (generator l E W C D p r (op (n, U.unop)) x y)) =
      integralTensorGenerator l E W P Q n p r U
        (((κC n).hom.f p).val.app U (coefficientEvaluationSection l E W (C.X p) n U x))
        (((κD n).hom.f r).val.app U (coefficientEvaluationSection l E W (D.X r) n U y)))
    (qL : (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l L W).obj ((scalar l E L ι W).obj C, (scalar l E L ι W).obj D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor l L W).obj
        ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)))
    (hqL : ∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
      (x : (((scalar l E L ι W).obj C).X p).val.obj (op (n, U.unop)))
      (y : (((scalar l E L ι W).obj D).X r).val.obj (op (n, U.unop))),
      ((qL.hom.app (op n)).f (p + r)).val.app U
        (integralComparisonRestrictedSection l L W
          (((tensor l L W).obj ((scalar l E L ι W).obj C,
            (scalar l E L ι W).obj D)).X (p + r)) n U
          (generator l L W _ _ p r (op (n, U.unop)) x y)) =
      integralTensorGenerator l L W _ _ n p r U
        (((κSC n).hom.f p).val.app U (coefficientEvaluationSection l L W _ n U x))
        (((κSD n).hom.f r).val.app U (coefficientEvaluationSection l L W _ n U y)))
    (t : integralOrdinaryScalar l E L ι W ≅ completedOrdinaryScalarExtension l E L ι W)
    (ht : ∀ (N : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U) (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι W N U s x) =
        completedScalarTensorSection l E L ι W N U s x)
    (a : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ⋙ completedOrdinaryScalarComplex l E L ι W ⟶
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).obj
        ((scalar l E L ι W).obj ((tensor l E W).obj (C, D)))).asFunctor)
    (ha : ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
      (x : (((tensor l E W).obj (C, D)).X i).val.obj (op (n, U.unop))),
      ((a.app (op n)).f i).val.app U
        (completedScalarTensorSection l E L ι W
          (((coefficientSequenceRestriction l E W).obj
            (((tensor l E W).obj (C, D)).X i)).obj (op n)) U s
          (integralComparisonRestrictedSection l E W _ n U x)) =
      integralComparisonRestrictedSection l L W _ n U
        (integralComparisonSequenceTensorSection l E L ι W _ (op (n, U.unop))
          ((completedIntegralCommRingProjectionUnrestricted l L W n).hom.app U s) x)) :
    let H := (tensor l E W).obj (C, D)
    let CE := ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj H
    let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
    let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
    Functor.whiskerRight qE.inv
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)) ≫
      Functor.whiskerLeft CE.asFunctor (NatIso.mapHomologicalComplex t (.up ℤ)).hom ≫
      a ≫ τ ≫ qL.hom = (scalarTensorTower l E L ι W).app (P, Q) := by
  dsimp only
  let σ := ((comparisons l).sigma E L ι W).hom.app (C, D)
  let τ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    (((coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)).map σ)
  apply NatTrans.ext
  funext n
  with_unfolding_all
    apply scalar_tensor_level_ext l E L ι W P Q n.unop
  intro p r U x y
  let zC := integralComparisonSequenceSection l E W (C.X p) n.unop U
    (((κC n.unop).inv.f p).val.app U
      (unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x))
  let zD := integralComparisonSequenceSection l E W (D.X r) n.unop U
    (((κD n.unop).inv.f r).val.app U
      (unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y))
  have hzC : ((κC n.unop).hom.f p).val.app U
      (coefficientEvaluationSection l E W (C.X p) n.unop U zC) =
      unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x := by
    apply Eq.trans (congrArg (((κC n.unop).hom.f p).val.app U)
      (evaluation_sequence_section l E W (C.X p) n.unop U _))
    exact congrArg (fun g ↦ (g.f p).val.app U
      (unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x))
        (κC n.unop).inv_hom_id
  have hzD : ((κD n.unop).hom.f r).val.app U
      (coefficientEvaluationSection l E W (D.X r) n.unop U zD) =
      unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y := by
    apply Eq.trans (congrArg (((κD n.unop).hom.f r).val.app U)
      (evaluation_sequence_section l E W (D.X r) n.unop U _))
    exact congrArg (fun g ↦ (g.f r).val.app U
      (unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y))
        (κD n.unop).inv_hom_id
  let w := integralComparisonRestrictedSection l E W
    (((tensor l E W).obj (C, D)).X (p + r)) n.unop U
      (generator l E W C D p r (op (n.unop, U.unop)) zC zD)
  have hqEw : ((qE.hom.app n).f (p + r)).val.app U w =
      integralTensorGenerator l E W P Q n.unop p r U
        (unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y) := by
    exact (hqE n.unop p r U zC zD).trans
      (congrArg₂ (integralTensorGenerator l E W P Q n.unop p r U) hzC hzD)
  have hinv : ((qE.inv.app n).f (p + r)).val.app U
      (integralTensorGenerator l E W P Q n.unop p r U
        (unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y)) = w := by
    have hi := congrArg (fun g ↦ ((g.app n).f (p + r)).val.app U w) qE.hom_inv_id
    with_unfolding_all
      exact (congrArg (((qE.inv.app n).f (p + r)).val.app U) hqEw.symm).trans hi
  have hlevel := (scalarTensorTower_existsUnique l E L ι W).exists.choose_spec P Q n.unop
  have hnorm := (scalarTensorLevel_existsUnique l E L ι W n.unop).exists.choose_spec
    P Q p r U x y
  with_unfolding_all
    change ((qL.hom.app n).f (p + r)).val.app U
      (((τ.app n).f (p + r)).val.app U
        (((a.app n).f (p + r)).val.app U
          ((t.hom.app _).val.app U
            (((integralOrdinaryScalar l E L ι W).map ((qE.inv.app n).f (p + r))).val.app U
              (integralOrdinaryTensorSection l E L ι W _ U 1
                (integralTensorGenerator l E W P Q n.unop p r U
                  (unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x)
                  (unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y))))))) = _
  rw [scalar_map_tensor]
  erw [hinv, ht]
  erw [ha n.unop (p + r) U 1
    (generator l E W C D p r (op (n.unop, U.unop)) zC zD)]
  simp only [map_one]
  change ((qL.hom.app n).f (p + r)).val.app U
    (((((coefficientSequenceRestriction l L W).map (σ.f (p + r))).app n).val.app U)
      (integralComparisonRestrictedSection l L W _ n.unop U
        (integralComparisonSequenceTensorSection l E L ι W _ (op (n.unop, U.unop)) 1
          (generator l E W C D p r (op (n.unop, U.unop)) zC zD)))) = _
  erw [OrdinaryTowerProof.restriction_map_section]
  have hs := (comparisons l).sigma_formula E L ι W C D p r
    (op (n.unop, U.unop)) 1 zC zD
  change ((qL.hom.app n).f (p + r)).val.app U
    (integralComparisonRestrictedSection l L W _ n.unop U
      ((σ.f (p + r)).val.app (op (n.unop, U.unop))
        (integralComparisonSequenceTensorSection l E L ι W _ (op (n.unop, U.unop)) 1
          (generator l E W C D p r (op (n.unop, U.unop)) zC zD)))) = _
  rw [hs]
  rw [hqL]
  have hhC := hκC n.unop p U.unop x
  have hhD := hκD n.unop r U.unop y
  change ((κSC n.unop).hom.f p).val.app U
    (coefficientEvaluationSection l L W _ n.unop U
      (integralComparisonSequenceTensorSection l E L ι W _
        (op (n.unop, U.unop)) 1 zC)) = _ at hhC
  change ((κSD n.unop).hom.f r).val.app U
    (coefficientEvaluationSection l L W _ n.unop U
      (integralComparisonSequenceTensorSection l E L ι W _
        (op (n.unop, U.unop)) 1 zD)) = _ at hhD
  rw [hhC, hhD]
  with_unfolding_all
    have hlevel' : ((scalarTensorTower l E L ι W).app (P, Q)).app n =
        (scalarTensorLevel l E L ι W n.unop).app (P, Q) := hlevel
    have htower := congrArg (fun g :
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsTensorLevel l E W n.unop).obj (P, Q)) ⟶
        (integralOperationsTensorLevel l L W n.unop).obj
          ((((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P),
            (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)) ↦
        (g.f (p + r)).val.app U
      (integralOrdinaryTensorSection l E L ι W _ U 1
        (integralTensorGenerator l E W P Q n.unop p r U
          (unrestrictedIntegralTensorSection l E W n.unop (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E W n.unop (Q.X r) U 1 y)))) hlevel'
    with_unfolding_all exact hnorm.symm.trans htower.symm

end WeilConjectures.ScalarExtensionTower
