/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels

/-! # Ordinary reconstruction of a coherent strict quotient system

Source: Stacks 03D7, 06YY and 0941.
(blueprint: lem-trf-coherent-quotient-ordinary-lift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem sheaf_eqToHom_apply
    {B : Type*} [Category B] {J : GrothendieckTopology B} {R : Sheaf J RingCat}
    {M N : SheafOfModules R} (h : M = N) (V : Bᵒᵖ) (x : M.val.obj V) :
    (eqToHom h).val.app V x =
      cast (congrArg (fun T : SheafOfModules R ↦ ↥(T.val.obj V)) h) x := by
  cases h
  rfl

private theorem restrictionEvaluation_apply (W : Scheme.{t})
    (C : coefficientSequenceModules l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : C.val.obj (op (n, V.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app C).val.app V)
      (integralComparisonRestrictedSection l E W C n V x) = x := by
  dsimp only [eqToIso, Iso.app_hom]
  erw [eqToHom_app, sheaf_eqToHom_apply]
  unfold integralComparisonRestrictedSection
  simp only [cast_cast, cast_eq]

private theorem scalarUnit_tensor (W : Scheme.{t})
    (A : scalarReductionSource l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : A.val.obj V) :
    ((scalarReductionExtension_adjunction l E W n).choose.unit.app A).val.app V x =
      unrestrictedIntegralTensorSection l E W n A V 1 x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec A V x
  dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
    unrestrictedIntegralReductionExistence, scalarReductionExistence] at h ⊢
  exact h

private theorem ordinaryUnit_projection (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W)
    (A : scalarReductionSource l E W) (n : ℕ) :
    M.adjunction.unit.app A ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj A)) (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
        (M.tensor.obj A) ≫
      (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app A) =
        (scalarReductionExtension_adjunction l E W n).choose.unit.app A := by
  ext V x
  exact (M.unit_tensor A n V x).trans
    (scalarUnit_tensor l E W A n V x).symm

private theorem sequenceSection_eq (W : Scheme.{t})
    (B : coefficientSequenceModules l E W) (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj B).val.obj V) :
    integralComparisonSequenceSection l E W B n V x = x := by
  unfold integralComparisonSequenceSection
  rfl

private theorem adjunction_iso_unit_unique
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (ad : F ⊣ G) {X : A} {Y : B} (q : Y ≅ F.obj X)
    (u : X ⟶ G.obj Y) (v : Y ⟶ F.obj X)
    (hq : u ≫ G.map q.hom = ad.unit.app X)
    (hv : u ≫ G.map v = ad.unit.app X) : v = q.hom := by
  have h : q.inv ≫ v = 𝟙 _ := by
    apply (ad.homEquiv X _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_id, ← hq]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]
    exact hv.trans hq.symm
  simpa only [← Category.assoc, q.hom_inv_id, Category.id_comp, Category.comp_id]
    using congrArg (fun g ↦ q.hom ≫ g) h

private theorem sheaf_iso_inv_hom_apply
    {B : Type*} [Category B] {J : GrothendieckTopology B} {R : Sheaf J RingCat}
    {M N : SheafOfModules R} (k : M ≅ N) (V : Bᵒᵖ) (x : N.val.obj V) :
    k.hom.val.app V (k.inv.val.app V x) = x := by
  exact congrArg (fun g ↦ g.val.app V x) k.inv_hom_id

private theorem sheaf_restrict_iso_cancel
    {B : Type*} [Category B] {J : GrothendieckTopology B}
    {R T : Sheaf J RingCat} (α : R ⟶ T)
    {A A' : SheafOfModules R} {N K : SheafOfModules T}
    (f : A ⟶ A') (g : A' ⟶ (SheafOfModules.restrictScalars α).obj N)
    (k : N ≅ K) (u : A ⟶ (SheafOfModules.restrictScalars α).obj K)
    (h : ∀ (V : Bᵒᵖ) (x : A.val.obj V),
      g.val.app V (f.val.app V x) = k.inv.val.app V (u.val.app V x)) :
    f ≫ g ≫ (SheafOfModules.restrictScalars α).map k.hom = u := by
  ext V x
  calc
    _ = k.hom.val.app V (g.val.app V (f.val.app V x)) := rfl
    _ = k.hom.val.app V (k.inv.val.app V (u.val.app V x)) :=
      congrArg (fun y ↦ k.hom.val.app V y) (h V x)
    _ = u.val.app V x := sheaf_iso_inv_hom_apply k V _

private theorem sectionUnit (W : Scheme.{t}) (n : ℕ)
    (A : scalarReductionSource l E W) (B : coefficientSequenceModules l E W)
    (k : (coefficientSequenceEvaluation l E W n).obj B ≅
      (scalarReductionExtension l E W n).obj A)
    (b : A ⟶ ((coefficientSequenceRestriction l E W).obj B).obj (op n))
    (hb : ∀ (V : W.ProEtᵒᵖ) (x : A.val.obj V),
      b.val.app V x = integralComparisonRestrictedSection l E W B n V
        (integralComparisonSequenceSection l E W B n V
          (k.inv.val.app V (unrestrictedIntegralTensorSection l E W n A V 1 x)))) :
    b ≫ (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app B ≫
      (scalarReductionRestriction l E W n).map k.hom =
        (scalarReductionExtension_adjunction l E W n).choose.unit.app A := by
  refine sheaf_restrict_iso_cancel
    ((sheafCompose (Scheme.ProEt.topology W) (forget₂ CommRingCat RingCat)).map
      (completedIntegralCommRingProjectionUnrestricted l E W n)) b
    ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app B) k
    ((scalarReductionExtension_adjunction l E W n).choose.unit.app A) ?_
  intro V x
  have hcast := restrictionEvaluation_apply l E W B n V
    (integralComparisonSequenceSection l E W B n V
      (k.inv.val.app V (unrestrictedIntegralTensorSection l E W n A V 1 x)))
  have hs := sequenceSection_eq l E W B n V
    (k.inv.val.app V (unrestrictedIntegralTensorSection l E W n A V 1 x))
  have hb' := congrArg
    (fun y ↦
      ((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app B).val.app V y)
    (hb V x)
  have hu := scalarUnit_tensor l E W A n V x
  dsimp only [scalarReductionRestriction, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, ModuleCat.restrictScalars, Functor.comp_obj] at hu
  have hi := congrArg
    (fun y : ((scalarReductionExtension l E W n).obj A).val.obj V ↦
      k.inv.val.app V y) hu.symm
  dsimp only [scalarReductionRestriction, SheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalars, ModuleCat.restrictScalars, Functor.comp_obj]
      at hb' hcast hs ⊢
  exact hb'.trans (hcast.trans (hs.trans hi))

private theorem ordinaryFiniteComparison (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W) (n : ℕ)
    (A : scalarReductionSource l E W) (B : coefficientSequenceModules l E W)
    (k : (coefficientSequenceEvaluation l E W n).obj B ≅
      (scalarReductionExtension l E W n).obj A)
    (b : A ⟶ ((coefficientSequenceRestriction l E W).obj B).obj (op n))
    (ai : M.tensor.obj A ⟶ B)
    (hπ : (M.adjunction.unit.app A ≫
        (CompletionUnit.ordinaryLimit l E W).map ai) ≫
      limit.π ((coefficientSequenceRestriction l E W).obj B) (op n) = b)
    (hb : ∀ (V : W.ProEtᵒᵖ) (x : A.val.obj V),
      b.val.app V x = integralComparisonRestrictedSection l E W B n V
        (integralComparisonSequenceSection l E W B n V
          (k.inv.val.app V (unrestrictedIntegralTensorSection l E W n A V 1 x)))) :
    (coefficientSequenceEvaluation l E W n).map ai ≫ k.hom =
      (M.evaluation n).hom.app A := by
  let v := (coefficientSequenceEvaluation l E W n).map ai ≫ k.hom
  let q := (M.evaluation n).app A
  let r := scalarReductionRestriction l E W n
  let e := eqToIso (coefficientSequenceRestriction_evaluation l E W n)
  let ad := (scalarReductionExtension_adjunction l E W n).choose
  have hunit : M.adjunction.unit.app A ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj A)) (op n) ≫
      e.hom.app (M.tensor.obj A) ≫ r.map v = ad.unit.app A := by
    have hp := limMap_π ((coefficientSequenceRestriction l E W).map ai) (op n)
    calc
      _ = M.adjunction.unit.app A ≫
          limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj A)) (op n) ≫
          ((coefficientSequenceRestriction l E W).map ai).app (op n) ≫
          e.hom.app B ≫ r.map k.hom := by
        dsimp only [v]
        rewrite [CategoryTheory.Functor.map_comp]
        have he := e.hom.naturality ai
        simpa only [Category.assoc, Functor.comp_map, evaluation_obj_map, r] using congrArg
          (fun g ↦ M.adjunction.unit.app A ≫
            limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj A)) (op n) ≫
            g ≫ r.map k.hom) he.symm
      _ = (M.adjunction.unit.app A ≫
          (CompletionUnit.ordinaryLimit l E W).map ai) ≫
          limit.π ((coefficientSequenceRestriction l E W).obj B) (op n) ≫
          e.hom.app B ≫ r.map k.hom := by
        change _ = (M.adjunction.unit.app A ≫
          limMap ((coefficientSequenceRestriction l E W).map ai)) ≫ _
        simpa only [Category.assoc] using congrArg
          (fun g ↦ M.adjunction.unit.app A ≫ g ≫ e.hom.app B ≫ r.map k.hom) hp.symm
      _ = b ≫ e.hom.app B ≫ r.map k.hom := by
        rw [← Category.assoc, hπ]
      _ = ad.unit.app A := ?_
    exact sectionUnit l E W n A B k b hb
  exact adjunction_iso_unit_unique ad q
    (M.adjunction.unit.app A ≫
      limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj A)) (op n) ≫
      e.hom.app (M.tensor.obj A)) v
    (ordinaryUnit_projection l E W M A n) hunit

private theorem ordinaryLift (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (CompletionUnit.tower l E W).obj C)
    (hb : ∀ (n : ℕ) (i : ℤ) (V : W.ProEtᵒᵖ) (x : (P.X i).val.obj V),
      (((b.f i).app (op n)).val.app V) x =
        integralComparisonRestrictedSection l E W (C.X i) n V
          (integralComparisonSequenceSection l E W (C.X i) n V
            (((κ n).inv.f i).val.app V
              (unrestrictedIntegralTensorSection l E W n (P.X i) V 1 x)))) :
    ∃ a : (M.quotient l E W).obj P ⟶ C,
      ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C) a =
        ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).mapHomologicalComplex
          (.up ℤ)).homEquiv P ((CompletionUnit.tower l E W).obj C) b ∧
      ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a ≫
          (κ n).hom =
            (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app P := by
  let a₀ := (M.adjunction.mapHomologicalComplex (.up ℤ))
  let c₀ := (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W))
  let f := (c₀.mapHomologicalComplex (.up ℤ)).homEquiv P
    ((CompletionUnit.tower l E W).obj C) b
  let a := (a₀.homEquiv P C).symm f
  have ha : a₀.homEquiv P C a = f := (a₀.homEquiv P C).apply_symm_apply f
  refine ⟨a, ha, ?_⟩
  intro n
  ext i : 1
  apply ordinaryFiniteComparison l E W M n (P.X i) (C.X i)
    (HomologicalComplex.Hom.isoApp (κ n) i) ((b.f i).app (op n)) (a.f i)
  · have h := ((c₀.mapHomologicalComplex (.up ℤ)).homEquiv P
      ((CompletionUnit.tower l E W).obj C)).symm_apply_apply b
    rw [Adjunction.homEquiv_counit] at h
    have hπ := congrArg (fun g ↦ (g.f i).app (op n)) h
    have htranspose : M.adjunction.unit.app (P.X i) ≫
        (CompletionUnit.ordinaryLimit l E W).map (a.f i) = f.f i :=
      congrArg (fun g ↦ g.f i) ha
    rw [htranspose]
    exact hπ
  · exact hb n i

private theorem isIso_of_evaluations (W : Scheme.{t})
    {P C : CochainComplex (coefficientSequenceModules l E W) ℤ} (a : P ⟶ C)
    (ha : ∀ n : ℕ,
      IsIso (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)) :
    IsIso a := by
  have hi (i : ℤ) : IsIso (a.f i) := by
    have hc (V : (ℕ × W.ProEt)ᵒᵖ) : IsIso ((a.f i).val.app V) := by
      let n := V.unop.1
      let U := V.unop.2
      let := ha n
      have : IsIso ((coefficientSequenceEvaluation l E W n).map (a.f i)) :=
        inferInstanceAs (IsIso ((HomologicalComplex.eval _ (.up ℤ) i).map
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a)))
      have h : IsIso
          (((coefficientSequenceEvaluation l E W n).map (a.f i)).val.app (op U)) :=
        inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op U)).map
          ((coefficientSequenceEvaluation l E W n).map (a.f i))))
      rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
      exact h
    let e : (P.X i).val ≅ (C.X i).val :=
      PresheafOfModules.isoMk (fun V ↦ @asIso _ _ _ _ ((a.f i).val.app V) (hc V))
        (by intro X Y f; exact (a.f i).val.naturality f)
    have : IsIso ((SheafOfModules.forget _).map (a.f i)) := e.isIso_hom
    exact isIso_of_reflects_iso (a.f i) (SheafOfModules.forget _)
  let := hi
  exact HomologicalComplex.Hom.isIso_of_components a

/-- A strict unit-tower map determines its ordinary quotient isomorphism.
Source: Stacks 03D7 (ordinary adjunction) and 0941 (strict tower limits).
(blueprint: lem-trf-coherent-quotient-ordinary-lift).

Proof: transpose b through the constant/limit adjunction and inversely through
M's termwise tensor/limit adjunction. At every degree and level, the prescribed
values on 1 tensor x and M.unit_tensor identify the two scalar adjuncts. The
finite scalar Hom bijection identifies the evaluated map followed by κ with
M.evaluation. Each evaluation is therefore invertible. Sectionwise bijectivity
on the product site detects an isomorphism of module sheaves degree by degree,
and hence an isomorphism of strict complexes. This uses no derived evaluation
faithfulness and applies to zero objects and level zero without exceptions. -/
theorem coherentQuotientOrdinaryLift (W : Scheme.{t})
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (CompletionUnit.tower l E W).obj C)
    (hb : ∀ (n : ℕ) (i : ℤ) (V : W.ProEtᵒᵖ) (x : (P.X i).val.obj V),
      (((b.f i).app (op n)).val.app V) x =
        integralComparisonRestrictedSection l E W (C.X i) n V
          (integralComparisonSequenceSection l E W (C.X i) n V
            (((κ n).inv.f i).val.app V
              (unrestrictedIntegralTensorSection l E W n (P.X i) V 1 x)))) :
    ∃ a : (M.quotient l E W).obj P ≅ C,
      ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv P C) a.hom =
        ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E W)).mapHomologicalComplex
          (.up ℤ)).homEquiv P ((CompletionUnit.tower l E W).obj C) b ∧
      ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          (κ n) =
            (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P := by
  obtain ⟨a, ha, hκ⟩ := ordinaryLift l E W M P C κ b hb
  have hiso (n : ℕ) : IsIso
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a) := by
    have : IsIso
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map a ≫
          (κ n).hom) := by
      rw [hκ n]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (κ n).hom
  have := isIso_of_evaluations l E W a hiso
  refine ⟨asIso a, ha, ?_⟩
  intro n
  apply Iso.ext
  exact hκ n

end WeilConjectures
