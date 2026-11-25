/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodQuotientTransition.PodQuotientTransitionGenerators
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.PoincareDuality.Pod.Identity.PodIdentityRestrictedTower
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismRoosUnitCancellation

/-! # Reindexing reduction on strict quotient models

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindex-reduction-quotient-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor
  roosF roosConeFunctor podRestrictedTower
  podOrdinaryReindex
  completedIntegralCommRingSheafUnrestricted CategoryTheory.sheafCompose
  isoSectionwiseModuleInverseImage integralComparisonSequencePullback
  integralComparisonSequenceDirectImage integralComparisonDerivedSequencePullback
  CochainComplex.mappingCocone integralOperationsTowerStep
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor
attribute [local irreducible] constantSheaf SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_roos_unique (W : Scheme.{u})
    (ρ ρ' : IntegralComparisonRoosModel l E W) : ρ = ρ' := by
  suffices h : ρ.comparison = ρ'.comparison by
    cases ρ
    cases ρ'
    cases h
    rfl
  apply Iso.ext_inv
  apply NatTrans.ext
  funext C
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso q := hq
  have : IsIso ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q) := by
    change IsIso ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q))
    infer_instance
  have hi : ρ.comparison.app I = ρ'.comparison.app I := by
    apply Iso.ext
    exact (ρ.computes I).trans (ρ'.computes I).symm
  apply (cancel_mono ((DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W).map q)).1
  rw [← ρ.comparison.inv.naturality q, ← ρ'.comparison.inv.naturality q]
  exact congrArg (fun z ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q).map q ≫ z) (congrArg Iso.inv hi)

private theorem systemUnit_roos (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (N : CompletionUnit.DerivedModel l E W S M)
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    N.systemUnit.app C ≫ (podLimitRoos l E ρ C).hom =
      DerivedCategory.Q.map (M.limitComparison.hom.app C ≫
        roosι ((CompletionUnit.tower l E W).obj C)) := by
  rw [normalized_roos_unique l E W ρ (roosModel l E W S M N)]
  rw [N.systemUnit_composition]
  simp only [podLimitRoos, Iso.trans_hom, Functor.mapIso_hom, Iso.app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [roosModel, comparisonFromModel, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, NatIso.ofComponents_hom_app, Iso.refl_hom]
  change DerivedCategory.Q.map (M.limitComparison.hom.app C) ≫
    N.limitUnit.app _ ≫ N.roos.inv.app _ ≫ 𝟙 _ = _
  rw [Category.comp_id, ← N.roos_normalization]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem reduction_unit_roos (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (N : CompletionUnit.DerivedModel l E W S M)
    (ρ : IntegralComparisonRoosModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    S.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (coefficientSequenceLimit l E W).map (N.reductionComparison.app P) ≫
        (podLimitRoos l E ρ ((M.quotient l E W).obj P)).hom =
      DerivedCategory.Q.map (M.coneAugmentation l E W P) := by
  have h := N.hom_normalization P ((M.quotient l E W).obj P) (𝟙 _)
  simp only [Adjunction.homEquiv_unit] at h
  erw [(DerivedCategory.Q (C := coefficientSequenceModules l E W)).map_id,
    ((CompletionUnit.ordinaryLimit l E W).mapHomologicalComplex (.up ℤ)).map_id,
    Category.comp_id, Category.comp_id] at h
  erw [← Category.assoc, h, Category.assoc, systemUnit_roos l E W S M N ρ]
  simp only [CompletionUnit.OrdinaryModel.coneAugmentation,
    CompletionUnit.OrdinaryModel.augmentation, CompletionUnit.OrdinaryModel.transpose,
    Adjunction.homEquiv_id, Functor.map_comp, Category.assoc]

-- The section calculation compares the two finite scalar-transport presentations.
private theorem augmentation_section (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    ((M.augmentation l E W P ≫ limit.π
        ((CompletionUnit.tower l E W).obj ((M.quotient l E W).obj P)).asFunctor
        (op n)).f i).val.app U x =
      integralComparisonRestrictedSection l E W (M.tensor.obj (P.X i)) n U
        (PodQuotientTransition.unitSection l E W M (P.X i) n U x) := by
  have hu : (M.augmentation l E W P).f i =
      M.adjunction.unit.app (P.X i) ≫
        (M.limitComparison.hom.app ((M.quotient l E W).obj P)).f i := by
    dsimp only [CompletionUnit.OrdinaryModel.augmentation,
      CompletionUnit.OrdinaryModel.transpose]
    rw [Adjunction.homEquiv_unit]
    erw [((CompletionUnit.ordinaryLimit l E W).mapHomologicalComplex (.up ℤ)).map_id]
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Adjunction.mapHomologicalComplex_unit_app_f]
    erw [Category.comp_id]
  have hp := M.limitComparison_projection ((M.quotient l E W).obj P) n i
  rw [HomologicalComplex.comp_f] at hp
  have hproj : (M.augmentation l E W P ≫ limit.π
      ((CompletionUnit.tower l E W).obj ((M.quotient l E W).obj P)).asFunctor
      (op n)).f i = M.adjunction.unit.app (P.X i) ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj (P.X i)))
          (op n) := by
    rw [HomologicalComplex.comp_f, hu, Category.assoc, hp]
    rfl
  rw [hproj]
  let T := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).app
      (M.tensor.obj (P.X i)) ≪≫
    (scalarReductionRestriction l E W n).mapIso ((M.evaluation n).app (P.X i))
  have hinj : Function.Injective (fun z ↦ T.hom.val.app U z) := by
    intro y z h
    have hi (w) : T.inv.val.app U (T.hom.val.app U w) = w :=
      congrArg (fun k ↦ k.val.app U w) T.hom_inv_id
    exact (hi y).symm.trans ((congrArg (fun w ↦ T.inv.val.app U w) h).trans (hi z))
  apply hinj
  have hunit := M.unit_tensor (P.X i) n U x
  change T.hom.val.app U _ = _ at hunit
  refine hunit.trans ?_
  dsimp only [T, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    PodQuotientTransition.unitSection]
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    restricted_section_cancel l E W (M.tensor.obj (P.X i)) n U]
  exact (congrArg (fun f ↦ f.val.app U
    (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))
      ((M.evaluation n).app (P.X i)).inv_hom_id).symm

-- Elaborating sectionwise pullback and tensor generators requires the full tower data.
private theorem augmentation_reindex
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hD : PodCompletionReindex.RestrictedGenerators l E g D)
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X)
    (β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
      isoReductionIntegralInverse l E g ⋙ MX.tensor)
    (hβ : PodQuotientTransition.ReindexNormalized l E g MY MX β)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    let C := (MY.quotient l E Y).obj P
    let b := (NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P
    let a := (D.restricted C).hom ≫
      HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map b)
    (isoReductionIntegralComplex l E g).map (MY.augmentation l E Y P ≫
        limit.π ((CompletionUnit.tower l E Y).obj C).asFunctor (op n)) ≫
        a.app (op n) =
      MX.augmentation l E X ((isoReductionIntegralComplex l E g).obj P) ≫
        limit.π ((CompletionUnit.tower l E X).obj
          ((MX.quotient l E X).obj ((isoReductionIntegralComplex l E g).obj P))).asFunctor
          (op n) := by
  dsimp only
  ext i U x
  change ((P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop))) at x
  change (((coefficientSequenceRestriction l E X).map (β.hom.app (P.X i))).app
      (op n)).val.app U
      (((((D.restricted ((MY.quotient l E Y).obj P)).hom.app (op n)).f i).val.app U
        (((MY.augmentation l E Y P ≫ limit.π
          ((CompletionUnit.tower l E Y).obj ((MY.quotient l E Y).obj P)).asFunctor
          (op n)).f i).val.app (op ((proEtaleIsoPostcompose g).obj U.unop)) x))) = _
  rw [augmentation_section l E Y MY P n i]
  erw [hD ((MY.quotient l E Y).obj P) n i U.unop]
  erw [restriction_map_section l E X (β.hom.app (P.X i)) n U]
  erw [hβ (P.X i) n U.unop x]
  exact (augmentation_section l E X MX
    ((isoReductionIntegralComplex l E g).obj P) n i U x).symm

private theorem augmentation_fst (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
    let C := podRestrictedTower l E ((M.quotient l E W).obj P)
    M.coneAugmentation l E W P ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary C) ≫ Pi.π (fun k : ℕ ↦ C.obj (op k)) n =
      M.augmentation l E W P ≫ limit.π C (op n) := by
  dsimp only [CompletionUnit.OrdinaryModel.coneAugmentation]
  rw [Category.assoc]
  congr 1
  exact roosι_eval _ n

private theorem augmentation_snd (W : Scheme.{u})
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (p : ℤ) :
    (M.coneAugmentation l E W P).f (p + 1) ≫
      (CochainComplex.mappingCocone.snd
        (podRoosBoundary (podRestrictedTower l E ((M.quotient l E W).obj P)))).v
        (p + 1) p (by omega) = 0 := by
  dsimp only [CompletionUnit.OrdinaryModel.coneAugmentation]
  rw [HomologicalComplex.comp_f, Category.assoc]
  have h : (roosι ((CompletionUnit.tower l E W).obj
      ((M.quotient l E W).obj P))).f (p + 1) ≫
      (CochainComplex.mappingCocone.snd (roosU ((CompletionUnit.tower l E W).obj
        ((M.quotient l E W).obj P)))).v (p + 1) p (by omega) = 0 := by
    simp [roosι, roosLift]
  erw [h, comp_zero]

-- Compare the complete product cone, including its shifted coordinate.
private theorem augmentation_roos_reindex
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hf : PodCompletionReindex.RoosFst l E g D)
    (hs : PodCompletionReindex.RoosSnd l E g D)
    (hr : PodCompletionReindex.RestrictedGenerators l E g D)
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X)
    (β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
      isoReductionIntegralInverse l E g ⋙ MX.tensor)
    (hβ : PodQuotientTransition.ReindexNormalized l E g MY MX β)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    let C := (MY.quotient l E Y).obj P
    let b := (NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P
    let a := (D.restricted C).hom ≫
      HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map b)
    (isoReductionIntegralComplex l E g).map (MY.coneAugmentation l E Y P) ≫
        (D.roos (podRestrictedTower l E C)).hom ≫ integralOperationsRoosFunctor.map a =
      MX.coneAugmentation l E X ((isoReductionIntegralComplex l E g).obj P) := by
  dsimp only
  let F := isoReductionIntegralInverse l E g
  let G := isoReductionIntegralComplex l E g
  let C := (MY.quotient l E Y).obj P
  let CY := podRestrictedTower l E C
  let PX := G.obj P
  let CX := podRestrictedTower l E ((MX.quotient l E X).obj PX)
  let b := (NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P
  let a : (podReindexTower l E g).obj CY ⟶ CX := (D.restricted C).hom ≫
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map b)
  change G.map (MY.coneAugmentation l E Y P) ≫ (D.roos CY).hom ≫
    integralOperationsRoosFunctor.map a = MX.coneAugmentation l E X PX
  apply cone_hom_ext (podRoosBoundary CX)
  · rw [Category.assoc, Category.assoc, roos_map_fst a,
      ← Category.assoc (D.roos CY).hom, hf CY]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc, podReindexProduct]
    rw [← G.map_comp_assoc, ← G.map_comp_assoc]
    simp only [Category.assoc]
    rw [augmentation_fst l E Y MY P n, augmentation_fst l E X MX PX n]
    exact augmentation_reindex l E g D hr MY MX β hβ P n
  · intro p
    rw [← Category.assoc]
    apply roos_map_shift_zero a (G.map (MY.coneAugmentation l E Y P) ≫
      (D.roos CY).hom)
    intro q
    apply image_shift_zero F (podRoosBoundary CY)
      (podRoosBoundary ((podReindexTower l E g).obj CY))
      (MY.coneAugmentation l E Y P) (D.roos CY).hom q
      ((podReindexProduct l E g CY).f q)
    · have hgen (i j : ℤ) (hij : i - 1 = j) :
          (D.roos CY).hom.f i ≫
              (CochainComplex.mappingCocone.snd
                (podRoosBoundary ((podReindexTower l E g).obj CY))).v
                  i j (by omega) =
            F.map ((CochainComplex.mappingCocone.snd (podRoosBoundary CY)).v
              i j (by omega)) ≫ (podReindexProduct l E g CY).f j := by
        subst j
        exact hs CY i
      exact hgen (q + 1) q (by omega)
    · exact augmentation_snd l E Y MY P q
  · exact augmentation_snd l E X MX PX

private theorem limitRoos_naturality (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W)
    {C C' : CochainComplex (coefficientSequenceModules l E W) ℤ} (f : C ⟶ C') :
    (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map f) ≫
        (podLimitRoos l E ρ C').hom =
      (podLimitRoos l E ρ C).hom ≫ DerivedCategory.Q.map
        (integralOperationsRoosFunctor.map
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map f))) := by
  dsimp only [podLimitRoos, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  have h := (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at h
  change (coefficientConstantTowerLimit l E W).map
    ((coefficientSequenceRestriction l E W).mapDerivedCategory.map
      (DerivedCategory.Q.map f)) ≫ _ = _
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc]
  rw [Category.assoc]
  congr 1
  exact ρ.comparison.hom.naturality
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map f)

private theorem transpose_reindex
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {RY : A ⥤ B} {LY : B ⥤ A} {RX : C ⥤ D} {LX : D ⥤ C}
    (adjY : RY ⊣ LY) (adjX : RX ⊣ LX) (F : A ⥤ C) (G : B ⥤ D)
    (α : RY ⋙ G ≅ F ⋙ RX) (δ : LY ⋙ F ≅ G ⋙ LX)
    (hu : ∀ K, F.map (adjY.unit.app K) ≫ δ.hom.app (RY.obj K) ≫
      LX.map (α.hom.app K) = adjX.unit.app (F.obj K))
    {K : A} {Z : B} (a : RY.obj K ⟶ Z) {T : D} (b : G.obj Z ⟶ T) :
    adjX.unit.app (F.obj K) ≫ LX.map (α.inv.app K ≫ G.map a ≫ b) =
      F.map (adjY.unit.app K ≫ LY.map a) ≫ δ.hom.app Z ≫ LX.map b := by
  rw [← hu K]
  simp only [Functor.map_comp, Category.assoc]
  rw [← LX.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have hn := δ.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

/-- The normalized reindexing reduction map is its ordinary quotient comparison.
Source: Stacks 03EL, 06YY, 0941; blueprint dual-Tate compatibility Steps 1 and 5.
(blueprint: lem-pod-reindex-reduction-quotient-normalization).

Proof: apply the target reduction/total-limit adjunction to both arrows. The unit
law for D identifies the transpose of D.reduction inverse with the reindexing of
the source reduction unit followed by D.limit. The Hom normalization of DY and DX
expresses their transposes as ordinary quotient units followed by the canonical
right-derived limit unit. The generator normalization of beta identifies the
ordinary quotient-unit maps after reindexing. Its compatibility with the genuine
horizontal quotient maps follows because beta is a map of whole sequence modules.
D.RestrictedGenerators fixes its restriction comparison to this same map, and
D.LimitModel identifies D.limit with its two-coordinate Roos realization. Naturality
of the canonical limit unit now equates the transposes. Injectivity of the adjunction
Hom equivalence gives the displayed equality. This is a single-coefficient assertion;
no scalar extension or coefficient-transition datum appears. Zero complexes, empty
sites and the identity isomorphism require no additional assumption. -/
theorem podReindexReduction_quotient_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X)
    (DY : CompletionUnit.DerivedModel l E Y (podReindexCalculus l E Y) MY)
    (DX : CompletionUnit.DerivedModel l E X (podReindexCalculus l E X) MX)
    (β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
      isoReductionIntegralInverse l E g ⋙ MX.tensor)
    (hβ : PodQuotientTransition.ReindexNormalized l E g MY MX β)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (podReindexCalculus l E X).reduction.map
        ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj) ≫
      DX.reductionComparison.app ((isoReductionIntegralComplex l E g).obj P.obj) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).inv.app P.obj) =
    D.reduction.inv.app (DerivedCategory.Q.obj P.obj) ≫
      (integralComparisonDerivedSequencePullback l E g).map
        (DY.reductionComparison.app P.obj) ≫
      (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app
        ((MY.quotient l E Y).obj P.obj) := by
  let F := podOrdinaryReindex l E g
  let A := isoReductionIntegralInverse l E g
  let G := integralComparisonDerivedSequencePullback l E g
  let L := coefficientSequenceLimit l E X
  let C := (MY.quotient l E Y).obj P.obj
  let PX := (isoReductionIntegralComplex l E g).obj P.obj
  let CX := (MX.quotient l E X).obj PX
  let b := (NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P.obj
  let k := A.mapDerivedCategoryFactors.hom.app P.obj
  have hu : PodCompletionReindex.Unit l E g D := hD.2.2.2.1
  have hf : PodCompletionReindex.RoosFst l E g D := hD.2.2.2.2.2.2.2.2.2.2.1
  have hs : PodCompletionReindex.RoosSnd l E g D := hD.2.2.2.2.2.2.2.2.2.2.2.1
  have hr : PodCompletionReindex.RestrictedGenerators l E g D :=
    hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm : PodCompletionReindex.LimitModel l E g D :=
    hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply (cancel_mono (DerivedCategory.Q.map b)).1
  simp only [Category.assoc, b, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [(DerivedCategory.Q (C := coefficientSequenceModules l E X)).map_id,
    Category.comp_id]
  apply ((podReindexCalculus l E X).adjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (podReindexCalculus l E X).adjunction.unit.app (F.obj _) ≫
      L.map ((podReindexCalculus l E X).reduction.map k ≫
        DX.reductionComparison.app PX) =
    (podReindexCalculus l E X).adjunction.unit.app (F.obj _) ≫
      L.map (D.reduction.inv.app _ ≫ G.map (DY.reductionComparison.app P.obj) ≫
        (integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map b)
  rw [transpose_reindex (podReindexCalculus l E Y).adjunction
    (podReindexCalculus l E X).adjunction F G D.reduction D.limit hu]
  apply (cancel_mono (podLimitRoos l E D.targetRoos CX).hom).1
  have hn := (podReindexCalculus l E X).adjunction.unit.naturality k
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  rw [reduction_unit_roos l E X _ MX DX D.targetRoos PX]
  erw [limitRoos_naturality l E X D.targetRoos b]
  erw [← reassoc_of% (hm C)]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  simp only [Category.assoc]
  rw [reduction_unit_roos l E Y _ MY DY D.sourceRoos P.obj]
  erw [A.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  apply congrArg (fun z ↦ k ≫ DerivedCategory.Q.map z)
  simpa only [integralOperationsRoosFunctor.map_comp, Category.assoc] using
    (augmentation_roos_reindex l E g D hf hs hr MY MX β hβ P.obj).symm

end WeilConjectures
