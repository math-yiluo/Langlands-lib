/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealizationNormalization
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationsUnique
import WeilConjectures.TraceFormula.Supporting.AmbientQuotientScalarModelExistence
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoos
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRoosRepresentativeSquareMate
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingStrictTensorTowersGenerators
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Ingredients of the canonical representative square

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-tensor-roos-representative-square).

The normalized pullback field of a lawful reindexing package is the fixed completed
pullback realization. With it, the adjunction calculation of
`PodTensorRoosRepresentativeSquareMate` identifies the coherent limit/tensor comparison
with the canonical completed pullback/tensor comparison. A single strict tower map is
packaged as a tensor reindexing datum, so the strict Roos normalization applies to it.
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

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The normalized pullback field of a lawful completion reindexing package is the fixed
completed pullback realization, by uniqueness of normalized pullback realizations.
Source: blueprint Steps 1 and 5; Stacks 099N(5), 0941
(blueprint: lem-pod-tensor-roos-representative-square). -/
theorem podCompletionReindex_pullback_eq
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D) :
    D.pullback = CompletedQuotient.completedQuotientPullbackRealization l E g := by
  obtain ⟨β⟩ := ambientQuotientScalarModel_exists l E E (AlgHom.id ℚ_[l] E) Y
    (podReindexCalculus l E Y) D.sourceRoos
  let α : IntegralComparisonPullbackModel l E g (podReindexCalculus l E Y) D.targetRoos :=
    ⟨CompletedQuotient.completedQuotientPullbackRealization l E g,
      CompletedQuotient.completedQuotientPullbackRealization_normalized l E g D.targetRoos⟩
  exact (primitiveQuotientRealizations_unique l E E (AlgHom.id ℚ_[l] E) g
    (podReindexCalculus l E Y) D.targetRoos D.sourceRoos α β).1
      ⟨D.pullback, hD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Reindexing the derived functor of an equality of exact functors gives the equality.
Source: Stacks 05RU. -/
theorem podMapDerivedCategoryNatIso_eqToIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    Functor.mapDerivedCategoryNatIso (eqToIso h) = eqToIso (by cases h; rfl) := by
  subst h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

/-- The ordinary-to-completed map, written through the fixed completed pullback model.
Source: blueprint Steps 1 and 5 (blueprint: def-pod-completion-reindex-models). -/
theorem podOrdinaryToCompleted_app_eq
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (K : DerivedCategory (scalarReductionSource l E Y)) :
    (podOrdinaryToCompleted l E g D).app K =
      (podOrdinaryReindex l E g).map ((podReindexCalculus l E Y).adjunction.unit.app K) ≫
        D.limit.hom.app ((podReindexCalculus l E Y).reduction.obj K) ≫
        (coefficientSequenceLimit l E X).map
          ((eqToIso (podReindexing_sequence_pullback_eq l E g)).inv.app
            ((podReindexCalculus l E Y).reduction.obj K)) ≫
        (pullbackTensorIntegralPullbackModel l E g).inv.app K := by
  unfold podOrdinaryToCompleted
  rw [podCompletionReindex_pullback_eq l E g D hD]
  unfold CompletedQuotient.completedQuotientPullbackRealization
  rw [podMapDerivedCategoryNatIso_eqToIso]
  rfl
/-- The coherent limit/tensor comparison, followed by the tensor of the two
ordinary-to-completed maps, is the ordinary-to-completed map of the tensor followed by
the canonical completed pullback/tensor comparison.
Source: blueprint theorem-poincare-duality-frobenius--2, Step 5; Stacks 07A4, 0941
(blueprint: lem-pod-tensor-roos-representative-square). -/
theorem podReindexingLimitTensorComparison_canonical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (M N : sfIntegralConstructibleCategory l E Y) :
    podReindexingLimitTensorComparisonHom l E g D hD M.obj N.obj ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((podOrdinaryToCompleted l E g D).app M.obj)
            ((podOrdinaryToCompleted l E g D).app N.obj)) =
      (podOrdinaryToCompleted l E g D).app
          ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        ((canonicalIntegralPullbackTensor l E g M N).hom).hom := by
  obtain ⟨_, h₂, h₃⟩ := pullbackTensorComparisonCounits l E g M N
  have key := podMate_square (podOrdinaryReindex l E g) (integralDerivedPullback l E g)
    (integralComparisonDerivedSequencePullback l E g) (pullbackTensorSequenceDerived l E g)
    (eqToIso (podReindexing_sequence_pullback_eq l E g))
    (podReindexCalculus l E Y).adjunction (podReindexCalculus l E X).adjunction
    D.limit.hom D.reduction (pullbackTensorIntegralPullbackModel l E g) hD.2.2.2.2.1
    (integralCompletedTensor l E Y) (integralCompletedTensor l E X)
    (podReindexCalculus l E Y).systemClosed.tensor (podReindexCalculus l E X).systemClosed.tensor
    (pullbackTensorIntegralTensorModel l E Y) (pullbackTensorIntegralTensorModel l E X)
    (pullbackTensorSystemComparison l E g) (podOrdinaryToCompleted l E g D).app
    (podOrdinaryToCompleted_app_eq l E g D hD) M.obj N.obj h₂ h₃
    ((podReindexingSystemTensor l E g).hom.app _) (by
      unfold podReindexingSystemTensor
      rfl)
  unfold podReindexingLimitTensorComparisonHom
  refine Eq.trans ?_ (key.trans ?_)
  · dsimp only [podReindexingTensorFrame]
    unfold podReindexingTensorModel
    rfl
  · unfold canonicalIntegralPullbackTensor pullbackTensorReferenceComparison
    rfl
/-- On complete constructible inputs the ordinary-to-completed map is invertible.
Source: blueprint Steps 1 and 5 (blueprint: def-pod-completion-reindex-models). -/
theorem podOrdinaryToCompleted_isIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso ((podOrdinaryToCompleted l E g D).app K.obj) := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let Δ : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ Δ.p := by
    change l ≠ p
    omega
  have hK : IntegralOnSlice.IsComplete l E Y none K.obj :=
    ⟨Δ, hlp, (sfDerivedComplete_iff_legacy l E Y Δ hlp K.obj).mp K.property.1⟩
  have : IsIso ((podReindexCalculus l E Y).adjunction.unit.app K.obj) :=
    hD.2.2.2.2.2.1 K.obj hK
  dsimp only [podOrdinaryToCompleted, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  infer_instance

/-- A strict tensor tower comparison, equal to a prescribed one at one pair of inputs and to
a chosen generator-normalized comparison elsewhere, packaged with the induced constructible
tensor comparison.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-tensor-roos-representative-square). -/
def podTensorReindexAt
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (τ : (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj)) :
    PodCompletedTensorReindex l E g D := by
  classical
  exact
  { constructible := fun M ↦ by
      have := podOrdinaryToCompleted_isIso l E g D hD M
      exact (sfIntegralConstructible l E X).prop_of_iso
        (asIso ((podOrdinaryToCompleted l E g D).app M.obj)).symm
        ((constructibleIntegralPullback l E g).obj M).property
    tower := fun P' Q' ↦ if h : P' = P ∧ Q' = Q then by
        obtain ⟨rfl, rfl⟩ := h
        exact τ
      else (podReindexingStrictTensorTowersGenerators l E g D hD).choose P' Q'
    tensor := fun M N ↦ by
      have := podOrdinaryToCompleted_isIso l E g D hD M
      have := podOrdinaryToCompleted_isIso l E g D hD N
      have hMN := podOrdinaryToCompleted_isIso l E g D hD
        ((constructibleIntegralTensor l E Y).obj (M, N))
      exact @asIso _ _ _ _ ((podOrdinaryToCompleted l E g D).app
          ((integralCompletedTensor l E Y).obj (M.obj, N.obj))) hMN ≪≫
        (sfIntegralConstructible l E X).ι.mapIso (canonicalIntegralPullbackTensor l E g M N) ≪≫
        (integralCompletedTensor l E X).mapIso
          (Iso.prod (asIso ((podOrdinaryToCompleted l E g D).app M.obj)).symm
            (asIso ((podOrdinaryToCompleted l E g D).app N.obj)).symm) }
/-- At the prescribed pair, the packaged tower comparison is the prescribed one.
Source: blueprint lem-pod-tensor-roos-representative-square. -/
theorem podTensorReindexAt_tower
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (τ : (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj)) :
    (podTensorReindexAt l E g D hD P Q τ).tower P Q = τ := by
  unfold podTensorReindexAt
  exact dite_eq_left (And.intro (rfl : P = P) (rfl : Q = Q))

/-- The packaged tower comparison satisfies the generator formula when the prescribed one does.
Source: blueprint lem-pod-tensor-roos-representative-square. -/
theorem podTensorReindexAt_generators
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (τ : (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (n : ℕ) (p q : ℤ) (U : X.ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      ((((τ.hom.app (op n)).f (p + q)).val.app (op U)))
          (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
        integralOperationsTotalTensorSection l E X n
          (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
          p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
            ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
    PodCompletedTensorReindex.Generators l E g D (podTensorReindexAt l E g D hD P Q τ) := by
  classical
  intro P' Q' n p q U x y
  by_cases h : P' = P ∧ Q' = Q
  · obtain ⟨rfl, rfl⟩ := h
    rw [podTensorReindexAt_tower]
    exact hgen n p q U x y
  · have ht : (podTensorReindexAt l E g D hD P Q τ).tower P' Q' =
        (podReindexingStrictTensorTowersGenerators l E g D hD).choose P' Q' := by
      unfold podTensorReindexAt
      exact dite_eq_right h
    rw [ht]
    exact (podReindexingStrictTensorTowersGenerators l E g D hD).choose_spec P' Q' n p q U x y

-- Record the good-representative endpoints before using the tensor comparison.
private def podRepresentativeReindexFactors
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj (((podGoodReindex l E g D).obj P).obj) := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  unfold podOrdinaryReindex podGoodReindex
  exact (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app P.obj

-- Cancel the comparison isomorphisms without expanding the strict Roos morphism.
private lemma podTensorRepresentative_cancel {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {P Q P' Q' : C} {A B Z : D}
    (eP : P ≅ P') (eQ : Q ≅ Q') (e : T.obj (P', Q') ≅ B)
    (k : A ⟶ T.obj (P, Q)) (t : A ⟶ B)
    (h : HEq (k ≫ T.map (Prod.mkHom eP.hom eQ.hom) ≫ e.hom) t)
    (f : T.obj (P, Q) ⟶ Z) :
    t ≫ e.inv ≫ T.map (Prod.mkHom eP.inv eQ.inv) ≫ f = k ≫ f := by
  rw [← eq_of_heq h]
  simp only [Category.assoc, e.hom_inv_id_assoc]
  rw [← T.map_comp_assoc]
  simp only [Prod.mkHom, prod_comp, eP.hom_inv_id, eQ.hom_inv_id,
    ← prod_id', T.map_id, Category.id_comp]

/-- The representative square, assembled from the strict Roos normalization and the
adjunction calculation of the canonical completed comparison.
Source: blueprint lem-pod-tensor-roos-representative-square. -/
theorem podTensorRoosRepresentativeSquare_of_normalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj))
    (τ : (podReindexTower l E g).obj
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
      (integralOperationsTensorTowerFunctor l E X).obj
        (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (n : ℕ) (p q : ℤ) (U : X.ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      ((((τ.hom.app (op n)).f (p + q)).val.app (op U)))
          (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
        integralOperationsTotalTensorSection l E X n
          (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
          p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
            ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
    letI : (isoReductionIntegralInverse l E g).Additive :=
      isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
    letI : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
      isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
    ((podOrdinaryReindex l E g).map
          ((integralCompletedTensorComparison l E Y).hom.app (P,Q)) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
            integralOperationsRoosFunctor.map τ.hom)) ≫
      (integralCompletedTensorComparison l E X).inv.app
        ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app P.obj)
          ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app Q.obj)) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom
          ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
          ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) =
    (podOrdinaryToCompleted l E g D).app
        ((integralCompletedTensor l E Y).obj
          (DerivedCategory.Q.obj P.obj,DerivedCategory.Q.obj Q.obj)) ≫
      ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom := by
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, integralOperationsRoosFunctor,
    Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj] at *
  have hs := podReindexing_tensor_roos_normalization l E g D
    (podTensorReindexAt l E g D hD P Q τ) hD
    (podTensorReindexAt_generators l E g D hD P Q τ hgen) P Q
  dsimp only [podReindexingTensorFrame, integralOperationsTensorOnGood,
    integralOperationsTensorComplexFunctor, integralOperationsGoodLocalization,
    integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hs
  let eP := podRepresentativeReindexFactors l E g D P
  let eQ := podRepresentativeReindexFactors l E g D Q
  let e := (integralCompletedTensorComparison l E X).app
    ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q)
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, integralOperationsRoosFunctor,
    Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj] at e
  let k := podReindexingLimitTensorComparisonHom l E g D hD
    (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)
  dsimp only [podReindexingTensorFrame] at k
  let fP := (podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj)
  let fQ := (podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj)
  -- Focus the tower rewrite so its derived endpoints stay folded.
  conv at hs =>
    rhs
    arg 2
    arg 2
    arg 2
    arg 2
    arg 1
    arg 1
    rw [podTensorReindexAt_tower]
  have finish := podTensorRepresentative_cancel (integralCompletedTensor l E X)
    eP eQ e k _ hs ((integralCompletedTensor l E X).map (Prod.mkHom fP fQ))
  have hc := podReindexingLimitTensorComparison_canonical l E g D hD ⟨_, hP⟩ ⟨_, hQ⟩
  dsimp only [eP, eQ, e, k, fP, fQ, podRepresentativeReindexFactors, Iso.app, id,
    podReindexingTensorFrame, integralOperationsTensorOnGood,
    integralOperationsTensorComplexFunctor, integralOperationsGoodLocalization,
    podOrdinaryReindex, isoReductionIntegralComplex, podGoodReindex,
    integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.lift, ObjectProperty.ι_obj, scalarReductionSource, integralTowerModules,
    scalarReductionSourceDerived, integralTowerHasDerivedCategory,
    integralOperationsCommHasDerivedCategory] at finish hc ⊢
  have final := finish.trans hc
  assumption

end WeilConjectures
