/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingHomResolutionModel
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore

/-! # Presentations for the reduction/reindexing tensor square

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: def-pod-reduction-reindex-representatives)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local instance 1000000] SheafOfModules.instAbelian
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

/-- Rebuild a localization factor componentwise after an isomorphism of functors.
Source: naturality of a composite of natural isomorphisms; Stacks 05RU. -/
def reductionFactorOfIso
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D) (F₀ : C₀ ⥤ D₀)
    (F G : C ⥤ D) (e : F ≅ G) (a : q ⋙ F ≅ F₀ ⋙ r) :
    q ⋙ G ≅ F₀ ⋙ r :=
  NatIso.ofComponents (fun P ↦ (e.app (q.obj P)).symm ≪≫ a.app P)
    (fun f ↦ (Functor.isoWhiskerLeft q e.symm ≪≫ a).hom.naturality f)

/-- Component equation for the componentwise localization factor.
Source: its defining components; Stacks 05RU. -/
theorem reductionFactorOfIso_hom
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D) (F₀ : C₀ ⥤ D₀)
    (F G : C ⥤ D) (e : F ≅ G) (a : q ⋙ F ≅ F₀ ⋙ r) (P : C₀) :
    (reductionFactorOfIso q r F₀ F G e a).hom.app P =
      e.inv.app (q.obj P) ≫ a.hom.app P := rfl

/-- Transport a localization factor with both its ordinary and derived functors.
Source: composition of natural isomorphisms; Stacks 05RU. -/
def reductionSystemFactorOfIso
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D) (F₀ G₀ : C₀ ⥤ D₀)
    (F G : C ⥤ D) (e₀ : F₀ ≅ G₀) (e : F ≅ G) (a : q ⋙ F ≅ F₀ ⋙ r) :
    q ⋙ G ≅ G₀ ⋙ r :=
  NatIso.ofComponents
    (fun P ↦ (e.app (q.obj P)).symm ≪≫ a.app P ≪≫ r.mapIso (e₀.app P))
    (fun f ↦ (Functor.isoWhiskerLeft q e.symm ≪≫ a ≪≫
      Functor.isoWhiskerRight e₀ r).hom.naturality f)

/-- Component equation for transport of the ordinary and derived functors.
Source: its defining components; Stacks 05RU. -/
theorem reductionSystemFactorOfIso_hom
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (q : C₀ ⥤ C) (r : D₀ ⥤ D) (F₀ G₀ : C₀ ⥤ D₀)
    (F G : C ⥤ D) (e₀ : F₀ ≅ G₀) (e : F ≅ G) (a : q ⋙ F ≅ F₀ ⋙ r) (P : C₀) :
    (reductionSystemFactorOfIso q r F₀ G₀ F G e₀ e a).hom.app P =
      e.inv.app (q.obj P) ≫ a.hom.app P ≫ r.map (e₀.hom.app P) := rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

namespace PodReductionRepresentatives

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none
set_option quotPrecheck false in
set_option hygiene false in
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

/-- The two inverse-image presentations agree by uniqueness of the coefficient map.
Source: Stacks 03D2 and 0941. -/
theorem inverse_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullbackTensorSequenceInverse l E g = integralComparisonSequencePullback l E g := by
  unfold pullbackTensorSequenceInverse integralComparisonSequencePullback
  congr 1
  unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
  rw [pullbackTensorSequenceRing_eq]

/-- The derived functors agree after the ordinary coefficient-map equality.
Source: Stacks 05RU, 0941. -/
theorem derived_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    pullbackTensorSequenceDerived l E g = integralComparisonDerivedSequencePullback l E g := by
  have he := inverse_eq l E g
  unfold pullbackTensorSequenceDerived integralComparisonDerivedSequencePullback
  congr 1

/-- The existing sequence localization, with its source and target fixed explicitly.
Source: Stacks 05RU
(blueprint: def-pod-reduction-reindex-representatives). -/
def systemQ (W : Scheme.{u}) :
    CochainComplex (coefficientSequenceModules l E W) ℤ ⥤ coefficientSequenceDerived l E W :=
  letI := coefficientSequenceHasDerived l E W
  DerivedCategory.Q

/-- The localization factor of the fixed system pullback presentation.
Source: its derived-functor construction; Stacks 05RU.
(blueprint: def-pod-reduction-reindex-representatives). -/
def rawSystemFactor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    systemQ l E Y ⋙ pullbackTensorSequenceDerived l E g ≅
      (pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ) ⋙ systemQ l E X :=
  (pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors

/-- Localization factor with the same transport as the canonical system tensor map.
The factor is transported from the fixed pullback presentation on both sides of
localization. Its components retain the ordinary coefficient-map equality, so no
comparison of two presentations of the derived-category instance is needed.
Source: Stacks 05RU, 0941
(blueprint: def-pod-reduction-reindex-representatives). -/
def systemFactor {X Y : Scheme.{u}} (g : X ⟶ Y) :
    systemQ l E Y ⋙ integralComparisonDerivedSequencePullback l E g ≅
      I[g] ⋙ systemQ l E X :=
  reductionSystemFactorOfIso (systemQ l E Y) (systemQ l E X)
    ((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)) (I[g])
    (pullbackTensorSequenceDerived l E g) (integralComparisonDerivedSequencePullback l E g)
    (NatIso.mapHomologicalComplex (eqToIso (inverse_eq l E g)) (.up ℤ))
    (eqToIso (derived_eq l E g))
    (rawSystemFactor l E g)

/-- Transport the unit-normalized system cochain tensor comparison.
Source: Stacks 07A4 and 0941. -/
def systemChain {X Y : Scheme.{u}} (g : X ⟶ Y) :
    S[Y] ⋙ I[g] ≅ (I[g]).prod (I[g]) ⋙ S[X] :=
  let e := NatIso.mapHomologicalComplex (eqToIso (inverse_eq l E g)) (.up ℤ)
  Functor.isoWhiskerLeft _ e.symm ≪≫ pullbackTensorSequenceCochain l E g ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) _

/-- The ordinary comparison is fixed on scalar generators at every quotient level.
Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03EL, 0941.
(blueprint: def-pod-reduction-reindex-representatives). -/
def Generators {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (β : (I[g]).obj ((R[Y]).obj P) ≅ (R[X]).obj ((F[g]).obj P)) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
    ((β.hom.f i).val.app (op (n, U)))
      (((integralComparisonSequencePullback l E g).obj
          ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i))).val.map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
        (integralComparisonSequenceGenerator.{u,u} l E g
          ((pullbackTensorOrdinaryReduction l E Y).obj (P.X i)) n
          ((proEtaleIsoPostcompose g).obj U)
          ((((pullbackTensorReductionEvaluation l E Y n).hom.app (P.X i)).val.app
            (op ((proEtaleIsoPostcompose g).obj U)))
            (unrestrictedIntegralTensorSection.{u,u} l E Y n (P.X i)
              (op ((proEtaleIsoPostcompose g).obj U)) a x)))) =
      (((pullbackTensorReductionEvaluation l E X n).hom.app
        (((F[g]).obj P).X i)).val.app (op U))
        (unrestrictedIntegralTensorSection.{u,u} l E X n (((F[g]).obj P).X i) (op U)
          ((isoSectionwiseConstantMap.{u,u} g (CommRingCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
              (op U) a) x)

/-- The exact reindexing localization factor in the ordinary presentation.
Source: Stacks 05RU. -/
def factor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g) :
    podReindexingQ l E Y none ⋙ podOrdinaryReindex l E g ≅
      F[g] ⋙ podReindexingQ l E X none :=
  reductionFactorOfIso (podReindexingQ l E Y none) (podReindexingQ l E X none)
    (podReindexingComplexFunctor l E g none) (podReindexingDerivedFunctor l E g none)
    (podOrdinaryReindex l E g) (eqToIso h) (podReindexingDerivedFactors l E g none)

end PodReductionRepresentatives
end WeilConjectures
