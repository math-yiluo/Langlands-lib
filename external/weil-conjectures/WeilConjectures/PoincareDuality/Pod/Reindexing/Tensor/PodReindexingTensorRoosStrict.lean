/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorRoosRepresentativeSquare
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Strict Roos realization for normalized tensor reindexing -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
attribute [local implicit_reducible] WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.coefficientSequenceHasDerived WeilConjectures.coefficientFiniteHasDerived
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem ordinaryComparisonIsIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
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
  have hlp : l ≠ Δ.p := by change l ≠ p; omega
  have hK : IntegralOnSlice.IsComplete l E Y none K.obj :=
    ⟨Δ, hlp, (sfDerivedComplete_iff_legacy l E Y Δ hlp K.obj).mp K.property.1⟩
  have : IsIso ((podReindexCalculus l E Y).adjunction.unit.app K.obj) :=
    hD.2.2.2.2.2.1 K.obj hK
  dsimp only [podOrdinaryToCompleted, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app]
  infer_instance

attribute [local irreducible] integralCompletedTensor sfIntegralConstructible
  podReindexCalculus podOrdinaryToCompleted integralCompletedTensorComparison
  scalarReductionExtension integralOperationsTensorTowerFunctor integralOperationsRoos
  canonicalIntegralPullbackTensor

private theorem comparison_cancel {C : Type*} [Category C] {A B S R Z : C}
    (u : B ≅ S) (v : S ≅ R) (a : A ⟶ B) (r : A ⟶ R) (b : B ⟶ Z) [Mono b]
    (c : A ⟶ Z) (hs : r ≫ v.inv ≫ u.inv ≫ b = c) :
    HEq r (a ≫ u.hom ≫ v.hom) ↔ c = a ≫ b := by
  constructor
  · intro h
    rw [eq_of_heq h] at hs
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs.symm
  · intro h
    apply heq_of_eq
    apply (cancel_mono v.inv).1
    apply (cancel_mono u.inv).1
    apply (cancel_mono b).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hs.trans h

private theorem tensor_comparison_cancel
    {C D : Type*} [Category C] [Category D] {P Q P' Q' : C} {A R Z : D}
    (F : C × C ⥤ D) (f : P ≅ P') (g : Q ≅ Q') (e : F.obj (P', Q') ≅ R)
    (a : A ⟶ F.obj (P, Q)) (r : A ⟶ R) (b : F.obj (P, Q) ⟶ Z) [hb : IsIso b]
    (c : A ⟶ Z) (hs : r ≫ e.inv ≫ F.map (Prod.mkHom f.inv g.inv) ≫ b = c) :
    HEq r (a ≫ F.map (Prod.mkHom f.hom g.hom) ≫ e.hom) ↔ c = a ≫ b := by
  exact comparison_cancel (F.mapIso (Iso.prod f g)) e a r b c hs

private theorem representative_equivalence
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T)
    [(isoReductionIntegralInverse l E g).Additive]
    [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
    [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
    (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)) :
    HEq ((podOrdinaryReindex l E g).map ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
            integralOperationsRoosFunctor.map (T.tower P Q).hom))
      ((T.tensor (⟨DerivedCategory.Q.obj P.obj,hP⟩ : sfIntegralConstructibleCategory l E Y)
        (⟨DerivedCategory.Q.obj Q.obj,hQ⟩ : sfIntegralConstructibleCategory l E Y)).hom ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app P.obj)
            ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
        (integralCompletedTensorComparison l E X).hom.app
          ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q)) ↔
        (podOrdinaryToCompleted l E g D).app
            ((integralCompletedTensor l E Y).obj
              (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
            ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom =
          (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom ≫
            (integralCompletedTensor l E X).map
              (Prod.mkHom
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) := by
  let F := integralCompletedTensor l E X
  let B := F.map (Prod.mkHom
    ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
    ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj)))
  let a := (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom
  let r := (podOrdinaryReindex l E g).map
      ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
    (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
    DerivedCategory.Q.map
      ((D.roos ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj))).hom ≫
        integralOperationsRoosFunctor.map (T.tower P Q).hom)
  let c := (podOrdinaryToCompleted l E g D).app
      ((integralCompletedTensor l E Y).obj
        (DerivedCategory.Q.obj P.obj,DerivedCategory.Q.obj Q.obj)) ≫
    ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom
  have hβP := ordinaryComparisonIsIso l E g D hD
    (⟨DerivedCategory.Q.obj P.obj,hP⟩ : sfIntegralConstructibleCategory l E Y)
  have hβQ := ordinaryComparisonIsIso l E g D hD
    (⟨DerivedCategory.Q.obj Q.obj,hQ⟩ : sfIntegralConstructibleCategory l E Y)
  have : IsIso (Prod.mkHom
      ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
      ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) :=
    (isIso_prod_iff _ _).mpr ⟨hβP, hβQ⟩
  have hB : IsIso B := F.map_isIso _
  have hs :=
    podTensorRoosRepresentativeSquare l E g D hD P Q hP hQ (T.tower P Q) (hgen P Q)
  exact tensor_comparison_cancel F (hb := hB)
    ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app P.obj)
    ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app Q.obj)
    ((integralCompletedTensorComparison l E X).app
      ((podGoodReindex l E g D).obj P,(podGoodReindex l E g D).obj Q)) a r B c hs

/-- The strict Roos equation is equivalent to the canonical equation on good
representatives. No naturality of the independently supplied derived tensor family
is assumed, so the conclusion concerns actual localized representatives only.

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-tensor-roos-model-iff-canonical).

Proof: the representative square identifies the localized strict Roos arrow,
transported through the two representative comparisons and the completion maps,
with the canonical completed tensor arrow. The completion maps on constructible
inputs are invertible by CompleteUnit. Cancel their tensor and the representative
comparison to obtain the equivalence, independently for each pair of representatives.

STATEMENT-DISPUTED: the old generator and tower naturality laws do not
constrain T.tensor. In particular they cannot imply the global Canonical equation.
The repaired statement identifies exactly the equation needed by the parent.
-/
theorem podReindexingTensorRoosNormalization_model_iff_canonical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T) :
    PodCompletedTensorReindex.Model l E g D T ↔
      ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
        (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)),
        (podOrdinaryToCompleted l E g D).app
            ((integralCompletedTensor l E Y).obj
              (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
            ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom =
          (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom ≫
            (integralCompletedTensor l E X).map
              (Prod.mkHom
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj))) := by
  have : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  have : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  have : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  constructor
  · intro h P Q hP hQ
    exact (representative_equivalence l E g D hD T hgen P Q hP hQ).mp (h P Q hP hQ)
  · intro h P Q hP hQ
    exact (representative_equivalence l E g D hD T hgen P Q hP hQ).mpr (h P Q hP hQ)

end WeilConjectures
