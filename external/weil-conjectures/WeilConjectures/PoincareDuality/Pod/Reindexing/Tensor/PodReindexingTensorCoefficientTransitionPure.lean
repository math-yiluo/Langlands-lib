/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic

/-! # Pure section component of the normalized coefficient transition

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-pure).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem transitionRingSquare {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoReductionCompletedMap.{u, u} l E g).hom ≫
        (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map
          (integralCompletedScalarMap l E L ι X) =
      (isoSectionwiseInverseImage g RingCat.{u+1}).map
        ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map
          (integralCompletedScalarMap l E L ι Y)) ≫
        (isoReductionCompletedMap.{u, u} l L g).hom := by
  let H (W : Scheme.{u}) := sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u+1} RingCat.{u+1})
  let σ (W : Scheme.{u}) := (H W).map (integralCompletedScalarMap l E L ι W)
  let πE (W : Scheme.{u}) (n : ℕ) :=
    (H W).map (completedIntegralCommRingProjectionUnrestricted l E W n)
  let πL (W : Scheme.{u}) (n : ℕ) :=
    (H W).map (completedIntegralCommRingProjectionUnrestricted l L W n)
  let q (W : Scheme.{u}) (n : ℕ) :=
    (H W).map (integralScalarQuotientSheafMap l E L ι W n)
  let F := isoSectionwiseInverseImage g RingCat.{u+1}
  have hs (W : Scheme.{u}) (n : ℕ) : σ W ≫ πL W n = πE W n ≫ q W n := by
    dsimp only [σ, πE, πL, q]
    rw [← (H W).map_comp, ← (H W).map_comp]
    exact congrArg (H W).map
      ((integralCompletedScalarMap_existsUnique l E L ι W).exists.choose_spec n)
  have hq (n : ℕ) : F.map (q Y n) ≫
      isoSectionwiseConstantMap.{u, u} g
        (CommRingCat.of (ULift.{u+1} (Padic.coefficientExtensionRing l L (n+1)))) =
      isoSectionwiseConstantMap.{u, u} g
        (CommRingCat.of (ULift.{u+1} (Padic.coefficientExtensionRing l E (n+1)))) ≫
          q X n := by
    exact isoReductionConstant_naturality.{u, u} g _
  apply (limit.isLimit (integralCoefficientSheafSystem.{u, u} l L X)).hom_ext
  intro n
  change ((isoReductionCompletedMap.{u, u} l E g).hom ≫ σ X) ≫ πL X n.unop =
    (F.map (σ Y) ≫ (isoReductionCompletedMap.{u, u} l L g).hom) ≫ πL X n.unop
  simp only [Category.assoc]
  rw [hs, ← Category.assoc, isoReduction_completedProjectionSquare.{u, u}]
  rw [Category.assoc, ← hq]
  rw [← F.map_comp_assoc, ← hs, F.map_comp, Category.assoc]
  rw [← isoReduction_completedProjectionSquare.{u, u}]

private theorem transitionOrdinary {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃ e : isoReductionIntegralInverse l E g ⋙ integralOrdinaryScalar l E L ι X ≅
        integralOrdinaryScalar l E L ι Y ⋙ isoReductionIntegralInverse l L g,
      ∀ (M : scalarReductionSource l E Y) (U : X.ProEtᵒᵖ)
        (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U))
        (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
          ((proEtaleIsoPostcompose g).op.obj U)),
        (e.hom.app M).val.app U
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) U
            ((isoReductionCompletedMap.{u, u} l L g).hom.hom.app U a) x) =
          integralOrdinaryTensorSection l E L ι Y M
            ((proEtaleIsoPostcompose g).op.obj U) a x := by
  let H (W : Scheme.{u}) := sheafCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u+1} RingCat.{u+1})
  let σ (W : Scheme.{u}) := (H W).map (integralCompletedScalarMap l E L ι W)
  obtain ⟨s, hs⟩ := restrictionSquare (proEtaleIsoPostcompose g)
    (asIso (isoReductionCompletedMap.{u, u} l E g).hom)
    (asIso (isoReductionCompletedMap.{u, u} l L g).hom)
    (σ Y) (σ X) (transitionRingSquare l E L ι g)
  let := isoReduction_equivalence.{u, u} g (isoReductionCompletedMap.{u, u} l E g).hom
  let := isoReduction_equivalence.{u, u} g (isoReductionCompletedMap.{u, u} l L g).hom
  obtain ⟨e, he⟩ := adjointSquare
    (isoReductionIntegralInverse l E g) (isoReductionIntegralInverse l L g)
    (scalarAdjunction l E L ι Y) (scalarAdjunction l E L ι X) s
  refine ⟨e, ?_⟩
  intro M U x a
  have hh := congrArg (fun f ↦ f.val.app U x) (he M)
  change (e.hom.app M).val.app U
      (((scalarAdjunction l E L ι X).unit.app
        ((isoReductionIntegralInverse l E g).obj M)).val.app U x) =
    (s.hom.app _).val.app U
      (((scalarAdjunction l E L ι Y).unit.app M).val.app
        ((proEtaleIsoPostcompose g).op.obj U) x) at hh
  rw [hs, scalarAdjunction_unit, scalarAdjunction_unit] at hh
  rw [scalar_tensor_one l E L ι X, _root_.map_smul]
  change ((inv (isoReductionCompletedMap.{u, u} l L g).hom).hom.app U
    ((isoReductionCompletedMap.{u, u} l L g).hom.hom.app U a)) •
      (show ((integralOrdinaryScalar l E L ι Y).obj M).val.obj
          ((proEtaleIsoPostcompose g).op.obj U) from
        (e.hom.app M).val.app U
          (integralOrdinaryTensorSection l E L ι X
            ((isoReductionIntegralInverse l E g).obj M) U 1 x)) = _
  have hi : (inv (isoReductionCompletedMap.{u, u} l L g).hom).hom.app U
      ((isoReductionCompletedMap.{u, u} l L g).hom.hom.app U a) = a :=
    congrArg (fun f ↦ f.hom.app U a) (IsIso.hom_inv_id (isoReductionCompletedMap.{u, u} l L g).hom)
  rw [hi, hh]
  exact (scalar_tensor_one l E L ι Y M
    ((proEtaleIsoPostcompose g).op.obj U) a x).symm

end

/-- The pure-tensor section law for a normalized coefficient transition.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-core-pure).
Proof: the completed coefficient maps commute with reindexing because their
composites with every finite quotient projection do, by naturality of the constant
sheaf functor. Transport of restriction of scalars therefore gives a square whose
components are identity maps on sections. Its mate under extension/restriction
adjunction is an isomorphism, since both reindexing functors are equivalences.
The adjunction units are pure tensors with coefficient one, so their mate identity
proves the desired formula for coefficient one. Linearity and the inverse
coefficient isomorphism give the formula for every coefficient. Finally use the
normalized primitive quotient scalar models at X and Y. Constructibility follows
from completed scalar extension and the completion isomorphism on a complete input.
-/
theorem podReindexingTensorCoefficientTransition_pure
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T') :
    ∃ S : PodReindexCoefficientTransition l E L ι g D D',
      ∀ (M : scalarReductionSource l E Y) (U : X.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (S.ordinary.hom.app M).val.app (op U)
            (integralOrdinaryTensorSection l E L ι X
              ((isoReductionIntegralInverse l E g).obj M) (op U)
              ((isoReductionCompletedMap l L g).hom.hom.app (op U) a) x) =
          integralOrdinaryTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a x := by
  obtain ⟨e, he⟩ := transitionOrdinary l E L ι g
  obtain ⟨sY⟩ := primitiveQuotientScalarModelExistence l E L ι Y
    (fun y ↦ isUnit_of_invertible (l : Y.residueField y)) (podReindexCalculus l E Y)
    D'.sourceRoos
  obtain ⟨sX⟩ := primitiveQuotientScalarModelExistence l E L ι X
    (fun x ↦ isUnit_of_invertible (l : X.residueField x)) (podReindexCalculus l E X)
    D'.targetRoos
  refine ⟨{ ordinary := e, source := sY, target := sX, sourceConstructible := ?_ }, ?_⟩
  · intro M
    have h := sfIntegralScalarExtension_constructible (l+1) l (by omega) E L ι Y
      M.obj M.property
    exact (sfIntegralConstructible l L Y).prop_of_iso
      (scalarCompletionIso l E L ι Y M.obj M.property.1).symm h
  · intro M U x a
    exact he M (op U) x a

end WeilConjectures
