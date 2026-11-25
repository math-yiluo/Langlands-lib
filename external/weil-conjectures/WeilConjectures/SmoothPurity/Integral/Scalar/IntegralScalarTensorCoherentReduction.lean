/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionModel
import WeilConjectures.TraceFormula.Supporting.TransportedReductionScalarNormalized
import all WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTensorModelNormalization
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientScalarModelExistence

/-! # Coherent reduction of the scalar tensor comparison

Source: Stacks Project, Tags 07A4, 0941 and 0FPQ.
(blueprint: lem-pur-integral-scalar-tensor-coherent-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem coefficientPrime_isUnit (l : ℕ) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply RingedSpace.isUnit_of_isUnit_germ W.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : W.residueField x)).ne_zero

attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

-- The proof compares the completed and entire-system derived normalizations.
/-- The prescribed scalar tensor comparison respects the coherent tensor reductions.
This assertion contains no braiding or signed-swap equation.

Source: Stacks 07A4 and 0941; the normalization step in
lem-pur-integral-braiding-scalar-extension-square-reduced.
(blueprint: lem-pur-integral-scalar-tensor-coherent-reduction).

Proof: use the primitive quotient scalar realization with the two published
coefficient calculi. Its reduction followed by the coherent counit is natural.
On a constructible complete input the quotient scalar system is normalized, so
normalized DVR effectivity makes that counit invertible. This gives p on the
constructible subcategory. Choose the tensor realizations obtained by transporting
the fixed completed tensor model to these same calculi. Their reduction maps
are precisely pullbackTensorIntegralReductionTensor. The scalar tower tensor
limit square identifies scalarTensorCompleted with the limit of derivedSigma
and the two tensor reductions. Apply coherent reduction, postcompose with the
counit and use its naturality. This is the displayed equation. The restricted
comparison integralTensorScalarComparison has exactly this ambient hom by its
definition. The construction retains entire systems and every quotient transition;
it needs no flatness of a quotient coefficient map and applies also to zero inputs,
the identity coefficient extension and ramified extensions. -/
theorem integralScalarTensorCoherentReduction
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    let F := sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
    let R := integralSystemReduction l E W
    let Q := integralSystemReduction l L W
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    ∃ p : F ⋙ Q ≅ R ⋙ H, ∀ M N : sfIntegralConstructibleCategory l E W,
      Q.map (integralTensorScalarComparison l E L ι W M N).hom ≫
        (pullbackTensorIntegralReductionTensor l L W (F.obj M) (F.obj N)).hom ≫
        (pullbackTensorCalculus l L W).systemClosed.tensor.map
          (Prod.mkHom (p.hom.app M) (p.hom.app N)) =
      p.hom.app ((constructibleIntegralTensor l E W).obj (M, N)) ≫
        H.map (pullbackTensorIntegralReductionTensor l E W M N).hom ≫
        (ScalarExtensionTower.derivedSigma l E L ι W
          (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
            (R.obj M, R.obj N) := by
  let SE := pullbackTensorCalculus l E W
  let SL := pullbackTensorCalculus l L W
  have ρE := Classical.choice (ambientRoos l E W SE)
  have ρL := Classical.choice (ambientRoos l L W SL)
  have S := Classical.choice (primitiveQuotientScalarModelExistence l E L ι W
    (fun w ↦ isUnit_of_invertible (l : W.residueField w)) SE ρL)
  let TE : ScalarExtensionTower.TensorModel l E W SE ρE :=
    ⟨ScalarExtensionTower.tensorModelRealization l E W SE,
      ScalarExtensionTower.tensorModelRealization_normalized l E W SE ρE⟩
  let TL : ScalarExtensionTower.TensorModel l L W SL ρL :=
    ⟨ScalarExtensionTower.tensorModelRealization l L W SL,
      ScalarExtensionTower.tensorModelRealization_normalized l L W SL ρL⟩
  let F := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let R := integralSystemReduction l E W
  let Q := integralSystemReduction l L W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let c : integralScalarExtensionOfUniverses l E L ι W ⋙ SL.reduction ⟶
      SE.reduction ⋙ H :=
    Functor.whiskerRight S.realization.hom SL.reduction ≫
      Functor.whiskerLeft (SE.reduction ⋙ H) SL.adjunction.counit
  let a : F ⋙ Q ⟶ R ⋙ H :=
    { app := fun K ↦ c.app K.obj
      naturality := fun _ _ f ↦ c.naturality f.hom }
  have ha (K : sfIntegralConstructibleCategory l E W) : IsIso (a.app K) := by
    have : IsIso (SL.adjunction.counit.app (H.obj (SE.reduction.obj K.obj))) :=
      normalizedSequence_counit_isIso l L W SL _
        (transportedReductionSystems_scalar_normalized l E L ι
          (fun w ↦ isUnit_of_invertible (l : W.residueField w)) SE K.obj)
    change IsIso (SL.reduction.map (S.realization.hom.app K.obj) ≫
      SL.adjunction.counit.app (H.obj (SE.reduction.obj K.obj)))
    infer_instance
  have : IsIso a := (NatTrans.isIso_iff_isIso_app a).2 ha
  refine ⟨asIso a, ?_⟩
  intro M N
  have ht (D : Type u) [Field D] [Algebra (Padic l) D]
      [FiniteDimensional (Padic l) D] (ρ : IntegralComparisonRoosModel l D W)
      (A B : sfIntegralConstructibleCategory l D W) :
      ScalarExtensionTower.tensorReduction l D W (pullbackTensorCalculus l D W) ρ
        ⟨ScalarExtensionTower.tensorModelRealization l D W (pullbackTensorCalculus l D W),
          ScalarExtensionTower.tensorModelRealization_normalized l D W
            (pullbackTensorCalculus l D W) ρ⟩ A.obj B.obj =
        (pullbackTensorIntegralReductionTensor l D W A B).hom := by
    dsimp only [ScalarExtensionTower.tensorReduction]
    rw [ScalarExtensionTower.tensorModelRealization_hom]
    have hi (X Y : coefficientSequenceDerived l D W) :
        Prod.mkHom (𝟙 X) (𝟙 Y) = 𝟙 (X, Y) := rfl
    simp only [Adjunction.leftAdjointUniq_refl, Iso.refl_hom, NatTrans.id_app,
      CoefficientClosedStructure.comparison_eqToIso _ _ rfl, eqToIso_refl,
      hi, Category.comp_id]
    erw [(pullbackTensorCalculus l D W).systemClosed.tensor.map_id,
      (coefficientSequenceLimit l D W).map_id, Category.comp_id]
    rfl
  have h := ScalarExtensionTower.scalarTowerTensorLimitSquare l E L ι W SE SL ρE ρL
    S TE TL (coefficientPrime_isUnit l W) M N
    ((constructibleIntegralTensor l E W).obj (M, N)).property.1
  have h' := ScalarExtensionTower.reduction_of_limit_square SL.adjunction
    (scalarTensorCompleted l E L ι W M.obj N.obj M.property.1 N.property.1
      ((constructibleIntegralTensor l E W).obj (M, N)).property.1).hom
    (TL.realization.hom.app
      ((integralScalarExtension l E L ι W).obj M.obj,
        (integralScalarExtension l E L ι W).obj N.obj))
    (S.realization.hom.app ((integralCompletedTensor l E W).obj (M.obj, N.obj)))
    _ _ h
  change SL.reduction.map _ ≫
      ScalarExtensionTower.tensorReduction l L W SL ρL TL (F.obj M).obj (F.obj N).obj ≫
        SL.systemClosed.tensor.map (Prod.mkHom (a.app M) (a.app N)) =
    a.app ((constructibleIntegralTensor l E W).obj (M, N)) ≫
      H.map (ScalarExtensionTower.tensorReduction l E W SE ρE TE M.obj N.obj) ≫ _ at h'
  change Q.map _ ≫ _ ≫ _ = a.app _ ≫ _ ≫ _
  rw [ht L ρL (F.obj M) (F.obj N), ht E ρE M N] at h'
  exact h'

end WeilConjectures
