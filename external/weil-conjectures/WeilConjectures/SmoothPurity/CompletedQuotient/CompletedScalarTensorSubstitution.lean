/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTensorModelNormalization
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitSquare
import all WeilConjectures.TraceFormula.Supporting.AmbientComparisonSystemExistence

/-! # Quotient realization steps

Source: Stacks 07A4 and 0941; scalar/tensor compatibility of quotient substitution.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  coefficientSequenceInternalHom integralComparisonDerivedSequenceScalar
  pullbackTensorReferenceTensor ScalarExtensionTower.tensor
  pullbackTensorSystemModel sfConstructibleIntegralScalarExtension
attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

attribute [local irreducible] pullbackTensorCalculus integralDerivedPullback
  integralCompletedTensor coefficientTotalTensor SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory

private theorem reduction_post {W : Scheme.{u}}
    {K : DerivedCategory (scalarReductionSource l E W)}
    {A B : coefficientSequenceDerived l E W}
    (β : K ⟶ (coefficientSequenceLimit l E W).obj A) (a : A ⟶ B) :
    reduction l E (β ≫ (coefficientSequenceLimit l E W).map a) =
      reduction l E β ≫ a := by
  unfold reduction
  rw [Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
    congrArg ((pullbackTensorCalculus l E W).reduction.map β ≫ ·)
      ((pullbackTensorCalculus l E W).adjunction.counit.naturality a)

private theorem scalar_reduction {W : Scheme.{u}}
    {ρ : IntegralComparisonRoosModel l L W}
    (S : IntegralComparisonScalarModel l E L ι W (pullbackTensorCalculus l E W) ρ)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W)
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A)) :
    reduction l L (scalarSubstitution l E L ι S A β) =
      ScalarExtensionTower.scalarReduction l E L ι W (pullbackTensorCalculus l E W)
        (pullbackTensorCalculus l L W) ρ S K ≫
      (integralComparisonDerivedSequenceScalar l E L ι W).map (reduction l E β) ≫
      (integralComparisonSequenceScalarModel l E L ι W).ε.app A := by
  unfold scalarSubstitution
  rw [reduction_post]
  unfold reduction ScalarExtensionTower.scalarReduction
  rfl

private theorem fixed_tensor (W : Scheme.{u}) :
    ScalarExtensionTower.tensorModelRealization l E W (pullbackTensorCalculus l E W) =
      pullbackTensorIntegralTensorModel l E W := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  rcases V with ⟨K, H⟩
  rw [ScalarExtensionTower.tensorModelRealization_hom]
  have hi (X Y : coefficientSequenceDerived l E W) :
      Prod.mkHom (𝟙 X) (𝟙 Y) = 𝟙 (X, Y) := rfl
  simp only [Adjunction.leftAdjointUniq_refl, Iso.refl_hom, NatTrans.id_app,
    CoefficientClosedStructure.comparison_eqToIso _ _ rfl, eqToIso_refl,
    hi, Category.comp_id]
  erw [(pullbackTensorCalculus l E W).systemClosed.tensor.map_id,
    (coefficientSequenceLimit l E W).map_id, Category.comp_id]

omit [Fact l.Prime] in
private theorem prime_unit (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  apply W.toRingedSpace.isUnit_of_isUnit_germ
  intro w hw
  apply isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk w))
  rw [map_natCast]
  with_unfolding_all exact isUnit_of_invertible (l : W.residueField w)

private theorem tensor_scalar_substitution {W : Scheme.{u}}
    {ρ : IntegralComparisonRoosModel l L W}
    (S : IntegralComparisonScalarModel l E L ι W (pullbackTensorCalculus l E W) ρ)
    {K H : DerivedCategory (scalarReductionSource l E W)}
    (A B : StrictQuotient.Complex l E W)
    (hsA : StrictQuotient.SystemGood l L ((ScalarExtensionTower.scalar l E L ι W).obj A))
    (hsB : StrictQuotient.SystemGood l L ((ScalarExtensionTower.scalar l E L ι W).obj B))
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (γ : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B)) :
    let FE := integralComparisonDerivedSequenceScalar l E L ι W
    let LL := coefficientSequenceLimit l L W
    let U := (pullbackTensorCalculus l L W).systemClosed.tensor
    let r := ScalarExtensionTower.scalarReduction l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W) ρ S
    tensorSubstitution l L ((ScalarExtensionTower.scalar l E L ι W).obj A)
        ((ScalarExtensionTower.scalar l E L ι W).obj B) hsA hsB
        (scalarSubstitution l E L ι S A β) (scalarSubstitution l E L ι S B γ) =
      (pullbackTensorIntegralTensorModel l L W).hom.app
        ((integralScalarExtension l E L ι W).obj K,
          (integralScalarExtension l E L ι W).obj H) ≫
      LL.map (U.map (Prod.mkHom (r K) (r H))) ≫
      LL.map (U.map (Prod.mkHom (FE.map (reduction l E β)) (FE.map (reduction l E γ)))) ≫
      LL.map (U.map (Prod.mkHom
        ((integralComparisonSequenceScalarModel l E L ι W).ε.app A)
        ((integralComparisonSequenceScalarModel l E L ι W).ε.app B))) ≫
      LL.map (pullbackTensorSystemModel l L W
        ((ScalarExtensionTower.scalar l E L ι W).obj A)
        ((ScalarExtensionTower.scalar l E L ι W).obj B) hsA.1 hsB.1).inv := by
  dsimp only
  unfold tensorSubstitution
  rewrite [scalar_reduction l E L ι S A β, scalar_reduction l E L ι S B γ]
  simp only [← Functor.map_comp, ← Category.assoc]
  rfl

-- The calculation combines three naturality squares in the system derived category.
/-- Scalar extension of tensor substitution is computed by the normalized strict sigma.
Source: Stacks 07A4 and 0941; the tensor step of scalar route coordinates.
(blueprint: lem-pur-completed-scalar-tensor-substitution).

Proof: take the adjunction transpose of the tensor substitution. Naturality of the
coherent counit identifies it with tensorReduction followed by the two reduced inputs
and the inverse system tensor model. The derivedSigma normalization moves this model
past sigma, and naturality moves the reduced inputs past derivedSigma. The scalar
limit square identifies the remaining prefix with the prescribed completed tensor
scalar comparison. Functoriality combines the scalar reductions of the two inputs.
All equations hold in the derived category of entire systems before total limit. -/
theorem completedScalarTensorSubstitution {W : Scheme.{u}}
    [∀ w : W, Invertible (l : W.residueField w)]
    {ρ : IntegralComparisonRoosModel l L W}
    (S : IntegralComparisonScalarModel l E L ι W (pullbackTensorCalculus l E W) ρ)
    (M N : sfIntegralConstructibleCategory l E W)
    (A B : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (hsA : StrictQuotient.SystemGood l L ((ScalarExtensionTower.scalar l E L ι W).obj A))
    (hsB : StrictQuotient.SystemGood l L ((ScalarExtensionTower.scalar l E L ι W).obj B))
    (β : M.obj ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (γ : N.obj ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B)) :
    scalarSubstitution l E L ι S (StrictQuotient.total l E A B)
        (tensorSubstitution l E A B hA hB β γ) ≫
      (coefficientSequenceLimit l L W).map (DerivedCategory.Q.map
        (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app (A, B))) =
    (integralTensorScalarComparison l E L ι W M N).hom.hom ≫
      tensorSubstitution l L ((ScalarExtensionTower.scalar l E L ι W).obj A)
        ((ScalarExtensionTower.scalar l E L ι W).obj B) hsA hsB
        (scalarSubstitution l E L ι S A β) (scalarSubstitution l E L ι S B γ) := by
  let SE := pullbackTensorCalculus l E W
  let SL := pullbackTensorCalculus l L W
  obtain ⟨ρE⟩ := ambientRoos l E W SE
  let TE : ScalarExtensionTower.TensorModel l E W SE ρE :=
    ⟨ScalarExtensionTower.tensorModelRealization l E W SE,
      ScalarExtensionTower.tensorModelRealization_normalized l E W SE ρE⟩
  let TL : ScalarExtensionTower.TensorModel l L W SL ρ :=
    ⟨ScalarExtensionTower.tensorModelRealization l L W SL,
      ScalarExtensionTower.tensorModelRealization_normalized l L W SL ρ⟩
  have hlim := ScalarExtensionTower.scalarTowerTensorLimitSquare l E L ι W SE SL ρE ρ
    S TE TL (prime_unit l W) M N
    ((constructibleIntegralTensor l E W).obj (M, N)).property.1
  have hn := (ScalarExtensionTower.derivedSigma_existsUnique l E L ι W SE SL).exists.choose_spec
  change ScalarExtensionTower.DerivedSigmaModel l E L ι W SE SL
    (ScalarExtensionTower.derivedSigma l E L ι W SE SL) at hn
  obtain ⟨_, _, hnorm⟩ := hn A B hA hB
  let FE := integralComparisonDerivedSequenceScalar l E L ι W
  let LE := coefficientSequenceLimit l E W
  let LL := coefficientSequenceLimit l L W
  let T := SE.systemClosed.tensor
  let U := SL.systemClosed.tensor
  let α := ScalarExtensionTower.derivedSigma l E L ι W SE SL
  let a := reduction l E β
  let b := reduction l E γ
  let e := pullbackTensorSystemModel l E W A B hA.1 hB.1
  let d := pullbackTensorSystemModel l L W
    ((ScalarExtensionTower.scalar l E L ι W).obj A)
    ((ScalarExtensionTower.scalar l E L ι W).obj B) hsA.1 hsB.1
  change FE.map e.hom ≫ α.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
    U.map (Prod.mkHom ((integralComparisonSequenceScalarModel l E L ι W).ε.app A)
      ((integralComparisonSequenceScalarModel l E L ι W).ε.app B)) =
    (integralComparisonSequenceScalarModel l E L ι W).ε.app (StrictQuotient.total l E A B) ≫
      DerivedCategory.Q.map (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
        (A, B)) ≫ d.hom at hnorm
  have hnorm' : FE.map e.inv ≫
        (integralComparisonSequenceScalarModel l E L ι W).ε.app
          (StrictQuotient.total l E A B) ≫
        DerivedCategory.Q.map (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
          (A, B)) =
      α.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        U.map (Prod.mkHom
          ((integralComparisonSequenceScalarModel l E L ι W).ε.app A)
          ((integralComparisonSequenceScalarModel l E L ι W).ε.app B)) ≫ d.inv := by
    apply (cancel_epi (FE.map e.hom)).1
    simp only [← Category.assoc, ← FE.map_comp, e.hom_inv_id, FE.map_id,
      Category.id_comp]
    have hh := congrArg (fun k ↦ k ≫ d.inv) hnorm
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm
  have hnat := α.hom.naturality (Prod.mkHom a b)
  change FE.map (T.map (Prod.mkHom a b)) ≫
      α.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) =
    α.hom.app (SE.reduction.obj M.obj, SE.reduction.obj N.obj) ≫
      U.map (Prod.mkHom (FE.map a) (FE.map b)) at hnat
  have hred : reduction l E (tensorSubstitution l E A B hA hB β γ) =
      ScalarExtensionTower.tensorReduction l E W SE ρE TE M.obj N.obj ≫
        T.map (Prod.mkHom a b) ≫ e.inv := by
    unfold tensorSubstitution
    change reduction l E
      ((pullbackTensorIntegralTensorModel l E W).hom.app (M.obj, N.obj) ≫
        LE.map (T.map (Prod.mkHom a b)) ≫ LE.map e.inv) = _
    rewrite [← LE.map_comp, reduction_post]
    dsimp only [ScalarExtensionTower.tensorReduction, TE]
    rewrite [fixed_tensor l E W]
    unfold reduction
    simp only [Category.assoc]
    rfl
  conv_lhs => unfold scalarSubstitution
  rewrite [hred]
  change (S.realization.hom.app _ ≫ LL.map _) ≫ LL.map _ = _
  change (S.realization.hom.app _ ≫ LL.map
    (FE.map (ScalarExtensionTower.tensorReduction l E W SE ρE TE M.obj N.obj ≫
      T.map (Prod.mkHom a b) ≫ e.inv) ≫
      (integralComparisonSequenceScalarModel l E L ι W).ε.app
        (StrictQuotient.total l E A B))) ≫ LL.map _ = _
  simp only [FE.map_comp, Category.assoc, ← LL.map_comp]
  rewrite [hnorm', reassoc_of% hnat]
  have hpost := congrArg (fun k ↦ k ≫ LL.map
    (U.map (Prod.mkHom (FE.map a) (FE.map b)) ≫
      U.map (Prod.mkHom ((integralComparisonSequenceScalarModel l E L ι W).ε.app A)
        ((integralComparisonSequenceScalarModel l E L ι W).ε.app B)) ≫ d.inv)) hlim.symm
  simp only [Functor.map_comp, Category.assoc] at hpost ⊢
  refine hpost.trans ?_
  rewrite [tensor_scalar_substitution l E L ι S A B hsA hsB β γ]
  dsimp only [TL]
  rewrite [fixed_tensor l L W]
  rfl

end WeilConjectures.CompletedQuotient
