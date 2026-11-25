/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralOrdinaryTensorChain
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Ordinary tensor chain comparisons and coefficient towers

Source: Stacks 03EL, 07A4; coefficient-comparison coherence in the blueprint.
(blueprint: lem-pur-integral-scalar-ordinary-tensor-chain-tower). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOrdinaryScalarComp scalarAdjunction

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (j : L →ₐ[ℚ_[l]] F)

private abbrev ordinaryTensorIso (W : AlgebraicGeometry.Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) ⋙
          (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)).prod
        ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l L W)

private abbrev ordinaryTensorNormalized (W : AlgebraicGeometry.Scheme.{u})
    (α : ordinaryTensorIso l E L ι W) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ)
        (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((α.hom.app (P, Q)).f (p + q)).val.app U
          (integralOrdinaryTensorSection l E L ι W
            (((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) U 1
            (coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y)) =
        coefficientTensorGenerator.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l L W)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)
          (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
          (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)

private theorem scalarDoubleUnit (W : AlgebraicGeometry.Scheme.{u})
    (N : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : N.val.obj U) :
    ((scalarAdjunction l L F j W).unit.app ((integralOrdinaryScalar l E L ι W).obj N)).val.app
        U (((scalarAdjunction l E L ι W).unit.app N).val.app U x) =
      integralOrdinaryTensorSection l L F j W _ U 1
        (integralOrdinaryTensorSection l E L ι W N U 1 x) := by
  erw [scalarAdjunction_unit, scalarAdjunction_unit]

private theorem ordinaryTensorTowerAux (W : AlgebraicGeometry.Scheme.{u})
    (μ : ordinaryTensorIso l E L ι W) (ν : ordinaryTensorIso l L F j W)
    (ξ : ordinaryTensorIso l E F (j.comp ι) W)
    (ha : ordinaryTensorNormalized l E L ι W μ)
    (hb : ordinaryTensorNormalized l L F j W ν)
    (hc : ordinaryTensorNormalized l E F (j.comp ι) W ξ)
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)).map
        ((μ).hom.app (P, Q)) ≫
      (ν).hom.app
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l F W)).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).hom.app
        ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
      (ξ).hom.app
        (P, Q) := by
  let κ := NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j) (.up ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply (((scalarAdjunction l E L ι W).comp
    (scalarAdjunction l L F j W)).homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u} P Q n
  intro p q hpq U x y
  subst n
  let Z := ((coefficientTotalTensor.{u, u + 1, u}
    (AlgebraicGeometry.Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)
  change (((coefficientTotalTensor.{u, u + 1, u}
      (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l F W)).map
        (CategoryTheory.Prod.mkHom (κ.hom.app P) (κ.hom.app Q))).f (p + q)).val.app U
      (((ν.hom.app _).f (p + q)).val.app U
        (((integralOrdinaryScalar l L F j W).map
          ((μ.hom.app (P, Q)).f (p + q))).val.app U
          (((scalarAdjunction l L F j W).unit.app
            ((integralOrdinaryScalar l E L ι W).obj Z)).val.app U
            (((scalarAdjunction l E L ι W).unit.app Z).val.app U
              (coefficientTensorGenerator.{u, u + 1, u}
                (AlgebraicGeometry.Scheme.ProEt.topology W)
                (completedIntegralCommRingSheafUnrestricted l E W)
                P Q p q (p + q) rfl U x y))))) =
    ((ξ.hom.app (P, Q)).f (p + q)).val.app U
      (((κ.hom.app _).f (p + q)).val.app U
        (((scalarAdjunction l L F j W).unit.app
            ((integralOrdinaryScalar l E L ι W).obj Z)).val.app U
          (((scalarAdjunction l E L ι W).unit.app Z).val.app U
            (coefficientTensorGenerator.{u, u + 1, u}
              (AlgebraicGeometry.Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W)
              P Q p q (p + q) rfl U x y))))
  erw [scalarDoubleUnit]
  erw [scalar_map_tensor]
  erw [ha P Q p q U x y]
  have hν := hb
    (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P)
    (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)
    p q U (integralOrdinaryTensorSection l E L ι W (P.X p) U 1 x)
      (integralOrdinaryTensorSection l E L ι W (Q.X q) U 1 y)
  erw [hν]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}]
  have hk (A : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ)
      (z : (A.X i).val.obj U) :
      (((κ.hom.app A).f i).val.app U)
          (integralOrdinaryTensorSection l L F j W _ U 1
            (integralOrdinaryTensorSection l E L ι W (A.X i) U 1 z)) =
        integralOrdinaryTensorSection l E F (j.comp ι) W (A.X i) U 1 z := by
    change ((integralOrdinaryScalarComp l E L ι W F j).hom.app (A.X i)).val.app U
        (integralOrdinaryTensorSection l L F j W _ U 1
          (integralOrdinaryTensorSection l E L ι W (A.X i) U 1 z)) =
      integralOrdinaryTensorSection l E F (j.comp ι) W (A.X i) U 1 z
    simpa only [integralOrdinaryScalarComp, map_one, one_mul] using
      (integralOrdinaryScalarComp_existsUnique l E L ι W F j).exists.choose_spec
        (A.X i) U 1 1 z
  erw [hk, hk, hk]
  exact (hc P Q p q U x y).symm

/-- Ordinary pure-tensor chain comparisons commute with scalar associators.
Source: Stacks 03EL, 07A4; blueprint scalar comparison proof step 9
(blueprint: lem-pur-integral-scalar-ordinary-tensor-chain-tower).
Proof: the normalization of the ordinary tensor comparison is the map
s tensor (x tensor y) to (s tensor x) tensor (1 tensor y). For a second
extension, both routes on c tensor (b tensor (x tensor y)) give
(c*j(b) tensor x) tensor (1 tensor y). The ordinary scalar associator has
precisely this multiplication formula. This proves equality first on unit scalar
generators, then on all scalar generators by linearity, and on all tensor
generators by balance. The sheafification adjunction extends the equality to
sheaves. Coproduct injections in each total degree extend it to the total
complex, and the prescribed chain comparisons already respect the two signed
differential summands. Thus the degreewise equality proves equality of chain
maps. This uses no boundedness or flatness assumptions; the zero and identity
cases are the same multiplication calculation. -/
theorem integralScalarOrdinaryTensorChainTower (W : AlgebraicGeometry.Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ((integralOrdinaryScalar l L F j W).mapHomologicalComplex (.up ℤ)).map
        (((normalizedIntegralOrdinaryTensorChain l E L ι W).exists.choose).hom.app (P, Q)) ≫
      ((normalizedIntegralOrdinaryTensorChain l L F j W).exists.choose).hom.app
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P,
          ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l F W)).map (CategoryTheory.Prod.mkHom
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app P)
        ((NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
          (.up ℤ)).hom.app Q)) =
    (NatIso.mapHomologicalComplex (integralOrdinaryScalarComp l E L ι W F j)
      (.up ℤ)).hom.app
        ((coefficientTotalTensor.{u, u + 1, u} (AlgebraicGeometry.Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
      ((normalizedIntegralOrdinaryTensorChain l E F (j.comp ι) W).exists.choose).hom.app
        (P, Q) := by
  exact ordinaryTensorTowerAux l E L ι F j W _ _ _
    (normalizedIntegralOrdinaryTensorChain l E L ι W).exists.choose_spec
    (normalizedIntegralOrdinaryTensorChain l L F j W).exists.choose_spec
    (normalizedIntegralOrdinaryTensorChain l E F (j.comp ι) W).exists.choose_spec P Q

end WeilConjectures
