/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCoreTensorData
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! The normalized tensor comparison at a single finite coefficient level.
(blueprint: lem-pod-reindexing-finite-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section GeneratorNormalization
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
open scoped TensorProduct

private theorem finiteTensorUnit_section
    {B : Type a} [Category.{b} B] {J : GrothendieckTopology B}
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J RingCat.{u + 1}) (M : PresheafOfModules.{u + 1} R.obj)
    (U : Bᵒᵖ) (x : M.obj U) :
    (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app M).app U) x =
      (toSheafify J M.presheaf).app U x := by
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app (𝟙 R.obj) M) U) x

private theorem finiteTensorGenerator_eq (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ)
    (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X q).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      ((unrestrictedIntegralFiniteComplex l E W n).obj P)
      ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q (p + q) rfl U x y =
    integralOperationsTotalTensorSection l E W n P Q p q U x y := by
  unfold coefficientTensorGenerator integralOperationsTotalTensorSection
    integralOperationsTensorSection
  erw [PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  erw [finiteTensorUnit_section]
  rfl

end GeneratorNormalization

/-- Reindexing a restricted finite total tensor, followed by any two finite chain
isomorphisms, has the prescribed map on every tensor summand.

Source: blueprint `theorem-poincare-duality-frobenius--2`, Steps 1 and 5;
Stacks 03EL, 012Z, 07A4 (blueprint: lem-pod-reindexing-finite-tensor-comparison).

Proof: commute sectionwise reindexing with restriction of scalars using the
completed projection square. At finite coefficients the sectionwise tensor
comparison sends x tensor y to the tensor of the same sections. It is natural:
the two composites agree on pure tensors, which determine maps after
sheafification. Reindexing is an additive equivalence and preserves coproducts,
so this comparison extends to the direct-sum total complex. On a summand of
bidegree (p,q), both differentials are d(x) tensor y + (-1)^p x tensor d(y),
hence the extended maps are chain maps. The inverse is the inverse sectionwise
tensor comparison, with inverse coefficient transport. Finally apply the total
tensor functor to a and b and restrict scalars. Their inverses give the inverse
of the composite, and evaluation on each coproduct injection gives the formula.
No compatibility between different coefficient levels is asserted here.
-/
private theorem podReindexingFiniteTensorComparison_withModels
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ)
    (CX : CoefficientDerivedSystemCalculus l E X)
    (CY : CoefficientDerivedSystemCalculus l E Y)
    (P Q : CochainComplex (integralTowerModules l E Y) ℤ)
    (P' Q' : CochainComplex (integralTowerModules l E X) ℤ)
    (a : (isoReductionFiniteComplex l E g n).obj
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P) ≅
      (unrestrictedIntegralFiniteComplex l E X n).obj P')
    (b : (isoReductionFiniteComplex l E g n).obj
        ((unrestrictedIntegralFiniteComplex l E Y n).obj Q) ≅
      (unrestrictedIntegralFiniteComplex l E X n).obj Q') :
    ∃ e : (isoReductionIntegralComplex l E g).obj
        ((integralOperationsTensorLevel l E Y n).obj (P, Q)) ≅
      (integralOperationsTensorLevel l E X n).obj (P', Q'),
    ∀ (p q : ℤ) (U : X.ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X p).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q).X q).val.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      ((e.hom.f (p + q)).val.app (op U))
          (integralOperationsTotalTensorSection l E Y n P Q p q
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
        integralOperationsTotalTensorSection l E X n P' Q' p q (op U)
          ((a.hom.f p).val.app (op U) x) ((b.hom.f q).val.app (op U) y) := by
  classical
  obtain ⟨c⟩ := PodReindexingCoherence.comparison_core_tensor_data_exists l E g (some n)
    (CX.finiteClosed n) (CY.finiteClosed n) (CX.finiteTensorModel n) (CY.finiteTensorModel n)
  have hc : (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (podReindexingCoefficient l E g (some n)).hom =
      isoSectionwiseConstantMap.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) :=
    (podReindexingCoefficient_existsUnique l E g).exists.choose_spec.1 n
  let PY := (unrestrictedIntegralFiniteComplex l E Y n).obj P
  let QY := (unrestrictedIntegralFiniteComplex l E Y n).obj Q
  let tY := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
    (integralCoefficientCommRingSheaf l E Y n)
  let tX := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)
  let T (φ : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        (integralCoefficientSheaf l E Y n) ≅ integralCoefficientSheaf l E X n) : Prop :=
    ∃ e₀ : ((isoSectionwiseModuleInverseImage.{u, u} g φ.hom).mapHomologicalComplex
        (.up ℤ)).obj (tY.obj (PY, QY)) ≅
      tX.obj (((isoSectionwiseModuleInverseImage.{u, u} g φ.hom).mapHomologicalComplex
          (.up ℤ)).obj PY,
        ((isoSectionwiseModuleInverseImage.{u, u} g φ.hom).mapHomologicalComplex (.up ℤ)).obj QY),
      ∀ (p q : ℤ) (U : X.ProEt)
        (x : (PY.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (QY.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        ((e₀.hom.f (p + q)).val.app (op U))
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n) PY QY p q (p + q) rfl
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X n)
            (((isoSectionwiseModuleInverseImage.{u, u} g φ.hom).mapHomologicalComplex
              (.up ℤ)).obj PY)
            (((isoSectionwiseModuleInverseImage.{u, u} g φ.hom).mapHomologicalComplex
              (.up ℤ)).obj QY) p q (p + q) rfl (op U) x y
  have hconst : IsIso (isoSectionwiseConstantMap.{u, u} g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    isoSectionwiseConstantMap_isIso.{u, u} g _
  let φconst : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
      (integralCoefficientSheaf l E Y n) ≅ integralCoefficientSheaf l E X n :=
    @asIso _ _ _ _ (isoSectionwiseConstantMap.{u, u} g
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) hconst
  have chain : ∃ e₀ : (isoReductionFiniteComplex l E g n).obj (tY.obj (PY, QY)) ≅
      tX.obj ((isoReductionFiniteComplex l E g n).obj PY,
        (isoReductionFiniteComplex l E g n).obj QY),
      ∀ (p q : ℤ) (U : X.ProEt)
        (x : (PY.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (QY.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        ((e₀.hom.f (p + q)).val.app (op U))
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n) PY QY p q (p + q) rfl
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X n)
            ((isoReductionFiniteComplex l E g n).obj PY)
            ((isoReductionFiniteComplex l E g n).obj QY) p q (p + q) rfl (op U) x y := by
    change T φconst
    have hpod : T ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g (some n))) :=
      ⟨c.tensorChain PY QY,
        fun p q U x y ↦ c.tensorChain_pure PY QY p q (p+q) rfl U x y⟩
    have hi : (sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (podReindexingCoefficient l E g (some n)) = φconst := by
      apply Iso.ext
      exact hc
    exact hi ▸ hpod
  obtain ⟨e₀, he₀⟩ := chain
  let R := (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)
  let s := (isoReduction_restrictionSquare l E g n).choose
  let : (isoReductionIntegralInverse l E g).Additive :=
    (isoSectionwiseModuleInverseImage_exact g (isoReductionCompletedMap l E g).hom).1
  let : (isoReductionFiniteInverse l E g n).Additive :=
    (isoSectionwiseModuleInverseImage_exact g
      (isoSectionwiseConstantMap.{u, u} g
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).1
  let sC := Functor.mapHomologicalComplexCompIso s (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n))
      (.up ℤ)).symm
  let e : (isoReductionIntegralComplex l E g).obj
        ((integralOperationsTensorLevel l E Y n).obj (P, Q)) ≅
      (integralOperationsTensorLevel l E X n).obj (P', Q') :=
    sC.app (tY.obj (PY, QY)) ≪≫ R.mapIso e₀ ≪≫
      R.mapIso (tX.mapIso (Iso.prod a b))
  refine ⟨e, ?_⟩
  intro p q U x y
  change (((tX.map (Prod.mkHom a.hom b.hom)).f (p + q)).val.app (op U))
      (((e₀.hom.f (p + q)).val.app (op U))
        (((s.hom.app ((tY.obj (PY, QY)).X (p + q))).val.app (op U))
          (integralOperationsTotalTensorSection l E Y n P Q p q
            (op ((proEtaleIsoPostcompose g).obj U)) x y))) = _
  have hs := (isoReduction_restrictionSquare l E g n).choose_spec
    ((tY.obj (PY, QY)).X (p + q)) (op U)
    (integralOperationsTotalTensorSection l E Y n P Q p q
      (op ((proEtaleIsoPostcompose g).obj U)) x y)
  have hY := finiteTensorGenerator_eq l E Y P Q n p q
    (op ((proEtaleIsoPostcompose g).obj U)) x y
  have hX := finiteTensorGenerator_eq l E X P' Q' n p q (op U)
    ((a.hom.f p).val.app (op U) x) ((b.hom.f q).val.app (op U) y)
  let m := ((tX.map (Prod.mkHom a.hom b.hom)).f (p + q)).val.app (op U)
  let f := (e₀.hom.f (p + q)).val.app (op U)
  exact (congrArg (fun z ↦ m (f z)) hs).trans
    ((congrArg (fun z ↦ m (f z)) hY.symm).trans
      ((congrArg (fun z ↦ m z) (he₀ p q U x y)).trans
        ((CategoryTheory.ScalarHomTensor.tensor_generator_map a.hom b.hom
          p q (p + q) rfl (op U) x y).trans hX)))

/-- A normalized tensor comparison at one finite coefficient level.
Source: blueprint `theorem-poincare-duality-frobenius--2`, Steps 1 and 5;
Stacks 03EL, 012Z, 07A4 (blueprint: lem-pod-reindexing-finite-tensor-comparison).
Proof: instantiate the finite closed models in the preceding parameterized argument.
The result uses only the sectionwise tensor comparison and the two given finite
chain isomorphisms. It requires no coherence between coefficient levels.
-/
theorem podReindexingFiniteTensorComparison
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E Y) ℤ)
    (P' Q' : CochainComplex (integralTowerModules l E X) ℤ)
    (a : (isoReductionFiniteComplex l E g n).obj
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P) ≅
      (unrestrictedIntegralFiniteComplex l E X n).obj P')
    (b : (isoReductionFiniteComplex l E g n).obj
        ((unrestrictedIntegralFiniteComplex l E Y n).obj Q) ≅
      (unrestrictedIntegralFiniteComplex l E X n).obj Q') :
    ∃ e : (isoReductionIntegralComplex l E g).obj
        ((integralOperationsTensorLevel l E Y n).obj (P, Q)) ≅
      (integralOperationsTensorLevel l E X n).obj (P', Q'),
    ∀ (p q : ℤ) (U : X.ProEt)
      (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X p).val.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q).X q).val.obj
        (op ((proEtaleIsoPostcompose g).obj U))),
      ((e.hom.f (p + q)).val.app (op U))
          (integralOperationsTotalTensorSection l E Y n P Q p q
            (op ((proEtaleIsoPostcompose g).obj U)) x y) =
        integralOperationsTotalTensorSection l E X n P' Q' p q (op U)
          ((a.hom.f p).val.app (op U) x) ((b.hom.f q).val.app (op U) y) := by
  exact podReindexingFiniteTensorComparison_withModels l E g n
    (coefficientDerivedSystemEvaluationCalculus l E X).choose
    (coefficientDerivedSystemEvaluationCalculus l E Y).choose P Q P' Q' a b

end WeilConjectures
