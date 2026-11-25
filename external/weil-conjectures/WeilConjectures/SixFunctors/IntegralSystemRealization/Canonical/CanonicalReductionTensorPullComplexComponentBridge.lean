/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SixFunctors.GeneratorReduction.PullQuotientOrdinaryProjectionSection
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.SmoothPurity.ProEtale.ProEtaleTotalTensorPullbackGenerators

/-! # Finite-evaluation bridge for the ordinary reduction/tensor pullback component

Source: Stacks 07A4, 07A6 and 0941; proposition-six-operations-change-coefficients, first paragraph.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] constantSheaf Functor.leftAdjoint presheafToSheaf
  proEtaleRingModulePullback pullbackTensorSequenceRing
  pullbackTensorSequenceInverse OrdinaryLimitModel.reductionPull
  completedIntegralCommRingProjectionUnrestricted
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem
attribute [local irreducible] pullbackTensorCalculus HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  SheafOfModules.monoidalCategory coefficientTensorGenerator
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local implicit_reducible] PurCompactSupport.completed
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceEvaluation pullbackTensorSequenceDirect pullbackTensorSequenceBase
  pullbackTensorOrdinaryLimit
attribute [local irreducible] pullbackTensorOrdinaryReduction
  pullbackTensorOrdinaryAdjunction pullbackTensorSequenceAdjunction
  coefficientSequenceRestriction
-- The actual reduction unit, projected to one quotient level.
private noncomputable def redUnit (W : Scheme.{u}) (M : integralTowerModules l E W)
    (n : ℕ) (V : W.ProEt) (x : M.val.obj (op V)) :
    ((pullbackTensorOrdinaryReduction l E W).obj M).val.obj (op (n, V)) :=
  ordinaryLimitProjection l E W _ n V
    (((pullbackTensorOrdinaryAdjunction l E W).unit.app M).val.app (op V) x)
private theorem redUnit_map (W : Scheme.{u}) {M N : integralTowerModules l E W}
    (k : M ⟶ N) (n : ℕ) (V : W.ProEt) (x : M.val.obj (op V)) :
    ((pullbackTensorOrdinaryReduction l E W).map k).val.app (op (n, V))
        (redUnit l E W M n V x) =
      redUnit l E W N n V (k.val.app (op V) x) := by
  have hp := GeneratorReduction.projection_map l E W
    ((pullbackTensorOrdinaryReduction l E W).map k) n V
    (((pullbackTensorOrdinaryAdjunction l E W).unit.app M).val.app (op V) x)
  have h := congrArg (fun t ↦ t.val.app (op V) x)
    ((pullbackTensorOrdinaryAdjunction l E W).unit.naturality k)
  exact hp.symm.trans (congrArg (ordinaryLimitProjection l E W _ n V) h.symm)

private theorem redUnit_eval (W : Scheme.{u}) (M : integralTowerModules l E W)
    (n : ℕ) (V : W.ProEt) (x : M.val.obj (op V)) :
    redUnit l E W M n V x =
      ((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app (op V)
        (coefficientIntegralScalarUnitSection l E W n M (op V) x) := by
  exact GeneratorReduction.projection_unit l E W M n V x

-- The canonical mate on the successive geometric and reduction units.
private theorem mate_redUnit (a : OrdinaryLimitModel l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (n : ℕ) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((a.reductionPull l E f).hom.app M).val.app
        (op (n, (proEtaleBaseChange f).obj V))
        (redUnit l E X ((integralOrdinaryPull l E f).obj M) n
          ((proEtaleBaseChange f).obj V)
          (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x)) =
      (((pullbackTensorSequenceAdjunction l E f).unit.app
        ((pullbackTensorOrdinaryReduction l E Y).obj M)).val.app (op (n, V)))
        (redUnit l E Y M n V x) := by
  let M₀ := (pullbackTensorOrdinaryReduction l E Y).obj M
  let N := (pullbackTensorSequenceInverse l E f).obj M₀
  let η := (pullbackTensorSequenceAdjunction l E f).unit.app M₀
  let x' := (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).unit.app M).val.app (op V) x)
  let d := ((pullbackTensorSequenceDirectEvaluation l E f n).hom.app N).val.app (op V)
  have hm := GeneratorReduction.mate_projection l E a f M n V x
  have hp := GeneratorReduction.projection_map l E Y η n V
    (((pullbackTensorOrdinaryAdjunction l E Y).unit.app M).val.app (op V) x)
  have hd := (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose_spec
    N V (((coefficientSequenceEvaluation l E Y n).map η).val.app (op V)
      (redUnit l E Y M n V x))
  have ha := GeneratorReduction.projection_map l E X
    ((a.reductionPull l E f).hom.app M) n ((proEtaleBaseChange f).obj V)
    (((pullbackTensorOrdinaryAdjunction l E X).unit.app
      ((integralOrdinaryPull l E f).obj M)).val.app
      (op ((proEtaleBaseChange f).obj V)) x')
  exact ha.symm.trans (hm.trans ((congrArg d hp).trans (eq_of_heq hd)))

-- Transpose twice and use the limit projections and homogeneous total generators.
private theorem reduction_pull_total_ext
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (integralTowerModules l E Y) ℤ) (k : ℤ)
    (N : coefficientSequenceModules l E X)
    (α β : (pullbackTensorOrdinaryReduction l E X).obj
      ((integralOrdinaryPull l E f).obj
        (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology Y)
          (completedIntegralCommRingSheafUnrestricted l E Y)).obj (P, Q)).X k)) ⟶ N)
    (h : ∀ (p q : ℤ) (hpq : p + q = k) (m : ℕ) (V : Y.ProEt)
      (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
      α.val.app (op (m, (proEtaleBaseChange f).obj V))
        (redUnit l E X _ m ((proEtaleBaseChange f).obj V)
          (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).unit.app _).val.app (op V)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq (op V) x y))) =
      β.val.app (op (m, (proEtaleBaseChange f).obj V))
        (redUnit l E X _ m ((proEtaleBaseChange f).obj V)
          (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull f)).unit.app _).val.app (op V)
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
              (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq (op V) x y)))) :
    α = β := by
  apply ((pullbackTensorOrdinaryAdjunction l E X).homEquiv _ _).injective
  apply limit.hom_ext
  intro m
  apply (cancel_mono
    ((eqToIso (coefficientSequenceRestriction_evaluation l E X m.unop)).hom.app N)).1
  apply ((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).homEquiv _ _).injective
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    (J := ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) P Q k _
  intro p q hpq V x y
  change ordinaryLimitProjection l E X N m.unop ((proEtaleBaseChange f).obj V.unop)
      (((pullbackTensorOrdinaryAdjunction l E X).homEquiv _ _ α).val.app _
        (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X)
          ((PurCompactSupport.completed l E).pull f)).unit.app _).val.app V
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
            (completedIntegralCommRingSheafUnrestricted l E Y) P Q p q k hpq V x y))) = _
  simp only [Adjunction.homEquiv_unit]
  change ordinaryLimitProjection l E X N _ _
      (((pullbackTensorOrdinaryLimit l E X).map α).val.app _ _) =
    ordinaryLimitProjection l E X N _ _
      (((pullbackTensorOrdinaryLimit l E X).map β).val.app _ _)
  rw [GeneratorReduction.projection_map, GeneratorReduction.projection_map]
  exact h p q hpq m.unop V.unop x y

attribute [local irreducible] redUnit
  pullbackTensorReductionEvaluation pullbackTensorReductionEvaluationComplex
  tensorReductionStrictMap coefficientScalarTensorIso
  coefficientEvaluationTensorIso

-- The finite-component characterizations determine strict reduction on generators.
private theorem reduction_tensor_generators (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (hm : ∀ m : ℕ,
      ((coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E W P Q) = tensorReductionFiniteComponent l E W P Q m)
    (p q k : ℤ) (h : p + q = k) (m : ℕ) (V : W.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    ((tensorReductionStrictMap l E W P Q).f k).val.app (op (m, V))
      (redUnit l E W _ m V
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k h (op V) x y)) =
    coefficientTensorGenerator.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
      (R.obj P) (R.obj Q) p q k h (op (m, V))
      (redUnit l E W (P.X p) m V x) (redUnit l E W (Q.X q) m V y) := by
  dsimp only
  let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let e := coefficientEvaluationTensorIso l E W m (R.obj P) (R.obj Q)
  have hinj : Function.Injective ((e.hom.f k).val.app (op V)) := by
    have hi (z) := congrArg (fun t ↦ (t.f k).val.app (op V) z) e.hom_inv_id
    intro z z' hz
    exact (hi z).symm.trans ((congrArg ((e.inv.f k).val.app (op V)) hz).trans (hi z'))
  apply hinj
  let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let c := pullbackTensorReductionEvaluationComplex l E W m
  let d := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W m)).map
      (Prod.mkHom (c.hom.app P) (c.hom.app Q))
  have hh : c.hom.app T ≫
      ((coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E W P Q) ≫ e.hom =
      (coefficientScalarTensorIso l E W m P Q).hom ≫ d := by
    rw [hm m]
    unfold tensorReductionFiniteComponent
    change c.hom.app T ≫ c.inv.app T ≫
      (coefficientScalarTensorIso l E W m P Q).hom ≫ d ≫ e.inv ≫ e.hom = _
    rw [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id]
    exact congrArg ((coefficientScalarTensorIso l E W m P Q).hom ≫ ·) (Category.comp_id d)
  have hcf (A : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ) :
      (c.hom.app A).f i = (pullbackTensorReductionEvaluation l E W m).hom.app (A.X i) := by
    unfold c pullbackTensorReductionEvaluationComplex
    simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_hom_app_f]
    change (pullbackTensorReductionEvaluation l E W m).hom.app (A.X i) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hs : CoefficientScalarTensorGenerators.{u, u + 1, u} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      (integralCoefficientCommRingSheaf l E W m) (scalarReductionExtension l E W m)
      (hF := coefficientFiniteExtensionAdditive l E W m)
      (coefficientIntegralScalarUnitSection l E W m) P Q
      (coefficientScalarTensorIso l E W m P Q) := by
    unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
    exact (coefficientScalarTensorIso_exists l E W m P Q).choose_spec.1
  have he : (e.hom.f k).val.app (op V)
      (coefficientEvaluationSection l E W _ m (op V)
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (R.obj P) (R.obj Q)
          p q k h (op (m, V)) (redUnit l E W (P.X p) m V x)
          (redUnit l E W (Q.X q) m V y))) =
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W m)
      (((coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).obj (R.obj P))
      (((coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).obj (R.obj Q))
      p q k h (op V)
      (coefficientEvaluationSection l E W _ m (op V) (redUnit l E W (P.X p) m V x))
      (coefficientEvaluationSection l E W _ m (op V) (redUnit l E W (Q.X q) m V y)) := by
    unfold e coefficientEvaluationTensorIso coefficientUniqueComparisonChoice
    exact (coefficientEvaluationTensorIso_exists l E W m (R.obj P) (R.obj Q)).choose_spec.1
      p q k h (op V) _ _
  have hu (A : CochainComplex (integralTowerModules l E W) ℤ) (i : ℤ)
      (z : (A.X i).val.obj (op V)) :
      ((c.hom.app A).f i).val.app (op V)
          (coefficientIntegralScalarUnitSection l E W m (A.X i) (op V) z) =
        redUnit l E W (A.X i) m V z := by
    exact (congrArg (fun t ↦ t.val.app (op V)
      (coefficientIntegralScalarUnitSection l E W m (A.X i) (op V) z)) (hcf A i)).trans
        (redUnit_eval l E W (A.X i) m V z).symm
  let g := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k h (op V) x y
  have hz := congrArg (fun t ↦ (t.f k).val.app (op V)
    (coefficientIntegralScalarUnitSection l E W m (T.X k) (op V) g)) hh
  change (e.hom.f k).val.app (op V)
    (((tensorReductionStrictMap l E W P Q).f k).val.app (op (m, V))
      (((c.hom.app T).f k).val.app (op V) _)) =
    (d.f k).val.app (op V) (((coefficientScalarTensorIso l E W m P Q).hom.f k).val.app
      (op V) _) at hz
  have hzt := congrArg (fun z ↦ (e.hom.f k).val.app (op V)
    (((tensorReductionStrictMap l E W P Q).f k).val.app (op (m, V)) z)) (hu T k g)
  refine (hzt.symm.trans hz).trans ?_
  have hs' := congrArg ((d.f k).val.app (op V)) (hs p q k h (op V) x y)
  refine hs'.trans ?_
  have hg := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (J := ProEt.topology W) (R := integralCoefficientCommRingSheaf l E W m)
    (c.hom.app P) (c.hom.app Q) p q k h (op V)
    (coefficientIntegralScalarUnitSection l E W m (P.X p) (op V) x)
    (coefficientIntegralScalarUnitSection l E W m (Q.X q) (op V) y)
  refine hg.trans ?_
  have hu' := congrArg₂ (fun x y ↦ coefficientTensorGenerator.{u, u + 1, u}
    (ProEt.topology W) (integralCoefficientCommRingSheaf l E W m)
    (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).obj P)
    (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E W m).mapHomologicalComplex (.up ℤ)).obj Q)
    p q k h (op V) x y) (hu P p x) (hu Q q y)
  exact hu'.trans he.symm

/--
The finite-evaluation equations for the strict reduction maps are sufficient for
one degree of the ordinary reduction/tensor pullback square.  This is the
finite-level bridge used to assemble the degreewise identity; its proof is the
pure-tensor calculation together with the normalized unit formula for the
sequence pullback tensor comparison.

Source: Stacks 07A4, 07A6 and 0941; the first paragraph of
`proposition-six-operations-change-coefficients`, after finite evaluation and before cochain
extensionality.  The two hypotheses are exactly the finite-component
characterizations of `tensorReductionStrictMap` at the source and target.
(blueprint: lem-sf-canonical-reduction-tensor-pull-complex-component-bridge).
-/
theorem canonicalReductionTensorPullComplex_component_bridge
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (a : OrdinaryLimitModel l E) {U V : Scheme.{u}} (f : U ⟶ V)
    (P Q : CochainComplex (integralTowerModules l E V) ℤ) (n : ℤ)
    (hV : ∀ m : ℕ,
      ((coefficientSequenceEvaluation l E V m).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E V P Q) =
        tensorReductionFiniteComponent l E V P Q m)
    (hU : ∀ m : ℕ,
      ((coefficientSequenceEvaluation l E U m).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E U
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q)) =
        tensorReductionFiniteComponent l E U
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q) m) :
    let F := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
    let R (W : Scheme.{u}) :=
      (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let S := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology V)
      (completedIntegralCommRingSheafUnrestricted l E V)).obj (P, Q)
    (a.reductionPullComplex l E f T ≫
        S.map (tensorReductionStrictMap l E V P Q) ≫
        (pullbackTensorSequenceCochain l E f).hom.app ((R V).obj P, (R V).obj Q)).f n =
      ((R U).map
          (proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring V)
            ((PurCompactSupport.completed l E).ring U)
            ((PurCompactSupport.completed l E).pull f) P Q).inv ≫
        tensorReductionStrictMap l E U (F.obj P) (F.obj Q) ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology U))
          (coefficientSequenceCommRingSheaf l E U)).map
          (Prod.mkHom (a.reductionPullComplex l E f P)
            (a.reductionPullComplex l E f Q))).f n := by
  intro F R S T
  apply reduction_pull_total_ext l E f P Q n
  intro p q hpq m W x y
  let W' := (proEtaleBaseChange f).obj W
  let z := redUnit l E U ((integralOrdinaryPull l E f).obj (T.X n)) m W'
    (((proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring V)
      ((PurCompactSupport.completed l E).ring U)
      ((PurCompactSupport.completed l E).pull f)).unit.app (T.X n)).val.app (op W)
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology V)
          (completedIntegralCommRingSheafUnrestricted l E V) P Q p q n hpq (op W) x y))
  change (((pullbackTensorSequenceCochain l E f).hom.app
      ((R V).obj P, (R V).obj Q)).f n).val.app (op (m, W'))
      (((pullbackTensorSequenceInverse l E f).map
        ((tensorReductionStrictMap l E V P Q).f n)).val.app (op (m, W'))
          (((a.reductionPull l E f).hom.app (T.X n)).val.app (op (m, W')) z)) =
    (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology U))
      (coefficientSequenceCommRingSheaf l E U)).map
        (Prod.mkHom (a.reductionPullComplex l E f P)
          (a.reductionPullComplex l E f Q))).f n).val.app (op (m, W'))
      (((tensorReductionStrictMap l E U (F.obj P) (F.obj Q)).f n).val.app (op (m, W'))
        (((pullbackTensorOrdinaryReduction l E U).map
          ((proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring V)
            ((PurCompactSupport.completed l E).ring U)
            ((PurCompactSupport.completed l E).pull f) P Q).inv.f n)).val.app (op (m, W')) z))
  let c := (((pullbackTensorSequenceCochain l E f).hom.app
    ((R V).obj P, (R V).obj Q)).f n).val.app (op (m, W'))
  let s := (((pullbackTensorSequenceInverse l E f).map
    ((tensorReductionStrictMap l E V P Q).f n)).val.app (op (m, W')))
  let d := (((coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology U))
    (coefficientSequenceCommRingSheaf l E U)).map
      (Prod.mkHom (a.reductionPullComplex l E f P)
        (a.reductionPullComplex l E f Q))).f n).val.app (op (m, W'))
  let t := ((tensorReductionStrictMap l E U (F.obj P) (F.obj Q)).f n).val.app (op (m, W'))
  let g := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology V)
    (completedIntegralCommRingSheafUnrestricted l E V) P Q p q n hpq (op W) x y
  let η := proEtaleRingModuleAdjunction f ((PurCompactSupport.completed l E).ring V)
    ((PurCompactSupport.completed l E).ring U) ((PurCompactSupport.completed l E).pull f)
  let x' := (η.unit.app (P.X p)).val.app (op W) x
  let y' := (η.unit.app (Q.X q)).val.app (op W) y
  have hmT := mate_redUnit l E a f (T.X n) m W g
  have hn := congrArg (fun t ↦ t.val.app (op (m, W))
    (redUnit l E V (T.X n) m W g))
    ((pullbackTensorSequenceAdjunction l E f).unit.naturality
      ((tensorReductionStrictMap l E V P Q).f n))
  have hsV := reduction_tensor_generators l E V P Q hV p q n hpq m W x y
  let ηS := (pullbackTensorSequenceAdjunction l E f).unit.app
    (((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology V))
      (coefficientSequenceCommRingSheaf l E V)).obj ((R V).obj P, (R V).obj Q)).X n)
  have hc := (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
    ((R V).obj P) ((R V).obj Q) p q n hpq (m, W)
    (redUnit l E V (P.X p) m W x) (redUnit l E V (Q.X q) m W y)
  have hleft := (congrArg (fun z ↦ c (s z)) hmT).trans
    ((congrArg c (hn.symm.trans (congrArg (ηS.val.app (op (m, W))) hsV))).trans hc)
  have hrmap := redUnit_map l E U
    ((proEtaleTensorPullbackTotalIso f ((PurCompactSupport.completed l E).ring V)
      ((PurCompactSupport.completed l E).ring U)
      ((PurCompactSupport.completed l E).pull f) P Q).inv.f n) m W'
    ((η.unit.app (T.X n)).val.app (op W) g)
  have hgeo := proEtaleTensorPullbackTotal_generators f
    ((PurCompactSupport.completed l E).ring V) ((PurCompactSupport.completed l E).ring U)
    ((PurCompactSupport.completed l E).pull f) P Q p q n hpq W x y
  have harg := hrmap.trans (congrArg (redUnit l E U _ m W') hgeo)
  have hsU := reduction_tensor_generators l E U (F.obj P) (F.obj Q) hU
    p q n hpq m W' x' y'
  have ht := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
    (J := coefficientSequenceTopology (ProEt.topology U))
    (R := coefficientSequenceCommRingSheaf l E U)
    (a.reductionPullComplex l E f P) (a.reductionPullComplex l E f Q)
    p q n hpq (op (m, W'))
    (redUnit l E U ((F.obj P).X p) m W' x')
    (redUnit l E U ((F.obj Q).X q) m W' y')
  have hp := mate_redUnit l E a f (P.X p) m W x
  have hq := mate_redUnit l E a f (Q.X q) m W y
  have hlast := congrArg₂ (fun x y ↦ coefficientTensorGenerator.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology U))
    (coefficientSequenceCommRingSheaf l E U)
    (S.obj ((R V).obj P)) (S.obj ((R V).obj Q)) p q n hpq (op (m, W')) x y) hp hq
  have hright := (congrArg (fun z ↦ d (t z)) harg).trans
    ((congrArg d hsU).trans (ht.trans hlast))
  exact hleft.trans hright.symm

end WeilConjectures.IntegralSystemRealization
