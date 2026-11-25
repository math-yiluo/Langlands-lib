/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedFiniteModuleComparison
import WeilConjectures.SixFunctors.RamifiedPullback.FinitePullbackTransitionGenerators
import WeilConjectures.SixFunctors.RamifiedPullback.TensorProof.RamifiedFiniteTensorSections
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Normalized ramified finite pullback comparison

Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze 6.8.2(1).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralReductionFunctor unrestrictedIntegralTransition
  integralOperationsPullbackTransition
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback
  Functor.leftAdjoint scalarWitness

private theorem finitePullbackModule_map_tensor {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ)
    {M N : integralTowerModules l E Y} (f : M ⟶ N) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : M.val.obj (op V)) :
    ((finitePullbackModule l E g n).map f).val.app _
      (finitePullbackModuleTensor l E g n M V a b p) =
      finitePullbackModuleTensor l E g n N V a b (f.val.app (op V) p) := by
  have h := congrArg (fun k ↦ k.val.app (op V)
      (unrestrictedIntegralTensorSection l E Y n M (op V) a p))
    ((integralOperationsPullbackAdjunction l E g n).unit.naturality
      ((unrestrictedIntegralReductionFunctor l E Y n).map f))
  have hr : ((unrestrictedIntegralReductionFunctor l E Y n).map f).val.app (op V)
      (unrestrictedIntegralTensorSection l E Y n M (op V) a p) =
        unrestrictedIntegralTensorSection l E Y n N (op V) a (f.val.app (op V) p) := by
    with_unfolding_all
      exact TensorProof.tensorSection_map
        (completedIntegralCommRingProjectionUnrestricted l E Y n)
        (unrestrictedIntegralReductionFunctor l E Y n) (unrestrictedReduction_obj l E Y n)
        (fun {A B : integralTowerModules l E Y} (f : A ⟶ B) ↦
          unrestrictedReduction_map l E Y n f) f (op V) a p
  change integralOperationsPullbackGenerator l E g n _ V
      (((unrestrictedIntegralReductionFunctor l E Y n).map f).val.app (op V)
        (unrestrictedIntegralTensorSection l E Y n M (op V) a p)) = _ at h
  have h' := h.symm.trans
    (congrArg (integralOperationsPullbackGenerator l E g n _ V) hr)
  change ((integralOperationsLevelPullback l E g n).map
    ((unrestrictedIntegralReductionFunctor l E Y n).map f)).val.app _
      (b • _) = _
  rw [map_smul]
  exact congrArg (fun z ↦ b • z) h'

private theorem scalar_pullback_ext {X Y : Scheme.{t}} (g : X ⟶ Y) (m n : ℕ)
    (c : completedIntegralCommRingSheafUnrestricted l E X ⟶
      completedIntegralCommRingSheafUnrestricted l L X)
    (q : integralCoefficientSheaf l E X m ⟶ integralCoefficientSheaf l L X n)
    (hq : integralOperationsProjection l E X m ≫ q =
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c ≫
          integralOperationsProjection l L X n)
    (M : integralTowerModules l E Y) (N : integralOperationsFiniteModules l L X n)
    (a b : (scalar.{t, u} c).obj ((finitePullbackModule l E g m).obj M) ⟶
      (SheafOfModules.restrictScalars (integralOperationsProjection l L X n)).obj N)
    (hab : ∀ (V : Y.ProEt) (p : M.val.obj (op V)),
      a.val.app _ (tensor.{t, u} c _ _ 1 (finitePullbackModuleTensor l E g m M V 1 1 p)) =
        b.val.app _ (tensor.{t, u} c _ _ 1 (finitePullbackModuleTensor l E g m M V 1 1 p))) :
    a = b := by
  let adj := scalarAdjunction.{t, u} c
  apply (adj.homEquiv _ _).injective
  let π := integralOperationsProjection l E X m
  let β := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map c ≫
      integralOperationsProjection l L X n
  let A := (integralOperationsLevelPullback l E g m).obj
    ((unrestrictedIntegralReductionFunctor l E Y m).obj M)
  let a' : (SheafOfModules.restrictScalars π).obj A ⟶
      (SheafOfModules.restrictScalars β).obj N := adj.homEquiv _ _ a
  let b' : (SheafOfModules.restrictScalars π).obj A ⟶
      (SheafOfModules.restrictScalars β).obj N := adj.homEquiv _ _ b
  let : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) π.hom :=
    completedProjection_locallySurjective l E X m
  let lift := SheafOfModules.IntegralScalarProof.liftMap π β q hq A N
  have hl : lift a' = lift b' := by
    apply ((integralOperationsPullbackAdjunction l E g m).homEquiv _ _).injective
    apply TensorProof.tensorSection_ext
      (completedIntegralCommRingProjectionUnrestricted l E Y m)
      (unrestrictedIntegralReductionFunctor l E Y m) (unrestrictedReduction_obj l E Y m)
    intro V p
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    with_unfolding_all
      change a'.val.app _ (integralOperationsPullbackGenerator l E g m _ V.unop
        (unrestrictedIntegralTensorSection l E Y m M V 1 p)) =
          b'.val.app _ (integralOperationsPullbackGenerator l E g m _ V.unop
            (unrestrictedIntegralTensorSection l E Y m M V 1 p))
    dsimp only [a', b']
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change a.val.app _ ((adj.unit.app _).val.app _ _) =
      b.val.app _ ((adj.unit.app _).val.app _ _)
    dsimp only [adj]
    rw [scalarAdjunction_unit.{t, u} c]
    simpa only [finitePullbackModuleTensor, one_smul, id_eq, Functor.op_obj, op_unop]
      using hab V.unop p
  ext U x
  have hh := congrArg (fun k ↦ k.val.app U x) hl
  exact (SheafOfModules.IntegralScalarProof.liftMap_apply π β q hq A N a' U x).symm.trans
    (hh.trans (SheafOfModules.IntegralScalarProof.liftMap_apply π β q hq A N b' U x))

private theorem ramified_projection_square {X : Scheme.{t}}
    (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (target : Coefficients l E L ι e j X) (n : ℕ) :
    integralOperationsProjection l E X n ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (ramifiedMap l E L X e n (j n)) =
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          target.completedMap ≫ integralOperationsProjection l L X (index e n) := by
  simpa only [Functor.map_comp, integralOperationsProjection] using
    congrArg ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map)
        (target.ramified_projection n).symm

/-- Normalized finite pullback base change, with its adjacent tower square.
Source: Stacks 03EL and 03EK; Bhatt--Scholze 6.8.2(1).
(blueprint: lem-weil-ramified-finite-pullback-comparison).

Proof: The inverse-image tensor comparison identifies the finite pullback with
inverse image of P tensored over the inverse-image completed ring with the finite
coefficient ring on X. Tensor this expression with the completed L ring and
associate the two last factors. The supplied coefficient isomorphism on X identifies
them with the L coefficient quotient. On the other route, pullback of P tensor S_Y
is inverse image of P tensor inverse image of S_Y. Tensoring with the L quotient
cancels that intermediate ring. The inverse balanced maps insert one and multiply
coefficients, so give inverse natural maps for all modules, without flatness.
Naturality makes them commute with differentials and with chain maps. Evaluating
on the two adjunction-unit tensor generators gives the displayed formula. The fixed-level
calculation is finiteModuleComparison_exists. For the adjacent square, it suffices to test
coefficients equal to one. The finite pullback transition
reduces its unit generator, and scalar tensor naturality preserves the inserted unit.
Both routes therefore agree on these generators. The tensor and pullback adjunction
universal properties detect equality, proving the entire square.
-/
theorem finitePullbackComparison_exists {X Y : Scheme.{t}} (g : X ⟶ Y)
    (e : ℕ) (hmono : Monotone (index e))
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (hj : ∀ (n : ℕ) (a : Padic.coefficientExtensionIntegers l E),
      j n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
          (integralScalarIntegerInclusion l E L ι a))
    (source : Coefficients l E L ι e j Y) (target : Coefficients l E L ι e j X) :
    ∃ levelIso : ∀ n : ℕ,
    integralOperationsPullbackLevel l E g n ⋙ scalarCx.{t, u} target.completedMap ≅
      scalarCx.{t, u} source.completedMap ⋙
        integralOperationsPullbackLevel l L g (index e n),
      ( ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)))
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
    (((levelIso n).hom.app P).f i).val.app _
      (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
        _ s (pullTensor l E g n P i V a b p)) =
      pullTensor l L g (index e n) ((scalarCx.{t, u} source.completedMap).obj P) i V
        ((ramifiedMap l E L Y e n (j n)).hom.app (op V) a)
        ((ramifiedMap l E L X e n (j n)).hom.app _ b *
          (completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s)
        (tensor source.completedMap (P.X i) (op V) 1 p)) ∧
      ( ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ),
    (scalarCx.{t, u} target.completedMap).map
        ((integralOperationsPullbackTransition l E g n).app P) ≫
          (levelIso n).hom.app P =
      (levelIso (n + 1)).hom.app P ≫
        transition l L g (index e n) (index e (n + 1)) (hmono (Nat.le_succ n))
          ((scalarCx.{t, u} source.completedMap).obj P)) := by
  classical
  have _quotient_formula := hj
  choose d hd using finiteModuleComparison_exists l E L ι g e j source target
  have hn (n : ℕ) {M N : integralTowerModules l E Y} (f : M ⟶ N) :
      ((finitePullbackModule l E g n) ⋙ scalar target.completedMap).map f ≫ (d n N).hom =
        (d n M).hom ≫
          ((scalar source.completedMap) ⋙ finitePullbackModule l L g (index e n)).map f := by
    apply scalar_pullback_ext l E L g n (index e n) target.completedMap
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (ramifiedMap l E L X e n (j n)))
      (ramified_projection_square l E L ι e j target n)
    intro V p
    change (d n N).hom.val.app _
        (((scalar target.completedMap).map ((finitePullbackModule l E g n).map f)).val.app _
          (tensor target.completedMap _ _ 1
            (finitePullbackModuleTensor l E g n M V 1 1 p))) =
      ((finitePullbackModule l L g (index e n)).map
        ((scalar source.completedMap).map f)).val.app _
          ((d n M).hom.val.app _ (tensor target.completedMap _ _ 1
            (finitePullbackModuleTensor l E g n M V 1 1 p)))
    rw [scalar_map_tensor, finitePullbackModule_map_tensor, hd, hd,
      finitePullbackModule_map_tensor, scalar_map_tensor]
  let levelIso (n : ℕ) :
      integralOperationsPullbackLevel l E g n ⋙ scalarCx target.completedMap ≅
        scalarCx source.completedMap ⋙ integralOperationsPullbackLevel l L g (index e n) :=
    NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ d n (P.X i)) (by
        intro i k hik
        exact (hn n (P.d i k)).symm)) (by
      intro P Q f
      apply HomologicalComplex.hom_ext
      intro i
      exact hn n (f.f i))
  have hformula : ∀ (n : ℕ) (P : CochainComplex (integralTowerModules l E Y) ℤ)
      (i : ℤ) (V : Y.ProEt)
      (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
      (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
        (op ((Scheme.proEtaleBaseChange g).obj V))) (p : (P.X i).val.obj (op V)),
      (((levelIso n).hom.app P).f i).val.app _
        (tensor target.completedMap (((integralOperationsPullbackLevel l E g n).obj P).X i)
          _ s (pullTensor l E g n P i V a b p)) =
        pullTensor l L g (index e n) ((scalarCx source.completedMap).obj P) i V
          ((ramifiedMap l E L Y e n (j n)).hom.app (op V) a)
          ((ramifiedMap l E L X e n (j n)).hom.app _ b *
            (completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s)
          (tensor source.completedMap (P.X i) (op V) 1 p) := by
    intro n P i V a b s p
    exact hd n (P.X i) V a b s p
  refine ⟨levelIso, hformula, ?_⟩
  intro n P
  let F := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let q := integralCoefficientSheafTransition l E X n ≫
    F.map (ramifiedMap l E L X e n (j n))
  have hq : integralOperationsProjection l E X (n + 1) ≫ q =
      F.map target.completedMap ≫ integralOperationsProjection l L X (index e n) := by
    have hs : integralOperationsProjection l E X (n + 1) ≫
        integralCoefficientSheafTransition l E X n = integralOperationsProjection l E X n := by
      with_unfolding_all exact integralProjection_step l E X n
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ F.map (ramifiedMap l E L X e n (j n))) hs).trans
        (ramified_projection_square l E L ι e j target n))
  apply HomologicalComplex.hom_ext
  intro i
  apply scalar_pullback_ext l E L g (n + 1) (index e n) target.completedMap q hq
    (P.X i)
  intro V p
  have htE := pullTensor_transition l E g n (n + 1) (Nat.le_succ n) P i V 1 1 p
  simp only [map_one] at htE
  have htL := pullTensor_transition l L g (index e n) (index e (n + 1))
    (hmono (Nat.le_succ n)) ((scalarCx source.completedMap).obj P) i V 1 1
      (tensor source.completedMap (P.X i) (op V) 1 p)
  simp only [map_one] at htL
  change (((levelIso n).hom.app P).f i).val.app _
      (((scalar target.completedMap).map
        (((integralOperationsPullbackTransition l E g n).app P).f i)).val.app _
          (tensor target.completedMap _ _ 1 (pullTensor l E g (n + 1) P i V 1 1 p))) =
    ((transition l L g (index e n) (index e (n + 1))
      (hmono (Nat.le_succ n)) ((scalarCx source.completedMap).obj P)).f i).val.app _
        ((((levelIso (n + 1)).hom.app P).f i).val.app _
          (tensor target.completedMap _ _ 1 (pullTensor l E g (n + 1) P i V 1 1 p)))
  rw [scalar_map_tensor]
  have htE' : (((integralOperationsPullbackTransition l E g n).app P).f i).val.app _
      (pullTensor l E g (n + 1) P i V 1 1 p) = pullTensor l E g n P i V 1 1 p := by
    simpa only [transition, integralOperationsPullbackTowerFunctor, Functor.flip_obj_map,
      Functor.ofOpSequence_map_homOfLE_succ] using htE
  rw [htE', hformula, hformula]
  simp only [map_one, mul_one]
  exact htL.symm

end WeilConjectures.RamifiedPullback
