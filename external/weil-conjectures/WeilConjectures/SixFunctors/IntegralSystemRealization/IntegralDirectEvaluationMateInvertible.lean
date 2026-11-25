/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricEvaluationMate
import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange

/-! # Invertibility of canonical system evaluation mate

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 0941
(blueprint: lem-sf-integral-direct-evaluation-mate-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived

private noncomputable def evaluationExtension (W : Scheme.{u}) (n : ℕ) :
    SheafOfModules.SystemDerivedLeftExtension (coefficientSequenceEvaluation l E W n)
      (SheafOfModules.systemLevelKFlat.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n) := by
  exact SemilinearSections.singletonModel.{u + 1, u, u + 1} (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W) n

private def ordinaryEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorSequenceInverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f :=
  (pullbackTensorSequenceInverseEvaluation l E f n).symm ≪≫
    Functor.isoWhiskerLeft _ (pullbackTensorLevelIntrinsic l E f n)

private theorem intrinsicComparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorLevelIntrinsic l E f n =
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).leftAdjointUniq
        (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) := by
  apply (pullbackTensorLevelIntrinsic_existsUnique l E f n).unique
    (pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose_spec
  intro M U x
  exact congrArg (fun a ↦ a.val.app (op U) x)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))))
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) M)

private theorem finiteGood {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : SheafOfModules.systemLevelKFlat.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSystem l E Y) n P) :
    SheafOfModules.systemLevelKFlat.{u + 1, u, u + 1}
      (coefficientSequenceCommRingSystem l E X) n
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  let A := finiteCoefficientRing l E (n + 1)
  have h := (proEtaleTensorPullbackDescentData f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (proEtaleConstantRingComparison f A)).1 P hP
  let e := (NatIso.mapHomologicalComplex (openSquarePullbackModel A f) (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent _ e h.1,
    fun i ↦ SheafOfModules.flatOnSite_of_iso _
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso e) (h.2 i)⟩

private theorem ordinaryMate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (mateEquiv (pullbackTensorSequenceAdjunction l E f)
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
      (TwoSquare.mk _ _ _ _ (ordinaryEvaluation l E f n).inv)) := by
  let a := pullbackTensorSequenceAdjunction l E f
  let b := sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))
  let b₀ := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
  let β := pullbackTensorSequenceDirectEvaluation l E f n
  let R := proEtaleConstantModuleDirectImage f (finiteCoefficientRing l E (n + 1))
  have he : (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom) =
      TwoSquare.mk _ _ _ _ (ordinaryEvaluation l E f n).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    erw [← unit_mateEquiv_symm]
    dsimp only [ordinaryEvaluation, Iso.trans_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv]
    rw [intrinsicComparison_eq, Adjunction.homEquiv_unit]
    let Z := (coefficientSequenceEvaluation l E Y n).obj M
    have hu : b.unit.app Z ≫ R.map ((b₀.leftAdjointUniq b).inv.app Z) =
        b₀.unit.app Z := by
      have h₀ : b₀.unit.app Z ≫ R.map ((b₀.leftAdjointUniq b).hom.app Z) =
          b.unit.app Z := Adjunction.unit_leftAdjointUniq_hom_app b₀ b Z
      have h := congrArg
        (fun z ↦ z ≫ R.map ((b₀.leftAdjointUniq b).inv.app Z)) h₀
      have h₁ := h.symm
      simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h₁
      erw [R.map_id, Category.comp_id] at h₁
      exact h₁
    rw [Functor.map_comp, ← Category.assoc, hu]
    exact ((pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose_spec
      M).symm
  have hh := congrArg (mateEquiv a b) he
  rw [Equiv.apply_symm_apply] at hh
  rw [← hh]
  infer_instance

private theorem derivedEvaluation_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
    let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
    Functor.mapDerivedCategorySquareIso (ordinaryEvaluation l E f n) =
      pullbackTensorDerivedEvaluation l E f n := by
  let := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  apply (pullbackTensorDerivedEvaluation_existsUnique l E f n).unique
  · unfold pullbackTensorDerivedEvaluationNormalization
    intro P
    have h := exactSquare_fac (ordinaryEvaluation l E f n) P
    have hc : (((ordinaryEvaluation l E f n).hom.mapHomologicalComplex (.up ℤ)).app P) =
        (pullbackTensorInverseEvaluationComplex l E f n).inv.app P ≫
          (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
            (.up ℤ)).hom.app
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P) := by
      apply HomologicalComplex.hom_ext
      intro i
      simp only [ordinaryEvaluation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        NatTrans.mapHomologicalComplex_app_f, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, pullbackTensorInverseEvaluationComplex, Iso.trans_inv,
        Iso.symm_inv]
      let α := (pullbackTensorSequenceInverseEvaluation l E f n).inv.app (P.X i)
      let β := (pullbackTensorLevelIntrinsic l E f n).hom.app
        ((coefficientSequenceEvaluation l E Y n).obj (P.X i))
      change α ≫ β = 𝟙 _ ≫ α ≫ 𝟙 _ ≫ β
      simp only [Category.id_comp]
    rw [hc, Functor.map_comp] at h
    exact h
  · exact (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec

/-- The canonical right mate of normalized pullback evaluation is invertible.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0941 and 07A7
(blueprint: lem-sf-integral-direct-evaluation-mate-invertible).

Proof: use the normalized derived finite-extension left adjoints to evaluation.
The ordinary inverse-image square has as right mate the canonical direct-image
comparison, by its unit normalization and uniqueness of intrinsic pullback.
Iterated mates therefore make the ordinary finite-extension mate invertible.
Intrinsic finite pullback preserves flat-term K-flat complexes, by the ringed
pullback theorem and the normalized constant-ring realization comparison.
The normalized extension-mate theorem now makes the derived extension mate
invertible. Its underlying derived square has exactly the cochain normalization
of pullbackTensorDerivedEvaluation, so uniqueness identifies the specified maps.
Finally iterated mates express the required right mate as the conjugate of
that invertible derived extension mate, using d.adj with its fixed left adjoint.
This applies to every system, including zero and n = 0; no flatness of the
quotient ring, boundedness or cartesianness is used. -/
theorem integralDirectEvaluationMate_invertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : Direct l E f) (n : ℕ) :
    IsIso (mateEquiv d.adj (finiteAdj l E f n)
      (TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f n).inv)) := by
  let d₁ := evaluationExtension l E Y n
  let d₂ := evaluationExtension l E X n
  let G := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  let : G.Additive := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  let : PreservesFiniteLimits G :=
    sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  let : PreservesFiniteColimits G :=
    sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let H := pullbackTensorSequenceInverse l E f
  let δ := (ordinaryEvaluation l E f n).symm
  let δD := (pullbackTensorDerivedEvaluation l E f n).symm
  let a := ((mateEquiv d₁.ordinaryAdj d₂.ordinaryAdj).symm
    (TwoSquare.mk _ _ _ _ δ.hom))
  have ha : IsIso a := by
    have h := iterated_mateEquiv_conjugateEquiv d₁.ordinaryAdj d₂.ordinaryAdj
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
      (pullbackTensorSequenceAdjunction l E f)
      ((mateEquiv d₁.ordinaryAdj d₂.ordinaryAdj).symm
        (TwoSquare.mk _ _ _ _ δ.hom))
    rw [Equiv.apply_symm_apply] at h
    have hi : IsIso (conjugateEquiv
        (d₁.ordinaryAdj.comp (pullbackTensorSequenceAdjunction l E f))
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).comp d₂.ordinaryAdj) a) := by
      rw [← h]
      exact ordinaryMate l E f n
    exact conjugateEquiv_of_iso
      (d₁.ordinaryAdj.comp (pullbackTensorSequenceAdjunction l E f))
      ((sfIntrinsicConstantModuleAdjunction f
        (finiteCoefficientRing l E (n + 1))).comp d₂.ordinaryAdj) a
  let aD := ((mateEquiv d₁.adjunction d₂.adjunction).symm
    (TwoSquare.mk _ _ _ _ δD.hom))
  have haD : IsIso aD := by
    refine SheafOfModules.derivedExtensionMate_isIso d₁ d₂ G H G.mapDerivedCategory
      G.mapDerivedCategoryFactors δD.hom δ.hom ?_
      (@asIso _ _ _ _ a ha) ?_
      (SheafOfModules.systemLevel_kFlatResolution
        (coefficientSequenceCommRingSystem l E Y) n) (finiteGood l E f n)
    · intro K
      have hδ : δD.hom = (Functor.mapDerivedCategorySquareIso δ).hom := by
        change (pullbackTensorDerivedEvaluation l E f n).inv = _
        rw [← derivedEvaluation_eq l E f n]
        simp only [δ, Functor.mapDerivedCategorySquareIso, Iso.symm_hom,
          Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
          Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
      rw [hδ]
      exact exactSquare_fac δ K
    · intro P
      exact (unit_mateEquiv_symm d₁.ordinaryAdj d₂.ordinaryAdj
        (TwoSquare.mk _ _ _ _ δ.hom) P).symm
  have h := iterated_mateEquiv_conjugateEquiv d₁.adjunction d₂.adjunction
    (finiteAdj l E f n) d.adj
    ((mateEquiv d₁.adjunction d₂.adjunction).symm
      (TwoSquare.mk _ _ _ _ δD.hom))
  rw [Equiv.apply_symm_apply] at h
  change IsIso (mateEquiv d.adj (finiteAdj l E f n)
    (TwoSquare.mk _ _ _ _ δD.hom))
  rw [h]
  infer_instance

end WeilConjectures.IntegralSystemRealization
