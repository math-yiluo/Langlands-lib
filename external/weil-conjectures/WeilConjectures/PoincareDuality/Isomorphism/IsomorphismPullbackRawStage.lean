/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived

import WeilConjectures.SmoothPurity.Supporting.IsomorphismDerivedPullback
import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonNatural
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.PoincareDuality.Isomorphism.IsomorphismPullbackRationalExact

/-! # Normalized exact and t-exact pullback at a finite coefficient stage -/

@[expose] public noncomputable section
set_option autoImplicit false
-- These clause packages do not need generated constructor injectivity or size lemmas.
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
namespace WeilConjectures
set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback
  integralDerivedPullback sfRationalTriangulationDatum sfRationalScalarExtension
  rationalPullbackScalarComparison completedIntegralCoefficientSheafUnrestricted
  sfIntegralScalarComp sfIntegralScalarUnit
  GeneralAlgebraicallyClosedCoefficients.unitor GeneralAlgebraicallyClosedCoefficients.associator
  AlgebraicallyClosedCoefficients.coefficientInclusion
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.transition
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] constantSheaf HasDerivedCategory.standard integralCompletedScalarMap
  integralScalarExtension integralOrdinaryScalar sfRationalCoefficientEquiv

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

section CoefficientProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

private theorem normalizedInverseImageComparison :
    ∃ e : (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g ≅
        constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        HEq (e.hom.app K) (inverseImagePullbackComparisonDerived l E g hX hY K.obj) := by
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  obtain ⟨D, _⟩ := integralPullbackComparisonRealization l E E (AlgHom.id ℚ_[l] E)
  let T := (D.coefficient E).system Y
  let I := (sfIntegralConstructible l E Y).ι
  let G := inverseImageIntegralDerived l E g
  let : ∀ K : sfIntegralConstructibleCategory l E Y,
      IsIso ((Functor.whiskerLeft I S.adjunction.unit).app K) := fun K ↦ by
    let := (D.coefficient E).complete Y K
    change IsIso (S.adjunction.unit.app K.obj)
    rw [← T.adjunction.unit_leftAdjointUniq_hom_app S.adjunction K.obj]
    infer_instance
  obtain ⟨κ, hk, _, hθ, _⟩ :=
    inverseImagePullbackComparisonIntegral_natural.{u, u, 0, 0} l E g hX hY
  obtain ⟨θ, hθ⟩ := hθ S hS
  let : ∀ K : sfIntegralConstructibleCategory l E Y,
      IsIso ((Functor.whiskerLeft I κ).app K) := fun K ↦ by
    let : IsIso (S.adjunction.unit.app K.obj) :=
      inferInstanceAs (IsIso ((Functor.whiskerLeft I S.adjunction.unit).app K))
    change IsIso (κ.app K.obj)
    rw [hθ]
    infer_instance
  let : IsIso (Functor.whiskerLeft I κ) := NatIso.isIso_of_isIso_app _
  unfold constructibleIntegralPullback
  refine ⟨asIso (Functor.whiskerLeft I κ), ?_⟩
  intro K
  exact heq_of_eq (hk K.obj)

set_option allowUnsafeReducibility true in
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted in
attribute [local irreducible] limit in
omit [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)] in
private theorem inverseImage_preservesConstants
    (U : X.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    (inverseImageCompletedCoefficientMap l E g).hom.app U
      (integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a) =
        integralScalarConstant l E X U a := by
  apply (integralScalarConstant_existsUnique l E X U a).unique
  · intro n
    have hπ := congrArg (fun f ↦ f.hom.app U)
      (limit.lift_π (C := Sheaf (ProEt.topology X) RingCat.{u + 1})
        (show Cone (integralCoefficientSheafSystem l E X) from
          { pt := _
            π := { app n := inverseImageCompletedCoefficientComponent l E g n.unop
                   naturality _ _ f := (Category.id_comp _).trans
                     (inverseImageCompletedCoefficientComponent_naturality l E g f).symm } })
        (Opposite.op n))
    have hv := congrArg (fun f ↦ f
      (integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a)) hπ
    change _ = (inverseImageFiniteCoefficientMap l E g n).hom.app U
      (((limit.π (integralCoefficientSheafSystem l E Y) (Opposite.op n)).hom.app
        ((proEtaleIsoPostcompose g).op.obj U))
          (integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a)) at hv
    change ((limit.π (integralCoefficientSheafSystem l E X) (Opposite.op n)).hom.app U)
      ((inverseImageCompletedCoefficientMap l E g).hom.app U
        (integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a)) = _ at hv
    rw [hv]
    have hy := (integralScalarConstant_existsUnique l E Y
      ((proEtaleIsoPostcompose g).op.obj U) a).exists.choose_spec n
    change ((limit.π (integralCoefficientSheafSystem l E Y) (Opposite.op n)).hom.app
      ((proEtaleIsoPostcompose g).op.obj U))
        (integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a) = _ at hy
    erw [hy]
    exact (isoSectionwiseConstantMap_existsUnique.{u, u} g
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).exists.choose_spec U.unop _
  · exact (integralScalarConstant_existsUnique l E X U a).exists.choose_spec

set_option allowUnsafeReducibility true in
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted in
attribute [local irreducible] limit in
omit [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)] in
private theorem inverseImage_integralLinear :
    (inverseImageIntegralDerived l E g).Linear (Padic.coefficientExtensionIntegers l E) := by
  let : IsIso (inverseImageCompletedCoefficientMap l E g) :=
    inverseImageCompletedCoefficientMap_isIso l E g
  let F := inverseImageIntegralModules l E g
  let G := inverseImageIntegralDerived l E g
  let : F.Additive := isoSectionwiseModuleInverseImage_additive.{u, u} g
    (inverseImageCompletedCoefficientMap l E g)
  let : PreservesFiniteLimits F := isoSectionwiseModuleInverseImage_limits.{u, u} g
    (inverseImageCompletedCoefficientMap l E g)
  let : PreservesFiniteColimits F := isoSectionwiseModuleInverseImage_colimits.{u, u} g
    (inverseImageCompletedCoefficientMap l E g)
  have hchain (a : Padic.coefficientExtensionIntegers l E)
      (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      (F.mapHomologicalComplex (.up ℤ)).map ((integralScalarChainAction l E Y a).app P) =
        (integralScalarChainAction l E X a).app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    ext i U x
    change (((integralScalarChainAction l E Y a).app P).f i).val.app
        ((proEtaleIsoPostcompose g).op.obj U) x = _
    erw [(integralScalarChainAction_existsUnique l E Y a).exists.choose_spec]
    erw [(integralScalarChainAction_existsUnique l E X a).exists.choose_spec]
    let : SMul ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
        ((proEtaleIsoPostcompose g).op.obj U))
        ((P.X i).val.obj ((proEtaleIsoPostcompose g).op.obj U)) :=
      ((P.X i).val.obj ((proEtaleIsoPostcompose g).op.obj U)).isModule.toSMul
    let : SMul (((isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y)).obj.obj U)
        ((P.X i).val.obj ((proEtaleIsoPostcompose g).op.obj U)) :=
      ((P.X i).val.obj ((proEtaleIsoPostcompose g).op.obj U)).isModule.toSMul
    let x' : (P.X i).val.obj ((proEtaleIsoPostcompose g).op.obj U) := x
    change integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a • x' =
      (show (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj
          ((proEtaleIsoPostcompose g).op.obj U) from
        (inv (inverseImageCompletedCoefficientMap l E g)).hom.app U
          (integralScalarConstant l E X U a)) • x'
    rw [← inverseImage_preservesConstants l E g U a]
    have hc := congrArg (fun f ↦ f.hom.app U)
      (IsIso.hom_inv_id (inverseImageCompletedCoefficientMap l E g))
    exact congrArg (fun r ↦ r • x')
      (congrArg (fun f ↦ f
        (integralScalarConstant l E Y ((proEtaleIsoPostcompose g).op.obj U) a)) hc).symm
  have haction (a : Padic.coefficientExtensionIntegers l E) :=
    IntegralScalarAux.action_descent
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) G F.mapDerivedCategoryFactors
      (integralScalarDerivedAction l E Y a) (integralScalarDerivedAction l E X a)
      (fun P ↦ (integralScalarChainAction l E Y a).app P)
      (integralScalarDerivedAction_app_Q l E Y a)
      (fun P ↦ (congrArg DerivedCategory.Q.map (hchain a P)).trans
        (integralScalarDerivedAction_app_Q l E X a _).symm)
  constructor
  intro K L f a
  rw [(sfIntegralConstructible_linear l E Y).1,
    (sfIntegralConstructible_linear l E X).1, G.map_comp, haction]

private theorem normalizedIntegralShift
    :
    ∃ s : (constructibleIntegralPullback l E g).CommShift ℤ,
      ∃ e : (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g ≅
          constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι,
        (∀ K : sfIntegralConstructibleCategory l E Y,
          HEq (e.hom.app K) (inverseImagePullbackComparisonDerived l E g hX hY K.obj)) ∧
        (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
          NatTrans.CommShift e.hom ℤ ∧
            (constructibleIntegralPullback l E g).IsTriangulated) (_s := s) := by
  obtain ⟨e, he⟩ := normalizedInverseImageComparison l E g hX hY
  let s := Functor.CommShift.ofComp e.symm ℤ
  let := s
  let : NatTrans.CommShift e.symm.hom ℤ := Functor.CommShift.ofComp_compatibility e.symm ℤ
  let : NatTrans.CommShift e.hom ℤ := inferInstanceAs (NatTrans.CommShift e.symm.inv ℤ)
  refine ⟨s, e, he, inferInstance, ?_⟩
  exact (Functor.isTriangulated_iff_comp_right e.symm).2 inferInstance

include hX hY in
private theorem constructible_integralLinear :
    (constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E) := by
  let := inverseImage_integralLinear l E g
  obtain ⟨e, _⟩ := normalizedInverseImageComparison l E g hX hY
  let : (constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι).Linear
      (Padic.coefficientExtensionIntegers l E) := Functor.linear_of_iso _ e
  constructor
  intro K L f a
  apply (sfIntegralConstructible l E X).ι.map_injective
  rw [(sfIntegralConstructible l E X).ι.map_smul]
  exact (constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι).map_smul a f

private theorem integralStandardClass_pullback
    (b : Bool) (n : ℤ) (K : sfIntegralConstructibleCategory l E Y)
    (hK : sfIntegralStandardClass l E Y b n K) :
    sfIntegralStandardClass l E X b n ((constructibleIntegralPullback l E g).obj K) := by
  obtain ⟨h, ⟨e⟩, _⟩ := isomorphismIntegralDerivedPullback_termwise l E g
  intro i hi
  let F := isomorphismTermwiseModuleInverseImage g
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (isomorphismCompletedCoefficientComparison l E g)
  have hz := F.isZero_homologyFunctor_mapDerivedCategory_obj (hK i hi)
  exact hz.of_iso ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) i).mapIso
    ((sfIntegralConstructible l E X).ι.mapIso (e.app K)))

private theorem rationalStandardClass_pullback
    (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y)
    (hK : sfRationalStandardClass l E Y b n K) :
    sfRationalStandardClass l E X b n ((rationalDerivedPullback l E g).obj K) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨(constructibleIntegralPullback l E g).obj M,
    integralStandardClass_pullback l E g b n M hM, ⟨?_⟩⟩
  refine (rationalDerivedPullback l E g).mapIso e ≪≫ eqToIso ?_
  unfold rationalDerivedPullback
  exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1 _

end CoefficientProof

/-- Normalized exact and t-exact pullback at a single finite coefficient field.
Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-constructible-truncations.proof.md, final automorphism sentence;
steps 1--3 and 6 of lem-pod-isomorphism-pullback-texact-coefficients.
(blueprint: lem-pod-isomorphism-pullback-raw-stage).

Proof: the pro-etale isomorphism reindexes sheaves and their completed coefficient
rings. At each quotient it fixes constant coefficients, hence also at their inverse
limit. The induced exact functor on modules is integral-linear on complexes and
therefore on derived morphisms. The normalized reconstruction unit and comparison
identify its derived functor with completed integral pullback on constructible inputs.
Transport its termwise shift through this comparison and the fully faithful inclusion.
This preserves distinguished triangles. Exact inverse image commutes with homology,
so it preserves the vanishing conditions for both integral standard halves in every
degree. Apply semilinear scalar localization to this linear exact functor. Its object
and pure-tensor formulas uniquely identify it with the prescribed rational pullback;
the induced degree-one shift has the displayed normalization. Every rational half is
the isomorphism closure of the corresponding integral half, so its preservation follows
by applying pullback to an integral representative and its witnessing isomorphism.
The argument includes the zero object, torsion morphisms and empty schemes. -/
theorem isomorphismPullbackRawStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ s : (constructibleIntegralPullback l E g).CommShift ℤ,
      ∃ e : (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g ≅
          constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι,
        (∀ K : sfIntegralConstructibleCategory l E Y,
          HEq (e.hom.app K) (inverseImagePullbackComparisonDerived l E g hX hY K.obj)) ∧
        (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
          NatTrans.CommShift e.hom ℤ ∧
          (constructibleIntegralPullback l E g).IsTriangulated) (_s := s) ∧
        (constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E) ∧
        (∀ (b : Bool) (n : ℤ) (K : sfIntegralConstructibleCategory l E Y),
          sfIntegralStandardClass l E Y b n K →
          sfIntegralStandardClass l E X b n ((constructibleIntegralPullback l E g).obj K)) ∧
        ∃ sr : (rationalDerivedPullback l E g).CommShift ℤ,
          (∀ K : sfIntegralConstructibleCategory l E Y,
            HEq (((rationalDerivedPullback l E g).commShiftIso
              (self := sr) (1 : ℤ)).hom.app
                ((sfRationalConstructibleLocalization l E Y).obj K))
              ((sfRationalConstructibleLocalization l E X).map
                (((constructibleIntegralPullback l E g).commShiftIso
                  (self := s) (1 : ℤ)).hom.app K))) ∧
          (fun [_sr : (rationalDerivedPullback l E g).CommShift ℤ] ↦
            (rationalDerivedPullback l E g).IsTriangulated) (_sr := sr) ∧
          (∀ (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y),
            sfRationalStandardClass l E Y b n K →
            sfRationalStandardClass l E X b n ((rationalDerivedPullback l E g).obj K))  := by
  obtain ⟨s, e, he, hs, ht⟩ := normalizedIntegralShift l E g hX hY
  let := s
  let := ht
  let := constructible_integralLinear l E g hX hY
  obtain ⟨sr, htr, hsr⟩ := isomorphismPullbackRationalExact l E g
  exact ⟨s, e, he, ⟨hs, ht⟩, inferInstance, integralStandardClass_pullback l E g,
    sr, hsr, htr, rationalStandardClass_pullback l E g⟩

end WeilConjectures
