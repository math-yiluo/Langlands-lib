/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Comparison of the two ordinary scalar models

Source: Stacks Tags 06YY and 0941; the finite-free tensor normalization.
(blueprint: lem-trf-integral-scalar-ordinary-model-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : Scheme.{u}) : EssentiallySmall.{u+1} W.ProEt :=
  essentiallySmallSelf.{0, u, u+1} _

private local instance (W : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

attribute [local irreducible] HasDerivedCategory.standard
  completedScalarChangeData
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

private theorem scalarModelComparison
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u}) :
    ∃ e : integralOrdinaryDerivedScalar l E L ι X ≅
        completedDerivedScalarExtension.{u, u} l E L ι X,
      (∀ P : CochainComplex (integralTowerModules l E X) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι X)
                (.up ℤ)).hom.app P)) ∧
      e.hom ≫ completedScalarComparison.{u, u} l E L ι X = scalarCompletion l E L ι X := by
  let G := integralOrdinaryScalar l E L ι X
  let q := HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)
  let D := completedScalarCochainModel.{u, u} l E L ι X
  let T := completedDerivedScalarExtension.{u, u} l E L ι X
  let t := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι X) (.up ℤ)
  let ε : DerivedCategory.Q ⋙ T ⟶
      completedOrdinaryScalarComplex.{u, u} l E L ι X ⋙ DerivedCategory.Q := D.ε
  let : T.IsLeftDerivedFunctor ε q := D.universal
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ G.mapDerivedCategoryFactors
  let e : integralOrdinaryDerivedScalar l E L ι X ≅ T :=
    Functor.leftDerivedNatIso G.mapDerivedCategory T G.mapDerivedCategoryFactors.hom
      ε q (Functor.isoWhiskerRight t DerivedCategory.Q)
  have he (P : CochainComplex (integralTowerModules l E X) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
        G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t.hom.app P) := by
    have h : e.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P =
        G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t.hom.app P) :=
      Functor.leftDerivedNatTrans_app G.mapDerivedCategory T
        G.mapDerivedCategoryFactors.hom ε q
        (Functor.isoWhiskerRight t DerivedCategory.Q).hom P
    have hε : ε.app P = completedScalarCounit.{u, u} l E L ι X P :=
      completedScalarCochainModel_counit l E L ι X P
    exact (congrArg (e.hom.app (DerivedCategory.Q.obj P) ≫ ·) hε).symm.trans h
  have hc : e.inv ≫ scalarCompletion l E L ι X =
      completedScalarComparison.{u, u} l E L ι X := by
    apply (completedScalarComparison_existsUnique l E L ι X).unique
    · intro P
      dsimp only [NatTrans.comp_app]
      rw [Category.assoc]
      erw [(scalarCompletion_existsUnique l E L ι X).exists.choose_spec.1 P]
      rw [integralScalarCompletionChain_model l E L ι X]
      dsimp only [NatTrans.comp_app]
      erw [CategoryTheory.Functor.map_comp]
      apply (cancel_epi (e.hom.app (DerivedCategory.Q.obj P.obj))).mp
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
      erw [he P.obj]
    · exact (completedScalarComparison_existsUnique l E L ι X).exists.choose_spec
  refine ⟨e, he, ?_⟩
  rw [← hc]
  simp

private theorem scalarModelTensor
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
    (x : N.val.obj U) :
    ((ordinaryScalarModelIso l E L ι X).hom.app N).val.app U
        (integralOrdinaryTensorSection l E L ι X N U s x) =
      completedScalarTensorSection.{u, u} l E L ι X N U s x := by
  exact ordinaryScalarModelIso_transport l E L ι X N U s x

/-- The ordinary scalar models admit a pure-tensor-normalized isomorphism, whose
universal derived comparison preserves both the cochain counit and scalar completion.
Source: Stacks 06YY and 0941; the strict quotient-completion normalization.

Proof: use the canonical identification of the two sheafified change-of-rings
models. It sends each sheafified pure tensor s tensor x to the same tensor.
Lift it through the universal left-derived counits to obtain the derived
isomorphism and its counit equation on all complexes. On good complexes the two
completion comparisons have the same quotient augmentation and the same zero
shifted coordinate. The chain transport equation therefore identifies their
normalized descents. Uniqueness of the completed comparison, followed by
cancellation of the model isomorphism, gives the completion identity.
This construction applies to zero objects, identity embeddings and equal fields.
(blueprint: lem-trf-integral-scalar-ordinary-model-comparison). -/
theorem integralScalarOrdinaryModelComparison
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u}) :
    ∃ (t : integralOrdinaryScalar l E L ι X ≅
          completedOrdinaryScalarExtension.{u, u} l E L ι X)
      (e : integralOrdinaryDerivedScalar l E L ι X ≅
          completedDerivedScalarExtension.{u, u} l E L ι X),
      (∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
        (x : N.val.obj U),
        (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
          completedScalarTensorSection.{u, u} l E L ι X N U s x) ∧
      (∀ P : CochainComplex (integralTowerModules l E X) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
          (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P)) ∧
      (e.hom ≫ completedScalarComparison.{u, u} l E L ι X =
        scalarCompletion l E L ι X) := by
  obtain ⟨e, he, hχ⟩ := scalarModelComparison l E L ι X
  exact ⟨ordinaryScalarModelIso l E L ι X, e, scalarModelTensor l E L ι X, he, hχ⟩

end WeilConjectures
