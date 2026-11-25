/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension

import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # The normalized integral scalar-completion comparison

Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-normalized-scalar-completion).

The ordinary coefficient model and its universal derived counit transport the existing
finite-free comparison to the specified quotient-completion chain map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
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

/-- The unique scalar-completion transformation with the specified counit square,
isomorphic on every derived-complete input.
Source: Bhatt--Scholze, Proposition 3.5.1 and Lemma 6.8.2(1)
(blueprint: lem-weil-normalized-scalar-completion).
Proof: identify the two ordinary sheafified scalar models by their completed coefficient
maps and lift this isomorphism to complexes. The universal left-derived comparison gives
a natural isomorphism of their derived functors and preserves the counits. Compose with
the existing normalized completed-scalar comparison. Its counit equation and the strict
chain transport identify the resulting square with the required quotient-completion
normalization, including the zero shifted coordinate. Intrinsic derived completeness
agrees with the legacy augmented-tower predicate; choose an auxiliary finite field in a
prime characteristic different from l to apply the finite-free comparison, which makes
this specified component invertible. Finally, good complexes localize to the derived
category. The normalization forces equality on every good representative by cancellation
of its representative comparison, and localization forces equality on all objects. -/
theorem normalizedIntegralScalarCompletion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W,
      (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        χ.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparison l E L ι W).hom.app P =
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj)) ∧
      (∀ K, IsSfDerivedComplete l E W K → IsIso (χ.app K)) := by
  let G := integralOrdinaryScalar l E L ι W
  let q := HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)
  let D := completedScalarCochainModel.{u, u} l E L ι W
  let T := completedDerivedScalarExtension.{u, u} l E L ι W
  let t := NatIso.mapHomologicalComplex (ordinaryScalarModelIso l E L ι W) (.up ℤ)
  let ε : DerivedCategory.Q ⋙ T ⟶
      completedOrdinaryScalarComplex l E L ι W ⋙ DerivedCategory.Q := D.ε
  let : T.IsLeftDerivedFunctor ε q := D.universal
  let : G.mapDerivedCategory.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom q :=
    Functor.isLeftDerivedFunctor_of_inverts q _ G.mapDerivedCategoryFactors
  let e : integralOrdinaryDerivedScalar l E L ι W ≅ T :=
    Functor.leftDerivedNatIso G.mapDerivedCategory T G.mapDerivedCategoryFactors.hom
      ε q (Functor.isoWhiskerRight t DerivedCategory.Q)
  have he (P : CochainComplex (integralTowerModules l E W) ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι W P =
        G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t.hom.app P) := by
    have h : e.hom.app (DerivedCategory.Q.obj P) ≫ ε.app P =
        G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (t.hom.app P) :=
      Functor.leftDerivedNatTrans_app G.mapDerivedCategory T
        G.mapDerivedCategoryFactors.hom ε q
        (Functor.isoWhiskerRight t DerivedCategory.Q).hom P
    have hε : ε.app P = completedScalarCounit.{u, u} l E L ι W P :=
      completedScalarCochainModel_counit l E L ι W P
    exact (congrArg (e.hom.app (DerivedCategory.Q.obj P) ≫ ·) hε).symm.trans h
  let c : T ⟶ integralScalarExtension l E L ι W := by
    unfold integralScalarExtension
    exact completedScalarComparison.{u, u} l E L ι W
  let r (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      (integralScalarExtension l E L ι W).obj (DerivedCategory.Q.obj P.obj) ⟶
        DerivedCategory.Q.obj ((integralScalarComplexFunctor l E L ι W).obj P.obj) :=
    (integralScalarExtensionComparison l E L ι W).hom.app P
  have hc (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
      c.app (DerivedCategory.Q.obj P.obj) ≫ r P =
        completedScalarCounit.{u, u} l E L ι W P.obj ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj) := by
    with_unfolding_all exact completedScalarComparison_spec.{u, u} l E L ι W P
  let χ : integralOrdinaryDerivedScalar l E L ι W ⟶ integralScalarExtension l E L ι W :=
    e.hom ≫ c
  have hχ : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      χ.app (DerivedCategory.Q.obj P.obj) ≫
          (integralScalarExtensionComparison l E L ι W).hom.app P =
        G.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι W).app P.obj) := by
    intro P
    change (e.hom.app _ ≫ c.app _) ≫ r P = _
    calc
      _ = e.hom.app _ ≫ (c.app _ ≫ r P) :=
        Category.assoc _ _ _
      _ = e.hom.app _ ≫ (completedScalarCounit.{u, u} l E L ι W P.obj ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj)) :=
        congrArg (e.hom.app (DerivedCategory.Q.obj P.obj) ≫ ·) (hc P)
      _ = (e.hom.app _ ≫ completedScalarCounit.{u, u} l E L ι W P.obj) ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj) :=
        (Category.assoc _ _ _).symm
      _ = (G.mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (t.hom.app P.obj)) ≫
          DerivedCategory.Q.map ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj) :=
        congrArg (· ≫ DerivedCategory.Q.map
          ((completedScalarChainComparison.{u, u} l E L ι W).app P.obj)) (he P.obj)
      _ = G.mapDerivedCategoryFactors.hom.app P.obj ≫ DerivedCategory.Q.map
          (t.hom.app P.obj ≫ (completedScalarChainComparison.{u, u} l E L ι W).app P.obj) :=
        (Category.assoc _ _ _).trans (congrArg
          (G.mapDerivedCategoryFactors.hom.app P.obj ≫ ·)
          (DerivedCategory.Q.map_comp _ _).symm)
      _ = _ := congrArg (fun z ↦ G.mapDerivedCategoryFactors.hom.app P.obj ≫
        DerivedCategory.Q.map z)
          (NatTrans.congr_app (integralScalarCompletionChain_model l E L ι W) P.obj).symm
  refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
  · intro K hK
    obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hp⟩
    let Δ : FiniteFieldDatum.{0} :=
      { p := p
        a := 1
        q := p
        prime := hp
        exponent_pos := le_refl 1
        cardinality_eq := (pow_one p).symm
        k₀ := ZMod p
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
    have hl : l ≠ Δ.p := by change l ≠ p; omega
    have hlegacy : IsDerivedCompleteUnrestricted l E W K :=
      ⟨Δ, hl, (sfDerivedComplete_iff_legacy l E W Δ hl K).mp hK⟩
    let : IsIso (c.app K) := by
      with_unfolding_all
        exact (finiteFreeCompletedScalarComparison.{u, u} l E L ι W).2.1 K hlegacy |>.1
    change IsIso (e.hom.app K ≫ c.app K)
    infer_instance
  · intro χ' hχ'
    let Λ := integralOperationsGoodLocalization l E W
    let qg := q.inverseImage (integralOperationsGoodComplex l E W).ι
    let : Λ.IsLocalization qg := integralOperationsGoodLocalization_isLocalization l E W
    apply Localization.natTrans_ext Λ qg
    intro P
    apply (cancel_mono ((integralScalarExtensionComparison l E L ι W).hom.app P)).mp
    exact (hχ'.1 P).trans (hχ P).symm

end WeilConjectures
