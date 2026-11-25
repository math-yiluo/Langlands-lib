/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
import WeilConjectures.SixFunctors.Open.OpenDvrOrdinaryTensorTransport
import all WeilConjectures.SixFunctors.Open.OpenDvrScalarUnitFormula
import WeilConjectures.SixFunctors.Open.OpenDvrDerivedTowerComparison
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
/-! # Strict quotient reduction under canonical DVR coefficients

Source: Stacks Tags 0941, 099B and 0A0E; canonical coefficient transport.
(blueprint: lem-sf-open-dvr-strict-reduction-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.rightDerivedFunctor

/-- The strict tensor comparisons before total derived coefficient-limit transport.
Source: Stacks Tags 07A6 and 0941
(blueprint: lem-sf-open-dvr-strict-reduction-comparison). -/
structure OpenDvrStrictReductionComparison
    {d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E)} {T : Scheme.{u}}
    (C : OpenDvrCoefficientModel l E d T) (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    where
  /-- The two quotient tower functors are canonically identified. -/
  tower : C.derived.functor ⋙ completedAdicReduction T d ≅
    S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T ⋙ C.towers
  /-- The same strict tensor augmentation, before taking total derived inverse limit. -/
  representative : ∀ (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
      (_hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T) Q),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (Q.X i)) →
    ∃ (B : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ)
      (a : ((Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _).mapHomologicalComplex
        (.up ℤ)).obj Q ⟶ B)
      (κ : HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj B ≅
        unrestrictedIntegralComplexTower.{u, u} l E T Q)
      (e : (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj B)
      (τ : ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
          (C.complexes.obj Q) ≅ C.towerComplexes.obj B),
      (∀ (i : ℤ) (n : ℕ),
        (reconstructionOrdinaryUnit T d).app (C.modules.functor.obj (Q.X i)) ≫
            limit.π ((completedAdicOrdinaryTower T d).obj
              (C.modules.functor.obj (Q.X i))) (op n) ≫ (τ.hom.f i).app (op n) =
          C.modules.functor.map ((a.f i).app (op n))) ∧
      ((completedAdicReduction T d).map
          (C.modules.functor.mapDerivedCategoryFactors.hom.app Q) ≫
          reconstructionReductionComplexCounit T d (C.complexes.obj Q) ≫
          DerivedCategory.Q.map τ.hom =
        tower.hom.app (DerivedCategory.Q.obj Q) ≫ C.towers.map e.hom ≫
          C.ordinaryTowers.mapDerivedCategoryFactors.hom.app B) ∧
      (∀ n : ℕ, HEq
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app (op n) ≫
          κ.hom.app (op n)) (unrestrictedTowerUnit.{u, u} l E T Q n)) ∧
      (C.derived.functor.map (S.adjunction.unit.app (DerivedCategory.Q.obj Q)) ≫
          C.derived.functor.map ((coefficientConstantTowerLimit.{u, u} l E T).map e.hom) =
        C.derived.functor.map (DerivedCategory.Q.map
          (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
              lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
              ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
                (.up ℤ)).map a) ≫
          derivedLimitComplexComparison
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
            (coefficientConstantTowerLimit.{u, u} l E T)
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B))

local instance (priority := 10000) sequenceSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × T.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} T

/-- Strict quotient tensor transport and its scalar adjunction normalization.
Source: Stacks Tags 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-strict-reduction-comparison).

Proof: choose the existing ordinary quotient model M for S, and its universally
normalized left-derived comparison epsilon. The ordinary coefficient tensor
comparison nu identifies the two strict ordinary towers and their augmentations.
The already proved ring-isomorphism tensor transport preserves K-flatness.
Construct two natural counits to the same complex-valued functor: completed-adic
reduction after the exact coefficient equivalence, and epsilon after restriction
and coefficient transport followed by nu inverse. Both counits are invertible on
flat-term K-flat complexes, which resolve all complexes. The comparison theorem
on a resolving class gives the natural derived tower isomorphism and its exact
representative equation. Cancellation of nu inverse gives the reduction-counit
square required here.

For a given Q use the actual complex I=M.quotient Q and its restricted tower B.
Take a to be the ordinary constant/limit adjunct of M.adjunction.unit on Q.
Take e from epsilon and the exact restriction localization factors, and tau from
nu on complexes. The ordinary transport gives kappa and both augmentation laws.
Evaluate the normalized derived Hom formula on the identity of I. After composing
with the restriction localization factor, its inverse in systemLimitUnit cancels.
Ordinary limit projections identify M.limitComparison with the canonical termwise
comparison after the composite-functor comparison. The ordinary Hom equivalence
identifies a's adjunct with M.adjunction.unit. Cancel the termwise comparison with
its inverse in the canonical derived-limit unit. This gives the total-limit formula
before applying C.derived.functor, so functoriality proves the last clause.
This calculation uses ordinary projections only to identify ordinary limits;
it never detects equality in a derived limit by its finite projections.
The construction works for zero complexes and the empty site and uses neither
flat quotient rings nor boundedness nor exact countable products. -/
theorem openDvrStrictReductionComparison
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u}) (C : OpenDvrCoefficientModel l E d T)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E T) :
    Nonempty (OpenDvrStrictReductionComparison l E C S) := by
  classical
  let := coefficientSequenceHasDerived.{u, u} l E T
  let := coefficientConstantTowerDerived.{u, u} l E T
  obtain ⟨M⟩ := CompletionUnit.ordinaryModel_exists.{u, u} l E T
  obtain ⟨ν, hν, hκ⟩ := openDvrOrdinaryTensorTransport l E d T C M
  obtain ⟨_, ε, _, hε, _, hhom⟩ := CompletionUnit.fixedDerivedComparison.{u, u} l E T S M
    (CompletionUnit.termwiseLimitComparison.{u, u} l E T)
    (CompletionUnit.termwiseLimitComparison_projection.{u, u} l E T)
    (CompletionUnit.constantLimitUnit.{u, u} l E T)
    (CompletionUnit.constantLimitUnit_normalization.{u, u} l E T)
  obtain ⟨t, ht⟩ := openDvrDerivedTowerComparison l E d T C S M ν ε hε
  let U := coefficientSequenceRestriction.{u, u} l E T
  let : U.Additive := coefficientSequenceRestriction_additive.{u, u} l E T
  let : PreservesFiniteLimits U := coefficientSequenceRestriction_limits.{u, u} l E T
  let : PreservesFiniteColimits U := coefficientSequenceRestriction_colimits.{u, u} l E T
  let νc := NatIso.mapHomologicalComplex ν (.up ℤ)
  refine ⟨{ tower := t, representative := ?_ }⟩
  intro Q hQ hflat
  let I := (M.quotient l E T).obj Q
  let B := (CompletionUnit.tower l E T).obj I
  let a := openScalarComplexAugmentation l E T M Q
  have := hε Q hQ hflat
  let e : (S.reduction ⋙ coefficientSequenceDerivedRestriction.{u, u} l E T).obj
      (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj B :=
    U.mapDerivedCategory.mapIso (asIso (ε.app Q)) ≪≫ U.mapDerivedCategoryFactors.app I
  let τ : ((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj
      (C.complexes.obj Q) ≅ C.towerComplexes.obj B := νc.app Q
  obtain ⟨κ, hκQ⟩ := hκ Q
  refine ⟨B, a, κ, e, τ, hν Q, ?_, hκQ, ?_⟩
  · exact ht Q hQ hflat
  · let R :=
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctor
    let sunit : DerivedCategory.Q.obj Q ⟶
        R.obj ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
          (S.reduction.obj (DerivedCategory.Q.obj Q))) :=
      S.adjunction.unit.app (DerivedCategory.Q.obj Q)
    let rhs := DerivedCategory.Q.map
      (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
        lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
          ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
            (.up ℤ)).map a) ≫
      derivedLimitComplexComparison
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _) R
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B
    change C.derived.functor.map sunit ≫ C.derived.functor.map (R.map e.hom) =
      C.derived.functor.map rhs
    have hu := hhom Q I (𝟙 _)
    have hid := (DerivedCategory.Q (C := coefficientSequenceModules.{u, u} l E T)).map_id I
    have hcomp : ε.app Q ≫ 𝟙 (DerivedCategory.Q.obj I) = ε.app Q :=
      Category.comp_id (ε.app Q)
    have hadj : ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I) (𝟙 I) =
        (M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q :=
      (M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv_id Q
    rw [hid, hcomp, hadj] at hu
    have hs : sunit ≫ R.map (U.mapDerivedCategory.map (ε.app Q) ≫
        U.mapDerivedCategoryFactors.hom.app I) = rhs :=
      openDvrScalarUnitFormula l E T S M Q
        (CompletionUnit.termwiseLimitComparison.{u, u} l E T)
        (CompletionUnit.termwiseLimitComparison_projection.{u, u} l E T)
        (CompletionUnit.constantLimitUnit.{u, u} l E T)
        (openDvrCanonicalLimitFormula l E T) (ε.app Q) hu
    have he : e.hom = U.mapDerivedCategory.map (ε.app Q) ≫
        U.mapDerivedCategoryFactors.hom.app I := by
      simp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom]
    rw [← he] at hs
    exact (C.derived.functor.map_comp _ _).symm.trans (congrArg C.derived.functor.map hs)

end WeilConjectures
