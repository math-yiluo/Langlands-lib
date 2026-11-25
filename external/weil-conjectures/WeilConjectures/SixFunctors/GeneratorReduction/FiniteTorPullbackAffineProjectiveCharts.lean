/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree.Path.QcqsOpenClosedTree
import WeilConjectures.AlgebraicGeometry.Affine.AffineOpenClosedChartFactorization
import all WeilConjectures.SixFunctors.GeneratorReduction.ProjectiveChartOrdinaryTensorModel
import all WeilConjectures.WeilSheaf.OrdinaryStratifiedModels.OrdinaryPullbackStratifiedModels
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison
import all WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Finite-projective charts for ordinary pullback

Source: Bhatt--Scholze, Lemmas 6.5.5--6.5.8; Stacks Tag 09C3.
(blueprint: lem-sf-finite-tor-pullback-affine-projective-charts)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
  WeilConjectures.IntegralOnSlice.abSheafify
  WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private abbrev ProjectiveTerms (T : Scheme.{u})
    (P : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) : Prop :=
  ∀ k : ℤ, ∃ r : ℕ,
    ∃ i : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)),
    ∃ p : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T))) ⟶ P.X k,
    i ≫ p = 𝟙 _

private abbrev HasProjectiveModel (T : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E T)) : Prop :=
  ∃ P : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ,
    (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k)) ∧
    ProjectiveTerms l E T P ∧ Nonempty (K ≅ DerivedCategory.Q.obj P)

private theorem projectiveModel_of_iso {T : Scheme.{u}}
    {K L : DerivedCategory (scalarReductionSource.{u, u} l E T)} (e : K ≅ L)
    (h : HasProjectiveModel l E T L) : HasProjectiveModel l E T K := by
  obtain ⟨P, hb, hp, ⟨d⟩⟩ := h
  exact ⟨P, hb, hp, ⟨e ≪≫ d⟩⟩

private def ordinaryUnitIso {T Y : Scheme.{u}} (g : T ⟶ Y) :
    (ordinaryIntegralModulePull l E g).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)) ≅
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T) := by
  let : (SheafOfModules.pushforward.{u + 1} (F := Scheme.proEtaleBaseChange g)
      (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology T)
      (ordinaryIntegralDirectRingMap l E g)).IsRightAdjoint :=
    ordinaryIntegralModulePush_isRightAdjoint l E g
  exact asIso (SheafOfModules.pullbackObjUnitToUnit (F := Scheme.proEtaleBaseChange g)
    (ordinaryIntegralDirectRingMap l E g))

private theorem projectiveModel_pullback {T Y : Scheme.{u}} (g : T ⟶ Y)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (hK : HasProjectiveModel l E Y K) :
    HasProjectiveModel l E T ((IntegralSystemRealization.ringedPull l E g).obj K) := by
  classical
  obtain ⟨P, ⟨a, b, hb⟩, hp, ⟨e⟩⟩ := hK
  let F := ordinaryIntegralModulePull l E g
  have := OrdinaryStratifiedModels.ordinaryPull_limits l E g
  have := OrdinaryStratifiedModels.ordinaryPull_colimits l E g
  let Q := (F.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨Q, ⟨a, b, fun k hk ↦ F.map_isZero (hb k hk)⟩, ?_, ?_⟩
  · intro k
    obtain ⟨r, i, p, hip⟩ := hp k
    let d : F.obj (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y))) ≅
        ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)) :=
      PreservesProduct.iso F _ ≪≫ Pi.mapIso (fun _ ↦ ordinaryUnitIso l E g)
    refine ⟨r, F.map i ≫ d.hom, d.inv ≫ F.map p, ?_⟩
    change (F.map i ≫ d.hom) ≫ (d.inv ≫ F.map p) = 𝟙 (F.obj (P.X k))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, hip, F.map_id]
  · have := OrdinaryStratifiedModels.ordinaryCounitExact l E g P
    exact ⟨(IntegralSystemRealization.ringedPull l E g).mapIso e ≪≫
      (IntegralOrdinary.pullIso l E g).app (DerivedCategory.Q.obj P) ≪≫
      asIso (ordinaryIntegralPullComplexCounit l E g P)⟩

private theorem unit_hasProjectiveModel (Y : Scheme.{u}) :
    HasProjectiveModel l E Y
      (IntegralSystemRealization.calculus l E Y).integralClosed.monoidal.tensorUnit := by
  classical
  let : HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, u} Y
  let : (Scheme.ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, u} Y
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y
  let S := (IntegralSystemRealization.calculus l E Y).integralClosed
  obtain ⟨e, _⟩ := @CategoryTheory.RingedKFlatModel.comparison_exists.{u + 1, u, u, u + 2}
    Y.ProEt inferInstance (Scheme.ProEt.topology Y) inferInstance inferInstance R
    (integralTowerHasDerivedCategory l E Y) S
    (IntegralSystemRealization.calculus l E Y).integralTensorModel
  let N : MonoidalCategory (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    @CategoryTheory.RingedDerivedNative.monoidal.{u + 1, u, u, u + 2}
      Y.ProEt inferInstance (Scheme.ProEt.topology Y) inferInstance inferInstance R
      (integralTowerHasDerivedCategory l E Y)
  let A := SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)
  let P := (HomologicalComplex.single (scalarReductionSource.{u, u} l E Y) (.up ℤ) 0).obj A
  let d : S.monoidal.tensorUnit ≅ DerivedCategory.Q.obj P :=
    (N.rightUnitor S.monoidal.tensorUnit).symm ≪≫
      e.app (S.monoidal.tensorUnit, N.tensorUnit) ≪≫ S.monoidal.leftUnitor N.tensorUnit ≪≫
      @CategoryTheory.RingedDerivedNative.unitIso.{u + 1, u, u, u + 2}
        Y.ProEt inferInstance (Scheme.ProEt.topology Y) inferInstance inferInstance R
        (integralTowerHasDerivedCategory l E Y)
  refine ⟨P, ⟨0, 0, ?_⟩, ?_, ⟨d⟩⟩
  · intro k hk
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A k (by omega)
  · intro k
    by_cases hk : k = 0
    · subst k
      let d : P.X 0 ≅ ∏ᶜ (fun _ : Fin 1 ↦ A) :=
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 A ≪≫ (productUniqueIso (fun _ : Fin 1 ↦ A)).symm
      exact ⟨1, d.hom, d.inv, d.hom_inv_id⟩
    · have hz : IsZero (P.X k) :=
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A k hk
      exact ⟨0, 0, 0, by exact hz.eq_of_src _ _⟩

/-- Source finite-projective charts give bounded finite-projective models for
ordinary pullback on a finite tree over every target affine open. This assertion constructs
models and splittings; it makes no assertion about completion of those models.

Source: Bhatt--Scholze, proof of Lemma 6.5.5, Lemmas 6.5.6--6.5.8;
Stacks proetale.tex, Tag 09C3, lemma-local-structure-constructible-complex.
(blueprint: lem-sf-finite-tor-pullback-affine-projective-charts).

Proof: apply affineOpenClosedChartFactorization to the property that the ordinary
restriction of K has a bounded finite-free-retract cochain model. Its finite qcqs
tree and chart covers give actual factorizations through source charts, so only
algebraic transport remains. Ordinary pullback is exact by the existing completed
coefficient comparison, and its derived counit identifies pullback of the source
model with its termwise ordinary pullback. This preserves zero terms, finite
products of the regular coefficient module, and the splitting equations.
The normalized ordinary-pullback comparisons and the ringedPull compositor
identify this termwise model with the required chart restriction of ringedPull f K.
In the tensor-unit case, the native K-flat tensor comparison and its unitors identify
the recorded unit with the regular coefficient module in degree zero. This has
a rank-one splitting in degree zero and rank-zero splittings elsewhere. Apply
the same algebraic transport along f and then along the identity pro-etale chart
over U, using the one-vertex tree. Empty leaves impose no model condition.
At no point is ordinary pullback asserted to preserve infinite products. -/
theorem finiteTorPullbackAffineProjectiveCharts
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hs : IsSeparated f) (_ht : LocallyOfFiniteType f) (_hq : QuasiCompact f)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : (∀ (V : Y.Opens), IsAffine V.toScheme →
      ∃ tree : QcqsOpenClosedTree V.toScheme,
        ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → Nonempty S →
          ∃ (c : ℕ) (A : Fin c → S.ProEt),
            (∀ i, CompactSpace (A i).left) ∧
            (∀ i, QuasiSeparatedSpace (A i).left) ∧
            (∀ x : S, ∃ i, x ∈ Set.range (A i).hom.base) ∧
            ∀ i : Fin c,
              ∃ P : CochainComplex (scalarReductionSource l E (A i).left) ℤ,
                (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k)) ∧
                (∀ k : ℤ, ∃ r : ℕ,
                  ∃ ι : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
                    (completedIntegralCoefficientSheafUnrestricted l E (A i).left)),
                  ∃ π : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
                    (completedIntegralCoefficientSheafUnrestricted l E (A i).left))) ⟶ P.X k,
                  ι ≫ π = 𝟙 _) ∧
                Nonempty ((IntegralOnSlice.ordinaryDerivedPull l E
                  ((A i).hom ≫ p.toRoot ≫ V.ι)).obj K ≅ DerivedCategory.Q.obj P)) ∨
      K = (IntegralSystemRealization.calculus l E Y).integralClosed.monoidal.tensorUnit)
    (U : X.Opens) [IsAffine U.toScheme] :
    ∃ tree : QcqsOpenClosedTree U.toScheme,
      ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → Nonempty S →
        ∃ (c : ℕ) (A : Fin c → S.ProEt),
          (∀ i, CompactSpace (A i).left) ∧
          (∀ i, QuasiSeparatedSpace (A i).left) ∧
          (∀ x : S, ∃ i, x ∈ Set.range (A i).hom.base) ∧
          ∀ i : Fin c,
            ∃ P : CochainComplex (scalarReductionSource l E (A i).left) ℤ,
              (∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (P.X k)) ∧
              (∀ k : ℤ, ∃ r : ℕ,
                ∃ ι : P.X k ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E (A i).left)),
                ∃ π : (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E (A i).left))) ⟶ P.X k,
                ι ≫ π = 𝟙 _) ∧
              Nonempty ((IntegralOnSlice.ordinaryDerivedPull l E
                ((A i).hom ≫ p.toRoot ≫ U.ι)).obj
                  ((IntegralSystemRealization.ringedPull l E f).obj K) ≅
                    DerivedCategory.Q.obj P) := by
  classical
  rcases _hK with hK | rfl
  · let C := fun (T : Scheme.{u}) (g : T ⟶ Y) ↦
      HasProjectiveModel l E T ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E g).obj K)
    obtain ⟨tree, htree⟩ := affineOpenClosedChartFactorization f _hs _ht _hq C hK U
    refine ⟨tree, ?_⟩
    intro S p hp hS
    obtain ⟨c, A, hqc, hqs, hcover, hfactor⟩ := htree S p hp hS
    refine ⟨c, A, hqc, hqs, hcover, ?_⟩
    intro i
    obtain ⟨T, g, h, hmodel, hcomp⟩ := hfactor i
    let q := (A i).hom ≫ p.toRoot ≫ U.ι
    let d : (IntegralOnSlice.ordinaryDerivedPull.{u, u} l E q).obj
          ((IntegralSystemRealization.ringedPull l E f).obj K) ≅
        (IntegralSystemRealization.ringedPull l E h).obj
          ((IntegralOnSlice.ordinaryDerivedPull.{u, u} l E g).obj K) :=
      (ordinaryPullIso l E q).app _ ≪≫
        (IntegralSystemRealization.ringedPullComp l E q f).symm.app K ≪≫
        (eqToIso (congrArg (fun r ↦ (IntegralSystemRealization.ringedPull l E r).obj K)
          hcomp)) ≪≫
        (IntegralSystemRealization.ringedPullComp l E h g).app K ≪≫
        (IntegralSystemRealization.ringedPull l E h).mapIso
          ((ordinaryPullIso l E g).symm.app K)
    exact projectiveModel_of_iso l E d (projectiveModel_pullback l E h _ hmodel)
  · refine ⟨.leaf U.toScheme, ?_⟩
    intro S p
    cases p with
    | root =>
      intro _ _
      let A : Fin 1 → U.toScheme.ProEt := fun _ ↦ Scheme.ProEt.mk (𝟙 U.toScheme)
      refine ⟨1, A, ?_, ?_, ?_, ?_⟩
      · intro i
        change CompactSpace U.toScheme
        infer_instance
      · intro i
        change QuasiSeparatedSpace U.toScheme
        infer_instance
      · intro x
        exact ⟨0, x, rfl⟩
      · intro i
        let q := (A i).hom ≫ QcqsOpenClosedTree.Path.toRoot
          (QcqsOpenClosedTree.Path.root (.leaf U.toScheme)) ≫ U.ι
        exact projectiveModel_of_iso l E ((ordinaryPullIso l E q).app _)
          (projectiveModel_pullback l E q _
            (projectiveModel_pullback l E f _ (unit_hasProjectiveModel l E Y)))

end WeilConjectures.GeneratorReduction
