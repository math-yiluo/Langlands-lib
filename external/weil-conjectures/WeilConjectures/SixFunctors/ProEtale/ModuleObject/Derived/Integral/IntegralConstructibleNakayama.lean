/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFiniteFreeContractive
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

/-! # Nakayama for integral constructible module objects

Source: Bhatt--Scholze, Proposition 6.8.11(3), and Nakayama's lemma.
(blueprint: lem-weil-pbc-integral-constructible-nakayama)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

variable {X : Scheme.{u}}
  {G G' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (φ : G ⟶ G') in
private lemma isIso_app_of_restriction {W : Scheme.{u}} (g : W ⟶ X)
    [WeaklyEtale g]
    (h : IsIso ((ProEtale.localizationRestriction Ab.{u + 1} g inferInstance).map φ))
    (V : X.ProEt) (p : V.left ⟶ W) (hp : p ≫ g = V.hom) :
    IsIso (φ.hom.app (op V)) := by
  have hpweaklyEtale : WeaklyEtale p := by
    have : WeaklyEtale (p ≫ g) := hp ▸ V.prop
    exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) p g ‹_› ‹_›
  have h1 : IsIso (((ProEtale.localizationRestriction Ab.{u + 1} g inferInstance).map φ).hom.app
      (op (MorphismProperty.Over.mk ⊤ p hpweaklyEtale))) := inferInstance
  rw [ProEtale.localizationRestriction_map_hom_app] at h1
  have e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj
      (MorphismProperty.Over.mk ⊤ p hpweaklyEtale) ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa using hp.symm)
  exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ φ.hom _ _ e.op h1

variable {X : Scheme.{u}}
  {G G' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (φ : G ⟶ G') in
private lemma isIso_of_cover_restrictions {indexType : Type*} {W : indexType → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, IsIso ((ProEtale.localizationRestriction Ab.{u + 1} (g i) inferInstance).map φ)) :
    IsIso φ := by
  refine Sheaf.isIso_of_isIso_app_of_mem _ φ fun V ↦
    ⟨_, Scheme.ProEt.ofArrows_baseChange_mem_topology V g hg, ?_⟩
  -- a member of the sieve generated by the base changes is a morphism `a` from a weakly
  -- étale `X`-scheme `T` to the `i`-th base change `V ×_X W i`, followed by the projection
  -- to `V`
  rintro T f ⟨-, a, -, ⟨i⟩, rfl⟩
  refine isIso_app_of_restriction φ (g i) (h i) T
    (a.left ≫ pullback.snd V.hom (g i)) ?_
  rw [Category.assoc, ← pullback.condition]
  exact MorphismProperty.Over.w a

private lemma isZero_of_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsZero (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    IsZero M := by
  have (i : U.I₀) : WeaklyEtale (U.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ (.mk i)
  have hX : IsZero M.X := by
    have : IsIso (0 : M.X ⟶ M.X) := by
      refine isIso_of_cover_restrictions _ U.f U.mem₀ fun i ↦ ?_
      have hz : IsZero ((localizationRestriction Ab.{u + 1} (U.f i)
          inferInstance).obj M.X) :=
        ((Mod.forget _).map_isZero (h i)).of_iso
          ((upperStarIsoLocalizationRestriction _ (U.f i) inferInstance).app M.X).symm
      rw [hz.eq_of_src ((localizationRestriction _ (U.f i) inferInstance).map 0) (𝟙 _)]
      infer_instance
    exact (IsZero.iff_id_eq_zero _).2 (by
      rw [← IsIso.hom_inv_id (0 : M.X ⟶ M.X), zero_comp])
  exact (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ (hX.eq_of_src _ _))

private lemma finitelyPresented_nakayama (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (e : R ⟶ condensedRingObj (integralCoeff ℓ E) X) [IsMonHom e] [IsIso e]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : Mod.IsFinitelyPresented R M) (hℓ : IsIso (ℓ • 𝟙 M)) : IsZero M := by
  let := hℓ
  obtain ⟨n, m, f, ⟨i⟩⟩ := hM
  let π : Mod.finiteFree R n ⟶ M := cokernel.π f ≫ i.inv
  have : Epi π := by dsimp [π]; infer_instance
  let t := π ≫ inv (ℓ • 𝟙 M)
  let b := pullback.snd π t
  have : Epi b := by dsimp [b]; infer_instance
  obtain ⟨U, hU⟩ := AlgebraicGeometry.ProEtale.freeEpiLocalSplitting X R _ _ b ⟨n, ⟨Iso.refl _⟩⟩
  apply isZero_of_cover M U
  intro j
  let F := (ProEtale.upperStar Ab.{u + 1} (U.f j)).mapMod R
  let R' := (ProEtale.upperStar Ab.{u + 1} (U.f j)).obj R
  have : IsSplitEpi (F.map b) := hU j
  let lift : F.obj (Mod.finiteFree R n) ⟶ F.obj (Mod.finiteFree R n) :=
    section_ (F.map b) ≫ F.map (pullback.fst π t)
  have hlift : lift ≫ F.map π = F.map t := by
    dsimp only [lift]
    rw [Category.assoc, ← F.map_comp, pullback.condition, F.map_comp,
      ← Category.assoc, IsSplitEpi.id, Category.id_comp]
  let efree : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree R' n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ ccsRegularMapIso (U.f j) R)
  let T := efree.inv ≫ lift ≫ efree.hom
  let e' : R' ⟶ condensedRingObj (integralCoeff ℓ E) (U.X j) :=
    (ProEtale.upperStar Ab.{u + 1} (U.f j)).map e ≫
      condensedPullbackHom (integralCoeff ℓ E) (U.f j)
  have : IsMonHom e' := by dsimp [e']; infer_instance
  have : IsIso e' := by dsimp [e']; infer_instance
  have : IsIso (𝟙 _ - ℓ • T) :=
    integralFiniteFree_one_sub_nsmul_isIso ℓ E (U.X j) R' e' n T
  have hconj : 𝟙 _ - ℓ • lift = efree.hom ≫ (𝟙 _ - ℓ • T) ≫ efree.inv := by
    simp [T, Preadditive.comp_sub, Preadditive.sub_comp]
  have : IsIso (𝟙 _ - ℓ • lift) := by rw [hconj]; infer_instance
  have hzero : (𝟙 _ - ℓ • lift) ≫ F.map π = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Preadditive.nsmul_comp, hlift]
    rw [← F.map_nsmul]
    have h : ℓ • t = π := by
      dsimp only [t]
      rw [← Preadditive.comp_nsmul]
      have h' : ℓ • inv (ℓ • 𝟙 M) = 𝟙 M := by
        simpa using IsIso.inv_hom_id (ℓ • 𝟙 M)
      rw [h', Category.comp_id]
    rw [h]
    exact sub_self _
  have hπ : F.map π = 0 := by
    rw [← Category.id_comp (F.map π), ← IsIso.inv_hom_id (𝟙 _ - ℓ • lift),
      Category.assoc, hzero, comp_zero]
  have : Epi (F.map π) := inferInstance
  exact (IsZero.iff_id_eq_zero _).2 ((cancel_epi (F.map π)).1 (by simp [hπ]))

/-- An integral constructible module on which multiplication by ℓ is invertible is zero.
Source: Bhatt--Scholze, Proposition 6.8.11(3), and Nakayama's lemma.
(blueprint: lem-weil-pbc-integral-constructible-nakayama)

Proof: choose a finite stratification and finite presentations on pro-etale covers.
For a presented module M, let π : R^n → M be the presentation epimorphism. Pull π back
along π composed with the inverse of multiplication by ℓ. Locally this pullback
epimorphism onto R^n splits: lift its finitely many basis sections through an epimorphism
of sheaves and combine their covering families. The resulting endomorphism T of R^n
satisfies Tπ = π/ℓ, so (1-ℓT)π=0. The contractive-matrix lemma makes 1-ℓT invertible;
thus π=0, and its epimorphism property makes M zero. Restriction along a presentation
cover detects zero by sheaf separatedness. The finitely many quasi-compact stratum
immersions jointly detect zero as well: after sheafification and filtered Kan extension,
vanishing along their pullbacks supplies a pro-etale cover on which each section
vanishes. This yields zero globally. Empty strata and rank zero satisfy the same formulas. -/
theorem integralConstructible_isZero_of_isIso_nsmul (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M)
    (hℓ : IsIso (ℓ • 𝟙 M)) : IsZero M := by
  let := hℓ
  obtain ⟨S, hS⟩ := hM
  have (a : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  have (a : Fin S.n) : QuasiCompact (S.immersion a) := inferInstance
  have hzero (a : Fin S.n) : IsZero
      (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod
        (condensedRingObj (integralCoeff ℓ E) X)).obj M) := by
    obtain ⟨U, hU⟩ := hS a
    apply isZero_of_cover _ U
    intro j
    let F := ProEtale.upperStar Ab.{u + 1} (S.immersion a)
    let G := ProEtale.upperStar Ab.{u + 1} (U.f j)
    let R := condensedRingObj (integralCoeff ℓ E) X
    let e : G.obj (F.obj R) ⟶ condensedRingObj (integralCoeff ℓ E) (U.X j) :=
      G.map (condensedPullbackHom (integralCoeff ℓ E) (S.immersion a)) ≫
        condensedPullbackHom (integralCoeff ℓ E) (U.f j)
    have : IsMonHom e := by dsimp [e]; infer_instance
    have : IsIso e := by dsimp [e]; infer_instance
    apply finitelyPresented_nakayama ℓ E (U.X j) _ e _ (hU j)
    have : IsIso ((G.mapMod (F.obj R)).map ((F.mapMod R).map (ℓ • 𝟙 M))) :=
      inferInstance
    rw [(F.mapMod R).map_nsmul, (F.mapMod R).map_id,
      (G.mapMod (F.obj R)).map_nsmul, (G.mapMod (F.obj R)).map_id] at this
    exact this
  apply (IsZero.iff_id_eq_zero _).2
  apply Mod.hom_ext
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
    (fun x ↦ ?_) (𝟙 M.X)
  · intro a
    exact congrArg Mod.Hom.hom ((hzero a).eq_of_src
      (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod
        (condensedRingObj (integralCoeff ℓ E) X)).map (𝟙 M)) 0)
  · have hx : x ∈ ⋃ a, S.stratum a := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩

end AlgebraicGeometry.ProEtale.CondensedRing
