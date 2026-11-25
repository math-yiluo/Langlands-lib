/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicProperLocalizingPushforward
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingBrownRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingSubcategoryUniverse
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
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
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Cohomological boundedness of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

universe w v₁ u₁ u₂

namespace CategoryTheory.Functor

private theorem closure_isLocalizing
    {C : Type u₁} [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G : ObjectProperty C) :
    IsLocalizingSubcategoryOfSize.{w} (localizingClosureOfSize.{w} G) := by
  let L := localizingClosureOfSize.{w} G
  have hi : L.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX P hP hGP
    have := hP.2.1
    exact P.prop_of_iso e (hX P hP hGP)⟩
  have hz : L.ContainsZero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := C)
    refine ⟨Z, hZ, ?_⟩
    intro P hP hGP
    have := hP.1
    have := hP.2.1
    exact P.prop_of_isZero hZ
  have hs : L.IsStableUnderShift ℤ := ⟨fun n ↦ ⟨by
    intro X hX P hP hGP
    have := hP.1
    exact P.le_shift n X (hX P hP hGP)⟩⟩
  have ht : L.IsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃ P hP hGP
    have := hP.1
    have := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hGP) (h₃ P hP hGP))
  refine ⟨⟨⟩, hi, ?_⟩
  intro I A hA h
  dsimp only
  intro P hP hGP
  exact hP.2.2 A hA (fun i ↦ h i P hP hGP)

private theorem closure_index_eq
    {C : Type u₁} [Category.{v₁} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{w} C] (G : ObjectProperty C) :
    localizingClosure G = localizingClosureOfSize.{w} G := by
  apply le_antisymm
  · intro K hK
    exact hK _ (@isLocalizingSubcategory_of_locallySmall C _ _ _ _ _ _ ‹LocallySmall.{w} C› _
      (closure_isLocalizing.{w} G)) (fun X hX P hP hGP ↦ hGP X hX)
  · intro K hK P hP hGP
    have := hP.2.1
    -- `IsLocalizingSubcategory` is indexed by the morphism universe `v₁`: restate `hP` with that
    -- index written out and enlarge it to the index `w` with
    -- `isLocalizingSubcategoryOfSize_of_locallySmall` at the instance `locallySmall_self C`,
    -- passed explicitly (instance resolution would pick the ambient `LocallySmall.{w} C` and fix
    -- the index to `w`)
    have hv : IsLocalizingSubcategoryOfSize.{v₁} P :=
      ⟨hP.1, hP.2.1, fun F hF h ↦ hP.2.2 F hF h⟩
    exact hK P (@isLocalizingSubcategoryOfSize_of_locallySmall C _ _ _ _ _ _ (locallySmall_self C)
      P hv) hGP

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local irreducible] upperStarFromPoint openImmersionLowerShriek lowerStar
  Functor.rightAdjoint

-- Transport both constructibility conventions through a coefficient-ring isomorphism.
private theorem general_constructible_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (h : IsConstructibleModuleObject R M) :
    IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun a ↦ lfp_of_iso (hS a)
    (((upperStar Ab (S.immersion a)).mapMod R).mapIso e)⟩

private theorem general_constructible_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun a ↦ ?_⟩
  let F := upperStar Ab (T.immersion a)
  exact lfp_of_iso (lfp_comap (F.map φ) (hT a)) ((F.mapModComapIso φ).app M).symm

private theorem comparison_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ' X),
      IsConstructibleModuleObject (condensedRingObj Λ' X) M ↔
        IsConstantModelConstructible Λ' X M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
      IsConstantModelConstructible Λ X M := by
  let φ := (upperStarFromPoint X).map e.inv.hom
  let ψ := (upperStarFromPoint X).map e.hom.hom
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
    Mod.comap φ
  let G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    Mod.comap ψ
  let ei : G.obj (F.obj M) ≅ M :=
    ((Mod.comapComp ψ φ).symm.app M) ≪≫
      ((Mod.comapCongr (show ψ ≫ φ = 𝟙 _ by
        exact ((upperStarFromPoint X).mapIso ((Mon.forget _).mapIso e)).hom_inv_id)).app M) ≪≫
      (Mod.comapId _).app M
  constructor
  · intro hM
    have hc := (h (F.obj M)).mp (general_constructible_comap φ hM)
    exact constructible_iso ei (constructible_comap e.hom.hom X _ hc)
  · intro hM
    have hc := (h (F.obj M)).mpr (constructible_comap e.inv.hom X _ hM)
    exact general_constructible_iso ei (general_constructible_comap ψ hc)

open MonoidalCategory MonObj in
private noncomputable def coefficientMonIso
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let h := Profinite.continuousMapRingSheafMap e.toRingHom he
  let k := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
  let q : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := h
      inv := k
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply (x.down t)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply (x.down t) }
  let F := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have _ : IsMonHom (F.mapIso q).hom :=
    inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat Ab)).map h))
  exact Mon.mkIso' (F.mapIso q)

open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_hasConstantModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
      ∃ n : ℕ, Nonempty ((CondensedRing.upperStar Λ (U.f i)).obj M ≅
        Mod.finiteFree (condensedRingObj Λ (U.X i)) n)) :
    HasFiniteConstantLocalModel Λ Y M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hU i
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesFiniteBiproducts F := inferInstance
  let en : F.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree (condensedRingObj Λ (U.X i)) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  refine ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

private theorem generators_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  have hm (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M := by
    rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      have : TopologicalSpace.NoetherianSpace (S.domain a) :=
        (S.immersion a).isEmbedding.isInducing.noetherianSpace
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
        ((Mod.extendScalarsIsoComapInv φ).app _).symm
      obtain ⟨U, hU⟩ := hLF _ _ h
      apply free_hasConstantModel Λ _
      refine ⟨U, fun i ↦ ?_⟩
      let ψ := condensedPullbackHom Λ (U.f i)
      exact free_of_iso (free_comap (inv ψ) (hU i))
        ((Mod.extendScalarsIsoComapInv ψ).app _).symm
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := (hS a).isLocallyFinitelyPresented _
      exact lfp_of_comap (inv φ)
        (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ (hm _).symm

private theorem continuous_coefficient_iso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj F)) := by
  let f : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let F : PadicAlgCl.FiniteIntermediateField ℓ :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  have : FiniteDimensional ℚ_[ℓ] F := F.property
  let e : E ≃ₐ[ℚ_[ℓ]] F := f.equivFieldRange
  have he : Continuous e := e.toLinearMap.continuous_of_finiteDimensional
  have hei : Continuous e.symm := e.symm.toLinearMap.continuous_of_finiteDimensional
  exact ⟨F, ⟨coefficientMonIso e.toRingEquiv he hei⟩⟩

private theorem continuous_generators (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
      boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj E) X) := by
  obtain ⟨F, ⟨e⟩⟩ := continuous_coefficient_iso.{u} ℓ E
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj F) X)) :
      IsConstructibleModuleObject (condensedRingObj (Profinite.continuousMapRingObj F) X) M ↔
        IsConstantModelConstructible (Profinite.continuousMapRingObj F) X M := by
    rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      have : TopologicalSpace.NoetherianSpace (S.domain a) :=
        (S.immersion a).isEmbedding.isInducing.noetherianSpace
      let φ := condensedPullbackHom (Profinite.continuousMapRingObj F) (S.immersion a)
      have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
        ((Mod.extendScalarsIsoComapInv φ).app _).symm
      obtain ⟨U, hU⟩ := finite_lf ℓ F _ _ h
      apply free_hasConstantModel (Profinite.continuousMapRingObj F) _
      refine ⟨U, fun i ↦ ?_⟩
      let ψ := condensedPullbackHom (Profinite.continuousMapRingObj F) (U.f i)
      exact free_of_iso (free_comap (inv ψ) (hU i))
        ((Mod.extendScalarsIsoComapInv ψ).app _).symm
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      let φ := condensedPullbackHom (Profinite.continuousMapRingObj F) (S.immersion a)
      have h := (hS a).isLocallyFinitelyPresented _
      exact lfp_of_comap (inv φ)
        (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
  have hm := comparison_transport e X hmod
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ (hm _).symm

private theorem integral_coefficient_iso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E) ≅
        Mon.mk (Profinite.padicIntegersRingObj ℓ F)) := by
  let f := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let F : PadicAlgCl.FiniteIntermediateField ℓ :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  let e : E ≃ₐ[ℚ_[ℓ]] F := f.equivFieldRange
  let t : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ F :=
    { toFun := fun x ↦ ⟨e x.val, x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, by
        have h := (PadicAlgCl.mem_integers_iff ℓ F x.val).mp x.property
        change ‖algebraMap E (PadicAlgCl ℓ) (e.symm x.val)‖₊ ≤ 1
        change ‖(e (e.symm x.val)).val‖₊ ≤ 1
        simpa only [e.apply_symm_apply, IntermediateField.algebraMap_apply] using h⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let := PadicAlgCl.normedFieldOfAlgebra ℓ F
  have ht : Isometry t := by
    apply Isometry.of_dist_eq
    intro x y
    rfl
  have hti : Continuous t.symm :=
    (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  exact ⟨F, ⟨coefficientMonIso t ht.continuous hti⟩⟩

-- The spectral and embedded valuations agree by uniqueness of the extended norm.
private theorem spectral_embedded_norm
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E)] (x : ULift.{u} E) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E) x =
      ‖(algebraMap E (PadicAlgCl ℓ) x.down)‖ := by
  let f : ULift.{u} E →+* PadicAlgCl ℓ :=
    (algebraMap E (PadicAlgCl ℓ)).comp ULift.ringEquiv.toRingHom
  let a : AbsoluteValue (ULift.{u} E) ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
      add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
  have ha : ∀ y : ℚ_[ℓ], a (algebraMap ℚ_[ℓ] (ULift.{u} E) y) = ‖y‖ := by
    intro y
    change ‖algebraMap E (PadicAlgCl ℓ) (algebraMap ℚ_[ℓ] E y)‖ = ‖y‖
    rw [← IsScalarTower.algebraMap_apply ℚ_[ℓ] E (PadicAlgCl ℓ)]
    exact PadicAlgCl.norm_extends ℓ y
  exact (spectralNorm_unique_field_norm_ext ha x).symm
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private theorem mem_lift_integers
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E)] (x : ULift.{u} E) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} E) ↔
      x.down ∈ PadicAlgCl.integers ℓ E := by
  have h := (Padic.coefficientExtensionIntegers_dvr ℓ (ULift.{u} E)).choose_spec.1 x
  rw [spectral_embedded_norm ℓ E x] at h
  exact h.trans (by
    rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
    rfl)

private noncomputable def latticeLiftEquiv
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    PadicAlgCl.integers ℓ E ≃+* latticeCoefficientIntegers ℓ (ULift.{u} E) where
  toFun x := ⟨WithAbs.toAbs _ (ULift.up x.val), (mem_lift_integers ℓ E _).mpr x.property⟩
  invFun x := ⟨x.val.ofAbs.down, (mem_lift_integers ℓ E _).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable def latticeLiftHomeo
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    PadicAlgCl.integers ℓ E ≃ₜ latticeCoefficientIntegers ℓ (ULift.{u} E) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let e := latticeLiftEquiv.{u} ℓ E
  have hi : Isometry e := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    change Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E)
      (ULift.up (x.val - y.val)) = ‖algebraMap E (PadicAlgCl ℓ) (x.val - y.val)‖
    exact spectral_embedded_norm ℓ E _
  exact { e.toEquiv with
    continuous_toFun := hi.continuous
    continuous_invFun := (hi.right_inv e.right_inv).continuous }

private noncomputable def latticeRingSheafIso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    Profinite.padicIntegersCondensedRing.{u} ℓ E ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (latticeCoefficientIntegers ℓ (ULift.{u} E)) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let e := latticeLiftEquiv.{u} ℓ E
  let h := latticeLiftHomeo.{u} ℓ E
  let forward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E) →+*
        ULift.{u + 1} C(S.unop, latticeCoefficientIntegers ℓ (ULift.{u} E)) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.toRingHom.compLeftContinuous _ h.continuous_toFun).comp ULift.ringEquiv.toRingHom)
  let backward (S : Profinite.{u}ᵒᵖ) :
      ULift.{u + 1} C(S.unop, latticeCoefficientIntegers ℓ (ULift.{u} E)) →+*
        ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.compLeftContinuous _ h.continuous_invFun).comp
        ULift.ringEquiv.toRingHom)
  refine
    { hom := ⟨{ app := fun S ↦ RingCat.ofHom (forward S)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun S ↦ RingCat.ofHom (backward S)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S x
    apply ULift.ext
    ext t
    rfl
  · ext S x
    apply ULift.ext
    ext t
    rfl

private theorem integral_generators (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X] :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X =
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) := by
  let q := latticeRingSheafIso.{u} ℓ E
  let F := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  let e0 := F.mapIso q
  have : IsMonHom e0.hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  let e : Mon.mk (Profinite.padicIntegersRingObj ℓ E) ≅
      Mon.mk (integralCondensedRing ℓ (ULift.{u} E)) := Mon.mkIso' e0
  have hm := comparison_transport e X
    (integralLfpConstantModelComparison ℓ (ULift.{u} E) X)
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ (hm _).symm

-- The three certificates therefore have the same bounded constructible generators.
private theorem certified_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] [IsLocallyNoetherian X]
    [TopologicalSpace.NoetherianSpace X] :
    IsLocalizingAdmissibleCoefficient ℓ Λ ∧
      (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        boundedConstructible (condensedRingObj Λ X) := by
  cases hΛ with
  | continuous E =>
    obtain ⟨F, he⟩ := continuous_coefficient_iso.{u} ℓ E
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨F, he⟩))), ?_⟩
    have ht := (localizingClosure_ctf_equals_bc ℓ X
      (Profinite.continuousMapRingObj E)
      (Or.inr (Or.inr (Or.inl ⟨F, Or.inr he⟩)))).1.2.2.1
    exact ht.trans (continuous_generators ℓ E X)
  | integral E =>
    obtain ⟨F, he⟩ := integral_coefficient_iso.{u} ℓ E
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, he⟩)))), ?_⟩
    have ht := (localizingClosure_ctf_equals_bc ℓ X
      (Profinite.padicIntegersRingObj ℓ E)
      (Or.inr (Or.inr (Or.inl ⟨F, Or.inl he⟩)))).1.2.2.1
    exact ht.trans (integral_generators ℓ E X)
  | algebraicClosure =>
    refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))), ?_⟩
    have ht := (localizingClosure_ctf_equals_bc ℓ X
      (Profinite.padicAlgClRingObj ℓ)
      (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))).1.2.2.1
    exact ht.trans (generators_of_localFree _ (algcl_lf ℓ) X)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local irreducible] upperStarFromPoint openImmersionLowerShriek lowerStar
  Functor.rightAdjoint

-- Compare the two coproduct-universe conventions using small support.
private theorem hull_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (heq : (constantModelBoundedConstructible Λ T ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) = boundedConstructible (condensedRingObj Λ T)) :
    localizingClosureProEtale Λ T = boundedConstructibleLocalizingClosure Λ T := by
  unfold localizingClosureProEtale
  rw [heq]
  have he : localizingClosure (boundedConstructible (condensedRingObj Λ T)) =
      localizingClosureOfSize.{u + 1} (boundedConstructible (condensedRingObj Λ T)) :=
    CategoryTheory.Functor.closure_index_eq.{u + 1, u + 1, u + 2} _
  rw [he]
  apply le_antisymm
  · intro K hK
    apply hK
    · exact ⟨inferInstance, inferInstance, fun {I} A hA h ↦ by
        have := hA
        exact (boundedConstructibleLocalizingClosure Λ T).prop_colimit A
          (fun i ↦ h i.as)⟩
    · exact boundedConstructible_le_localizingClosure Λ T
  · intro K hK P hP hS
    have := hP.1
    have := hP.2.1
    have (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) :=
      hP.isClosedUnderColimitsOfShape_discrete I
    exact boundedConstructibleLocalizingClosure_le Λ T P hS K hK

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- The exceptional-inverse-image data the restriction arguments use: the lower shriek of the
chosen compactification on the localizing closures, its comparison with every
compactification, and a right adjoint preserving `D_ctf`
(blueprint: theorem-exceptional-inverse-image, clauses (2)--(4)). -/
private def ExceptionalKey : Prop :=
  ∃ h : ∀ K, localizingClosureProEtale Λ Z.left K → localizingClosureProEtale Λ Y.left
      ((rightDerivedLowerShriekOfCompactification Λ (compactificationOverField g)).obj K),
    (∀ c : Compactification g.left, Nonempty
      ((localizingLowerShriek Λ (compactificationOverField g) h) ⋙
          (localizingClosureProEtale Λ Y.left).ι ≅
        (localizingClosureProEtale Λ Z.left).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)) ∧
    ∃ H : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
        (localizingClosureProEtale Λ Z.left).FullSubcategory,
      Nonempty (localizingLowerShriek Λ (compactificationOverField g) h ⊣ H) ∧
      ∀ N : (localizingClosureProEtale Λ Y.left).FullSubcategory,
        (constantModelBoundedConstructible Λ Y.left ⊓
          _root_.DerivedCategory.finiteTorAmplitude _) N.obj →
        (constantModelBoundedConstructible Λ Z.left ⊓
          _root_.DerivedCategory.finiteTorAmplitude _) (H.obj N).obj

omit [IsProper (Over.Hom.left g)] in
/-- The data for `E` and `Q̄_ℓ`, from Brown representability and the rational restriction
theorem alone (blueprint: theorem-f-shriek-ell-adic-coefficients). -/
private theorem exceptionalKey_rational
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    (hr : ((∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))) :
    ExceptionalKey Λ g :=
  rationalExceptionalInverseImage_exists (hcd := hcd) Λ ℓ k g hr

/-- The canonical Brown right adjoint has finite cohomological amplitude on bounded
constructible inputs.  This is the geometric restriction step of the blueprint proof.

Source: blueprint `det-existence-restriction.proof.md`, Part (2), rational and integral
restriction theorems and their coefficient comparison.
Proof: identify the canonical Brown right adjoint with the geometric exceptional inverse
image on finite affine charts, apply the rational and integral restriction theorems, and
take a common bound over the finite affine cover.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded-canonical)
-/
private theorem canonical_isBounded_of_key (hkey : ExceptionalKey Λ g)
    (hF : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF).obj
          ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : IsNoetherian Y.left := ⟨⟩
  obtain ⟨_, hX⟩ := certified_comparison Λ ℓ hΛ Z.left
  have hY := (certified_comparison Λ ℓ hΛ Y.left).2
  classical
  let LX := localizingClosureProEtale Λ Z.left
  let LY := localizingClosureProEtale Λ Y.left
  have eX := hull_eq Λ Z.left hX
  have eY := hull_eq Λ Y.left hY
  let jX := ObjectProperty.ιOfLE (le_of_eq eX)
  let jY := ObjectProperty.ιOfLE (le_of_eq eY)
  let iX := ObjectProperty.ιOfLE (le_of_eq eX.symm)
  let F := ellAdicLocalizingLowerStar Λ ℓ g hΛ
  let H := @Functor.rightAdjoint _ _ _ _ F hF
  let adjH : F ⊣ H := @Adjunction.ofIsLeftAdjoint _ _ _ _ F hF
  obtain ⟨h, hcomp, G, ⟨adjG⟩, hG⟩ := hkey
  let eShriek : openImmersionLowerShriek Λ (𝟙 Z.left) ≅ 𝟭 _ :=
    ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 Z.left)).ofNatIsoRight
      (upperStarId Λ Z.left)).leftAdjointUniq Adjunction.id
  let eId : (openImmersionLowerShriek Λ (𝟙 Z.left)).mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryNatIso eShriek ≪≫ Functor.mapDerivedCategoryIdIso _
  let ec : rightDerivedLowerShriekOfCompactification Λ
      (Compactification.ofIsProper g.left) ≅ R((g.left)_*⟦Λ⟧) :=
    Functor.isoWhiskerRight eId _ ≪≫ Functor.leftUnitor _
  obtain ⟨bc⟩ := hcomp (Compactification.ofIsProper g.left)
  let beta : localizingLowerShriek Λ (compactificationOverField g) h ⋙ LY.ι ≅
      LX.ι ⋙ R((g.left)_*⟦Λ⟧) :=
    bc ≪≫ Functor.isoWhiskerLeft LX.ι ec
  let J := jY ⋙ H ⋙ iX
  let FStar := (LY).lift (LX.ι ⋙ R((g.left)_*⟦Λ⟧))
    (fun A ↦ (le_of_eq eY.symm) _
      (ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ A.obj (jX.obj A).property))
  let alpha : localizingLowerShriek Λ (compactificationOverField g) h ≅ FStar :=
    NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk LY (beta.app A)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact beta.hom.naturality f)
  let adjJ : FStar ⊣ J := adjH.restrictFullyFaithful
    (iC := jX) (iD := jY) (L := FStar) (R := J)
    (ObjectProperty.fullyFaithfulιOfLE (le_of_eq eX))
    (ObjectProperty.fullyFaithfulιOfLE (le_of_eq eY))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intros
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intros
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
  let eg : G ≅ J := adjG.rightAdjointUniq (adjJ.ofNatIsoLeft alpha.symm)
  let N : LY.FullSubcategory := ⟨K.obj, (le_of_eq eY.symm) _
    (boundedConstructible_le_localizingClosure Λ Y.left K.obj K.property)⟩
  have hN : (constantModelBoundedConstructible Λ Y.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) N.obj := (congrFun hY K.obj).mpr K.property
  have hGK := hG N hN
  have hJK : (constantModelBoundedConstructible Λ Z.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (J.obj N).obj := by
    have hprop := (constantModelConstructibleFiniteTor_wellDefined Λ Z.left).2.1
    exact (constantModelBoundedConstructible Λ Z.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso (LX.ι.mapIso (eg.app N)) hGK
  have hbnd := hJK.1.1
  change (∃ a, _) ∧ (∃ b, _) at hbnd
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hbnd
  let M := (J.obj N).obj
  have : M.IsGE a := ha
  have : M.IsLE b := hb
  refine ⟨a, b, fun i hi ↦ ?_⟩
  change IsZero ((DerivedCategory.homologyFunctor _ i).obj M)
  rcases hi with hi | hi
  · exact DerivedCategory.isZero_of_isGE M a i hi
  · exact DerivedCategory.isZero_of_isLE M b i hi

/-- The supplied localizing right adjoint has finite cohomological amplitude on a bounded
constructible input.

Source: blueprint `theorem-exceptional-inverse-image` (4), `det-existence-restriction.proof.md`,
Part (2). Proof: use the finite affine factorization of the proper map and the boundedness part of
the rational restriction theorem, or its compatible integral torsion-level analogue.  A
finite affine cover gives a common pair of cohomological bounds; uniqueness of right
adjoints transports these bounds from the geometric construction to the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/
private theorem isBounded_of_key (hkey : ExceptionalKey Λ g)
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  let F := ellAdicLocalizingLowerStar Λ ℓ g hΛ
  let hF : F.IsLeftAdjoint := ellAdic_isLeftAdjoint_localizingLowerStar Λ ℓ g hΛ
  let H := @Functor.rightAdjoint _ _ _ _ F hF
  let adjH : F ⊣ H := @Adjunction.ofIsLeftAdjoint _ _ _ _ F hF
  obtain ⟨a, b, hb⟩ := canonical_isBounded_of_key Λ ℓ g hΛ hkey hF K
  let e := adjH.rightAdjointUniq adj
  refine ⟨a, b, fun i hi ↦ ?_⟩
  let e' := (boundedConstructibleLocalizingClosure Λ Z.left).ι.mapIso
    (e.app ((boundedConstructibleToLocalizing Λ Y.left).obj K))
  exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e'.symm)

/-- The bound of `ellAdic_localizing_rightAdjoint_obj_isBounded` for the coefficients `E`
and `Q̄_ℓ`, through the rational restriction theorem only.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded) -/
theorem ellAdic_localizing_rightAdjoint_obj_isBounded_rational
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    (hr : ((∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))))
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) :=
  isBounded_of_key Λ ℓ g hΛ (exceptionalKey_rational (hcd := hcd) Λ ℓ g hr) G adj K

end AlgebraicGeometry.ProEtale.CondensedRing
