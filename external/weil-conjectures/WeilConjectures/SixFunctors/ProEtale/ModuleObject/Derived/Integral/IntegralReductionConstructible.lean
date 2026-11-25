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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralReductionTriangulatedProperty
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.IntegralReductionTensor
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-! # Bounded constructibility of integral reduction

Source: Bhatt--Scholze, Proposition 6.8.11(3), and the finite free residue resolution.
(blueprint: lem-weil-pbc-integral-reduction-constructible)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralReductionConstructible
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

section Quotient

variable {X : Scheme.{u}}
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (q : R ⟶ S) [IsMonHom q] [Epi q]

omit [IsCommMonObj R] [IsCommMonObj S] in
private theorem full_comap_of_epi :
    (Mod.comap q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R).Full where
  map_surjective {M N} f := by
    have : Epi (q ▷ M.X) := (tensorRight M.X).map_epi q
    refine ⟨Mod.homMk f.hom ?_, ?_⟩
    · apply (cancel_epi (q ▷ M.X)).1
      let t : M.X ⟶ N.X := f.hom
      have hf : q ▷ M.X ≫ γ[S,M.X] ≫ t = R ◁ t ≫ q ▷ N.X ≫ γ[S,N.X] := by
        simpa only [Mod.act, Mod.comap_obj_smul, Category.assoc] using Mod.act_hom f
      rw [whisker_exchange_assoc] at hf
      exact hf
    · apply Mod.hom_ext
      rfl

omit [IsCommMonObj R] in
private theorem fp_of_iso {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) (e : M ≅ N) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ e'⟩⟩

private noncomputable def regularExtendIso :
    (Mod.extendScalars q).obj (Mod.regular R) ≅ Mod.regular S := by
  let B := Bimod.ofMonHom q
  let e₀ := Mod.toBimodRegularIso (R := R)
  let e₁ : B.tensorBimod ((Mod.toBimod R).obj (Mod.regular R)) ≅
      B.tensorBimod (Bimod.regular (Mon.mk R)) :=
    { hom := Bimod.whiskerLeft B e₀.hom
      inv := Bimod.whiskerLeft B e₀.inv
      hom_inv_id := by
        rw [← Bimod.whiskerLeft_comp_bimod, Iso.hom_inv_id]
        exact Bimod.whiskerLeft_id_bimod
      inv_hom_id := by
        rw [← Bimod.whiskerLeft_comp_bimod, Iso.inv_hom_id]
        exact Bimod.whiskerLeft_id_bimod }
  let e := e₁ ≪≫ Bimod.rightUnitorBimod B
  exact Mod.isoMk
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Bimod.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Bimod.Hom.hom e.inv_hom_id }
    e.hom.left_act_hom

omit [IsCommMonObj S] [Epi q] in
private theorem fp_extend {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars q).obj M) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := h
  let F := Mod.extendScalars q
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ regularExtendIso R S q)
  let f' := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso e ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

omit [IsCommMonObj S] in
private theorem fp_reflect {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFinitelyPresented R ((Mod.comap q).obj M)) :
    Mod.IsFinitelyPresented S M := by
  have : (Mod.comap q).Full := full_comap_of_epi R S q
  exact fp_of_iso S (fp_extend R S q h)
    (asIso ((Mod.extendRestrictAdjunction q).counit.app M))

omit [IsCommMonObj S] in
private theorem lfp_reflect {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented R ((Mod.comap q).obj M)) :
    IsLocallyFinitelyPresented S M := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (U.f i)
  exact fp_reflect (F.obj R) (F.obj S) (F.map q)
    (fp_of_iso _ (hU i) ((F.mapModComapIso q).app M))

omit [IsCommMonObj S] in
private theorem constructible_reflect
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsConstructibleModuleObject R ((Mod.comap q).obj M)) :
    IsConstructibleModuleObject S M := by
  obtain ⟨V, hV⟩ := h
  refine ⟨V, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (V.immersion i)
  exact lfp_reflect (F.obj R) (F.obj S) (F.map q)
    (_root_.localFinitePresentation_of_iso ((F.mapModComapIso q).app M) (hV i))

end Quotient

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- Derived reduction modulo ℓ preserves bounded constructible integral complexes.

Source: Bhatt--Scholze, Proposition 6.8.11(3), the two-term finite free residue resolution.
(blueprint: lem-weil-pbc-integral-reduction-constructible)

Proof. Constructible integral modules form a weak Serre class, so bounded constructible
integral complexes form a triangulated subcategory. Restricted derived reduction belongs
to this subcategory by the mapping-cone argument for multiplication by ℓ. Exact faithful
restriction of scalars reflects cohomological boundedness. It also reflects constructibility
along the quotient: restriction along an epimorphism of ring objects is fully faithful,
because an integral-linear map is residue-linear after cancellation of the epimorphism
q tensored with its source. Hence the extension-restriction counit is invertible.
Extension of scalars preserves finite presentations: apply it to the presentation,
identify the images of finite free modules with the corresponding residue finite free
modules, and use preservation of cokernels. Thus an integral finite presentation of a
restricted residue module gives a residue finite presentation. Inverse image commutes
with restriction, so the same argument on each presentation cover and stratum proves
reflection of constructibility. Apply it to each cohomology object, using exact
restriction's homology comparison. Empty covers, zero ranks, and zero modules are included.
-/
theorem integralReduction_boundedConstructible (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] (M : integralConstructible ℓ E X) :
    boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X)
      ((integralReduction ℓ E X).obj M.obj) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj (integralResidue ℓ E)) X
  let q := coefficientMap (integralReductionMap ℓ E) X
  have : Epi (integralReductionMap.{u} ℓ E) :=
    (integralReductionSequence_shortExact ℓ E).epi_g
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  have : Epi q := (upperStarFromPoint X).map_epi (integralReductionMap ℓ E)
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).1
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).2.1
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) :=
    (integralConstructible_serre ℓ E X).2.2
  let : (boundedConstructible R).IsTriangulated :=
    isTriangulated_boundedConstructible_of_serre R
      (fun _ _ f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
        ObjectProperty.prop_cokernel _ f hM hN⟩)
      (fun _ hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)
  have : (boundedConstructible R).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e h.1,
      fun n ↦ _root_.constructible_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (h.2 n)⟩⟩
  obtain ⟨ε, hε⟩ := integralReduction_restrictTensor ℓ E X
  have h := integralReduction_restricted_mem ℓ E X (boundedConstructible R)
    M.obj M.property ε hε
  refine ⟨(Mod.comap q).bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
  apply constructible_reflect R S q
  exact _root_.constructible_of_iso
    (((Mod.comap q).mapDerivedCategoryHomologyFunctorIso n).symm.app _)
    (h.2 n)

end AlgebraicGeometry.ProEtale.CondensedRing
