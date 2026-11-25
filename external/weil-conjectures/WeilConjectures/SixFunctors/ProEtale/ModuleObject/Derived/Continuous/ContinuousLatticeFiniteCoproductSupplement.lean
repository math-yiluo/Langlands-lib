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
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
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
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import all Mathlib.NumberTheory.Padics.PadicNumbers
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
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.AlgebraicGeometry.ContinuousLatticeFiniteCoproduct

/-! # Integral lattices on finite disjoint unions

Source: Stacks Project, Tag 04TR, sheaf gluing; Bhatt--Scholze, Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-lattice-finite-coproduct)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma locallyFree_of_extendScalars {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj T] [IsCommMonObj R]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree T ((Mod.extendScalars φ).obj P)) : LocallyFree R P := by
  exact locallyFree_of_iso ((Mod.comapEquivalenceOfIsIso φ).counitIso.app P)
    (locallyFree_comap φ
      (locallyFree_of_iso ((Mod.extendScalarsIsoComapInv φ).app P) hP))

private lemma module_isZero_of_underlying
    {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (h : IsZero M.X) :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (Mod.forget R).map_injective
  exact h.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private lemma pull_push_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U V : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : V ⟶ X)
    (h : Set.range g.base ∩ Set.range j.base = ∅)
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    IsZero ((upperStar Λ j).obj ((lowerStar Λ g).obj M)) := by
  apply module_isZero_of_underlying
  apply IsZero.of_iso _ ((profinitePointModuleForgetPullbackIso Λ j).app _)
  apply IsZero.of_iso _ ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  apply Sheaf.isZero_of_isZero_obj
  rintro ⟨T⟩
  let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
    ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
  have : IsEmpty W.left := by
    refine ⟨fun w ↦ ?_⟩
    have hw : (pullback.fst (T.hom ≫ j) g ≫ T.hom ≫ j).base w ∈
        Set.range g.base ∩ Set.range j.base := by
      refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) g w), rfl⟩⟩
      rw [pullback.condition]
      exact ⟨_, rfl⟩
    rw [h] at hw
    exact hw
  exact (isZero_zero Ab.{u + 1}).of_iso
    ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X W).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

private lemma pull_shriek_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U V : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : V ⟶ X)
    (h : Set.range j.base ∩ Set.range g.base = ∅)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsZero ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)) := by
  have hinit : IsInitial ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)) := by
    refine IsInitial.ofUnique (h := fun N ↦ ?_)
    have hz := pull_push_zero Λ j g (by rw [Set.inter_comm]; exact h) N
    letI : Unique (M ⟶ (upperStar Λ j).obj ((lowerStar Λ g).obj N)) :=
      ⟨⟨hz.isTerminal.from M⟩, fun f ↦ hz.isTerminal.hom_ext f _⟩
    exact Equiv.unique
      (((upperStarLowerStarAdjunction Λ g).homEquiv _ N).trans
        ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M _))
  exact (isZero_zero _).of_iso (hinit.uniqueUpToIso HasZeroObject.zeroIsInitial)

private lemma module_iso_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {I : Type u} (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ x : X, ∃ (i : I) (y : Y i), j i y = x)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) (hf : ∀ i, IsIso ((upperStar Λ (j i)).map f)) : IsIso f := by
  have hsheaf : IsIso f.hom := by
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom j
    · apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
      exact (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hj, fun _ ↦ inferInstance⟩
    · intro i
      have : IsIso ((ProEtale.upperStar Ab.{u + 1} (j i)).map f.hom) := by
        have : IsIso ((upperStar Λ (j i)).map f) := hf i
        have : IsIso ((Mod.forget _).map ((upperStar Λ (j i)).map f)) := inferInstance
        exact (NatIso.isIso_map_iff (profinitePointModuleForgetPullbackIso Λ (j i)) f).mp
          (show IsIso ((Mod.forget _).map ((upperStar Λ (j i)).map f)) from
            inferInstance)
      exact (NatIso.isIso_map_iff
        (ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} (j i)) f.hom).mp
          (by infer_instance)
  have : IsIso ((Mod.forget _).map f) := hsheaf
  exact isIso_of_reflects_iso f (Mod.forget _)

attribute [local instance] Abelian.hasFiniteBiproducts

private lemma sigma_disjoint {I : Type u} (Y : I → Scheme.{u}) {s t : I} (hst : s ≠ t) :
    Set.range (Sigma.ι Y s).base ∩ Set.range (Sigma.ι Y t).base = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ hst ?_
  exact congrArg Sigma.fst ((sigmaι_eq_iff Y s t a b).mp (ha.trans hb.symm))

private lemma pull_biproduct_shriek_inclusion_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {I : Type u} [Finite I]
    (Y : I → Scheme.{u})
    (M : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      (condensedRingObj Λ (Y i))) (t : I) :
    IsIso ((upperStar Λ (Sigma.ι Y t)).map
      (biproduct.ι (fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)) t)) := by
  classical
  let := Fintype.ofFinite I
  let G := fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)
  let F := upperStar Λ (Sigma.ι Y t)
  have hz (s : I) (hst : s ≠ t) : IsZero (F.obj (G s)) :=
    pull_shriek_zero Λ _ _ (sigma_disjoint Y hst) (M s)
  refine ⟨F.map (biproduct.π G t), ?_, ?_⟩
  · rw [← F.map_comp, biproduct.ι_π_self, F.map_id]
  · rw [← F.map_comp, ← F.map_id, ← IsBilimit.total (biproduct.isBilimit G),
      F.map_sum, Finset.sum_eq_single t (fun s _ hst ↦ ?_) (by simp)]
    rw [F.map_comp, (hz s hst).eq_zero_of_tgt (F.map (biproduct.π G s)), zero_comp]

private theorem nonempty_pull_biproduct_shriek_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {I : Type u} [Finite I]
    (Y : I → Scheme.{u})
    (M : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      (condensedRingObj Λ (Y i))) (t : I) :
    Nonempty ((upperStar Λ (Sigma.ι Y t)).obj
      (⨁ fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)) ≅ M t) := by
  have := pull_biproduct_shriek_inclusion_isIso Λ Y M t
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  exact ⟨(asIso ((upperStar Λ (Sigma.ι Y t)).map (biproduct.ι _ t))).symm ≪≫
    (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit.app
      (M t))).symm⟩

private lemma biproduct_shriek_counit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {I : Type u} [Finite I]
    (Y : I → Scheme.{u})
    (G : Mod (Sheaf (Scheme.ProEt.topology (∐ Y)) Ab.{u + 1})
      (condensedRingObj Λ (∐ Y))) :
    IsIso (biproduct.desc (fun i ↦
      (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y i)).counit.app G)) := by
  apply module_iso_of_cover Λ Y (Sigma.ι Y)
    (fun x ↦ (sigmaOpenCover Y).exists_eq x)
  intro t
  let F := upperStar Λ (Sigma.ι Y t)
  have := pull_biproduct_shriek_inclusion_isIso Λ Y (fun i ↦
    (upperStar Λ (Sigma.ι Y i)).obj G) t
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hε : IsIso (F.map
      ((openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).counit.app G)) := by
    let adj := openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)
    have ht := adj.right_triangle_components G
    have : IsIso (adj.unit.app (F.obj G) ≫ F.map (adj.counit.app G)) := by
      rw [ht]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app (F.obj G)) _
  have : IsIso (F.map (biproduct.ι _ t) ≫ F.map (biproduct.desc (fun i ↦
      (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y i)).counit.app G))) := by
    rw [← F.map_comp, biproduct.ι_desc]
    exact hε
  have hι : IsIso (F.map (biproduct.ι (fun i ↦
      ((upperStar Λ (Sigma.ι Y i)) ⋙
        (openImmersionLowerShriek Λ (Sigma.ι Y i))).obj G) t)) :=
    pull_biproduct_shriek_inclusion_isIso Λ Y (fun i ↦
      (upperStar Λ (Sigma.ι Y i)).obj G) t
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hι ‹_›

end AlgebraicGeometry.ProEtale.CondensedRing
