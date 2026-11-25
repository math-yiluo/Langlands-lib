/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFunctionPresentationRange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleLatticeSheetMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeFiniteCover
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
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
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFreeSheetFrames

/-! # Continuous matrices for the sheet embeddings

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2.
(blueprint: lem-sfb-continuous-finite-etale-sheet-matrices)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar upperStarComp continuousRingModuleEquivalence
  finiteEtaleLatticeSheetEmbedding

/-- A splitting by sections stays a splitting under arbitrary base change. -/
private theorem split_cofan_refine {X U Y Z : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X)
    (d : ℕ) (t : Fin d → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (a : Z ⟶ Y) (w' : ∀ j, (a ≫ t j) ≫ p = a ≫ g) :
    Nonempty (IsColimit (Cofan.mk (pullback p (a ≫ g))
      (fun j ↦ pullback.lift (a ≫ t j) (𝟙 Z) (by simpa using w' j)))) := by
  let i (j : Fin d) := pullback.lift (t j) (𝟙 Y) (by simpa using w j)
  let i' (j : Fin d) := pullback.lift (a ≫ t j) (𝟙 Z) (by simpa using w' j)
  let b : pullback p (a ≫ g) ⟶ pullback p g :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by
      rw [Category.assoc, pullback.condition])
  have hi (j : Fin d) : i' j ≫ b = a ≫ i j := by
    apply pullback.hom_ext
    · simp [i, i', b]
    · simp only [i, i', b, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  let s (j : Fin d) : PullbackCone b (i j) := PullbackCone.mk (i' j) a (hi j)
  have hs (j : Fin d) : IsLimit (s j) := by
    refine PullbackCone.IsLimit.mk _ (fun c ↦ c.fst ≫ pullback.snd _ _) ?_ ?_ ?_
    · intro c
      apply pullback.hom_ext
      · have h₁ := congrArg (fun f ↦ f ≫ pullback.fst p g) c.condition
        have h₂ := congrArg (fun f ↦ f ≫ pullback.snd p g) c.condition
        have h₂' : c.fst ≫ pullback.snd p (a ≫ g) ≫ a = c.snd := by
          simpa [s, i, b, Category.assoc] using h₂
        simp only [Category.assoc, i', pullback.lift_fst]
        calc
          _ = c.snd ≫ t j := by
            simpa only [Category.assoc] using congrArg (fun v ↦ v ≫ t j) h₂'
          _ = _ := by simpa [s, i, b, Category.assoc] using h₁.symm
      · simp [i']
    · intro c
      have h := congrArg (fun f ↦ f ≫ pullback.snd p g) c.condition
      simpa [s, i, b, Category.assoc] using h
    · intro c m hm _
      have h := congrArg (fun f ↦ f ≫ pullback.snd p (a ≫ g)) hm
      simpa [s, i', Category.assoc] using h
  let hu := FinitaryPreExtensive.isUniversal_finiteCoproducts hc.some
  exact hu.nonempty_isColimit_of_pullbackCone_left i (𝟙 _) b s hs
    (PullbackCone.mk (𝟙 _) b (by simp)) (IsPullback.id_horiz b).isLimit
    (Cofan.mk _ i') (Iso.refl _) (by intro j; rfl) (by simp [s])
    (by intro j; simpa [s] using hi j)

/-- Use a finite common refinement without reducing any coefficient-module objects. -/
private theorem finite_cover_property {Y : Scheme.{u}} {I : Type} [Finite I]
    (Q : ∀ Z : Scheme.{u}, (Z ⟶ Y) → I → Prop)
    (href : ∀ {Z W : Scheme.{u}} (a : W ⟶ Z) (b : Z ⟶ Y) (i : I),
      Q Z b i → Q W (a ≫ b) i)
    (h : ∀ i, ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y,
      ∀ k : D.I₀, Q (D.X k) (D.f k) i) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y,
      ∀ s : C.I₀, ∀ i, Q (C.X s) (C.f s) i := by
  obtain ⟨D, hD⟩ := Classical.skolem.mp h
  obtain ⟨C, hC⟩ := finiteCommonCover D
  refine ⟨C, fun s i ↦ ?_⟩
  obtain ⟨k, a, ha⟩ := hC s i
  exact ha ▸ href a ((D i).f k) i (hD i k)

/-- Transport freeness across the normalized composition comparison once. -/
private theorem free_over_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (a : Z ⟶ Y) (g : Y ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : Mod.IsFree (condensedRingObj Λ Z)
      ((upperStar Λ a).obj ((upperStar Λ g).obj P))) :
    Mod.IsFree (condensedRingObj Λ Z) ((upperStar Λ (a ≫ g)).obj P) :=
  ProEtale.free_of_iso h ((upperStarComp Λ a g).app P).symm

/-- A free cover for a pullback, stated using the composite base morphism. -/
private theorem cover_free_composite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : LocallyFree (condensedRingObj Λ X) P) (g : Y ⟶ X) :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ k : D.I₀,
      Mod.IsFree (condensedRingObj Λ (D.X k)) ((upperStar Λ (D.f k ≫ g)).obj P) := by
  obtain ⟨D, hD⟩ := locallyFree_upperStar Λ g hP
  exact ⟨D, fun k ↦ free_over_comp Λ (D.f k) g P
    (isFree_upperStar_of_isFree_mapMod (D.f k) (hD k))⟩

/-- Simultaneously make a rational module and finitely many integral sheet modules free. -/
private theorem simultaneous_free_cover
    (Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    {X U Y : Scheme.{u}}
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : LocallyFree (condensedRingObj Λ X) P)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Γ U))
    (hM : LocallyFree (condensedRingObj Γ U) M)
    (g : Y ⟶ X) (d : ℕ) (t : Fin d → (Y ⟶ U)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ s : C.I₀,
      Mod.IsFree (condensedRingObj Λ (C.X s)) ((upperStar Λ (C.f s ≫ g)).obj P) ∧
      ∀ j, Mod.IsFree (condensedRingObj Γ (C.X s))
        ((upperStar Γ (C.f s ≫ t j)).obj M) := by
  let Q (Z : Scheme.{u}) (a : Z ⟶ Y) : Option (Fin d) → Prop
    | none => Mod.IsFree (condensedRingObj Λ Z) ((upperStar Λ (a ≫ g)).obj P)
    | some j => Mod.IsFree (condensedRingObj Γ Z) ((upperStar Γ (a ≫ t j)).obj M)
  have href {Z W : Scheme.{u}} (a : W ⟶ Z) (b : Z ⟶ Y) (i : Option (Fin d)) :
      Q Z b i → Q W (a ≫ b) i := by
    cases i with
    | none =>
      intro h
      simpa only [Q, Category.assoc] using free_standard_refine Λ (b ≫ g) a P h
    | some j =>
      intro h
      simpa only [Q, Category.assoc] using free_standard_refine Γ (b ≫ t j) a M h
  have hlocal (i : Option (Fin d)) :
      ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y,
        ∀ k : D.I₀, Q (D.X k) (D.f k) i := by
    cases i with
    | none => exact cover_free_composite Λ P hP g
    | some j => exact cover_free_composite Γ M hM (t j)
  obtain ⟨C, hC⟩ := finite_cover_property Q href hlocal
  exact ⟨C, fun s ↦ ⟨hC s none, fun j ↦ hC s (some j)⟩⟩

/-- Construct the splitting cover with two abstract families of local properties. -/
private theorem split_cover_with_property
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (R : ∀ Y : Scheme.{u}, (Y ⟶ U) → Prop)
    (hlocal : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) (d : ℕ) (t : Fin d → (Y ⟶ U)),
      ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ k : D.I₀,
        Q (D.X k) (D.f k ≫ g) ∧ ∀ j, R (D.X k) (D.f k ≫ t j)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      ∃ (d : ℕ) (_ : 0 < d) (t : Fin d → (C.X s ⟶ U))
        (w : ∀ j, t j ≫ p = C.f s),
        Nonempty (IsColimit (Cofan.mk (pullback p (C.f s))
          (fun j ↦ pullback.lift (t j) (𝟙 _) (by simpa using w j)))) ∧
        Q (C.X s) (C.f s) ∧ ∀ j, R (C.X s) (t j) := by
  classical
  choose Y g y hg hy d hd t w hs using exists_split_sections p
  obtain ⟨C, hC⟩ := exists_etale_cover_with_property Y g y hg hy
    (fun Z f ↦ ∃ (d : ℕ) (_ : 0 < d) (t : Fin d → (Z ⟶ U))
      (w : ∀ j, t j ≫ p = f), Nonempty (IsColimit (Cofan.mk (pullback p f)
        (fun j ↦ pullback.lift (t j) (𝟙 Z) (by simpa using w j)))))
    (fun x ↦ ⟨d x, hd x, t x, w x, hs x⟩)
  refine ProEtale.exists_cover_of_local_property C
    (fun Z f ↦ ∃ (d : ℕ) (_ : 0 < d) (t : Fin d → (Z ⟶ U))
      (w : ∀ j, t j ≫ p = f),
      Nonempty (IsColimit (Cofan.mk (pullback p f)
        (fun j ↦ pullback.lift (t j) (𝟙 Z) (by simpa using w j)))) ∧
      Q Z f ∧ ∀ j, R Z (t j)) ?_
  intro s
  obtain ⟨d, hd, t, w, hs⟩ := hC s
  obtain ⟨D, hD⟩ := hlocal (C.X s) (C.f s) d t
  refine ⟨D, fun k ↦ ?_⟩
  let t' (j : Fin d) := D.f k ≫ t j
  have w' (j : Fin d) : t' j ≫ p = D.f k ≫ C.f s := by
    dsimp [t']
    rw [Category.assoc, w]
  exact ⟨d, hd, t', w', split_cofan_refine p (C.f s) d t w hs (D.f k) w', hD k⟩

/-- The range of a matrix in integral continuous coordinates is tested by its inverse. -/
private theorem range_of_integral_frame
    {E : Type} [NormedField E] (A : Subring E)
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {r : ℕ} (G : Y → Matrix.GeneralLinearGroup (Fin r) E)
    (hGi : ∀ i k, Continuous (fun y ↦ ((G y)⁻¹).val i k))
    (a : Z → Y) (ha : Continuous a) {S : Type*}
    (c : S ≃ C(Z, Fin r → A)) (H : S → C(Z, Fin r → E))
    (hH : ∀ x z, H x z = (G (a z)).val *ᵥ (fun i ↦ (c x z i : E))) :
    Set.range H = {f : C(Z, Fin r → E) | ∀ z i,
      (((G (a z))⁻¹).val *ᵥ f z) i ∈ A} := by
  have hinv (g : Matrix.GeneralLinearGroup (Fin r) E) (v : Fin r → E) :
      (g⁻¹).val *ᵥ (g.val *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hmul (g : Matrix.GeneralLinearGroup (Fin r) E) (v : Fin r → E) :
      g.val *ᵥ ((g⁻¹).val *ᵥ v) = v := by
    simpa only [inv_inv] using hinv g⁻¹ v
  ext f
  constructor
  · rintro ⟨x, rfl⟩ z i
    rw [hH, hinv]
    exact (c x z i).property
  · intro hf
    let b : C(Z, Fin r → A) :=
      ⟨fun z i ↦ ⟨(((G (a z))⁻¹).val *ᵥ f z) i, hf z i⟩,
        continuous_pi (fun i ↦ Continuous.subtype_mk
          (show Continuous (fun z ↦ (((G (a z))⁻¹).val *ᵥ f z) i) by
            change Continuous (fun z ↦ ∑ k : Fin r, ((G (a z))⁻¹).val i k * f z k)
            exact continuous_finsetSum _ (fun k _ ↦
              ((hGi i k).comp ha).mul ((continuous_apply k).comp f.continuous))) _)⟩
    refine ⟨c.symm b, ?_⟩
    apply ContinuousMap.ext
    intro z
    rw [hH, Equiv.apply_symm_apply]
    exact hmul (G (a z)) (f z)

/-- Local integral and rational frames describe the sheet embeddings by invertible
continuous matrices. No matrix coset is asserted to be constant.

Source: blueprint, stratified lattice trace proof, Local computation, paragraphs 1--2;
Bhatt--Scholze, Section 6.8, the continuous coefficient realization and local bases.
(blueprint: lem-sfb-continuous-finite-etale-sheet-matrices)

Proof. Split p on an etale covering using finite_etale_etale_local_split.
Replace each summand by its isomorphism with the base and reindex by Fin d.
On a nonempty member surjectivity of p makes d positive; omit empty members.
Pull back a rational free cover for P. Pull back the integral free cover for M
along each of the finitely many sections and take their common refinement.
Normalize all pullbacks by condensedPullbackHom and upperStarComp. The chosen
e and the scalar-extension comparison identify the rationalized integral
frames with the rational frame. Evaluation at a point shows that each integral
frame has the rational rank r. The coordinate matrix and its inverse have
continuous entries, since the continuous coefficient encoding takes a finite
free internal module to the corresponding sheaf of continuous vectors.
Use the inverse coordinate matrix to test whether a rational section is in
the image of the integral frame: every coordinate must lie in the integral
subring. This test is sufficient on every pro-etale object, since a continuous
function with values in a subspace is continuous into that subspace. Restrict
the same rational frame to every open W. Naturality of the extension unit and
of the composition comparisons gives the displayed test for the actual sheet
map, rather than an abstract isomorphic lattice. Coproduct splittings are stable
under this open base change, yielding the cofan assertion for W. Rank zero uses
empty matrices, and an empty base uses the empty cover. -/
theorem continuousFiniteEtaleLattice_sheet_matrices
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (hM : LocallyFree (condensedRingObj (integralCoeff l E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      ∃ (r d : ℕ) (_ : 0 < d) (t : Fin d → (C.X s ⟶ U))
        (_w : ∀ j, t j ≫ p = C.f s),
      ∃ G : Fin d → (C.X s) → Matrix.GeneralLinearGroup (Fin r) E,
        (∀ j i k, Continuous (fun y ↦ (G j y).val i k)) ∧
        (∀ j i k, Continuous (fun y ↦ ((G j y)⁻¹).val i k)) ∧
        ∀ W : (C.X s).Opens,
          ∃ w' : ∀ j, (W.ι ≫ t j) ≫ p = W.ι ≫ C.f s,
          Nonempty (IsColimit (Cofan.mk (pullback p (W.ι ≫ C.f s))
            (fun j ↦ pullback.lift (W.ι ≫ t j) (𝟙 W.toScheme)
              (by simpa using w' j)))) ∧
          ∃ c : ContinuousFunctionPresentation W.toScheme (continuousIntegers l E)
              (Fin r → E) ((Mod.comap
                (coefficientMap (integralScalarMap l E) W.toScheme)).obj
                ((upperStar (Profinite.continuousMapRingObj E) (W.ι ≫ C.f s)).obj P)),
            ∀ (j : Fin d) (B : W.toScheme.ProEt),
              continuousFunctionPresentationRange (continuousIntegers l E) c
                (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
                  (W.ι ≫ C.f s) (W.ι ≫ t j) (w' j)) B =
                {f : C(B.left, Fin r → E) | ∀ z i,
                  (((G j (W.ι (B.hom z)))⁻¹).val *ᵥ f z) i ∈ continuousIntegers l E} := by
  classical
  obtain ⟨C, hC⟩ := split_cover_with_property p
    (fun Y g ↦ Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj E) Y)
      ((upperStar (Profinite.continuousMapRingObj E) g).obj P))
    (fun Y t ↦ Mod.IsFree (condensedRingObj (integralCoeff l E) Y)
      ((upperStar (integralCoeff l E) t).obj M))
    (fun _ g d t ↦ simultaneous_free_cover (Profinite.continuousMapRingObj E)
      (integralCoeff l E) P hP M hM g d t)
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨d, hd, t, w, hsplit, hfreeP, hfreeM⟩ := hC s
  obtain ⟨r, G, hG, hGi, hframes⟩ := continuousFreeSheet_frames l E P p M e
    (C.f s) d t w hfreeP hfreeM
  refine ⟨r, d, hd, t, w, G, hG, hGi, ?_⟩
  intro W
  obtain ⟨wW, c, b, hcb⟩ := hframes W
  refine ⟨wW, split_cofan_refine p (C.f s) d t w hsplit W.ι wW, c, ?_⟩
  intro j B
  rw [continuousFunctionPresentationRange_eq]
  exact range_of_integral_frame (continuousIntegers l E) (G j) (hGi j)
    (fun z ↦ W.ι (B.hom z)) (W.ι.continuous.comp B.hom.continuous)
    ((b j).sections B).toEquiv _ (hcb j B)

end AlgebraicGeometry.ProEtale.CondensedRing
