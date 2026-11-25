/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleOpenClosedImages
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Integral inverse image and uncompleted tensor

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor/_section.md;
Stacks Project, Tags 09BP, 09BM and 09AA (blueprint: lemma-inverse-image-tensor-product).

The completed inverse-image comparison uses the existing intrinsic completeness
predicate from IntegralModelsEmbedded, applied to the ordinary inverse image.
The principal Koszul completion criterion identifies this with invertibility of
the canonical quotient completion unit. Uniformizer powers and ell powers are
cofinal. The explicit ell-power cone reductions below remain available as models
of these reductions, with their canonical inclusions and transition squares.
No arbitrary comparison morphism or completion object is selected.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- As in the upstream bounded-constructible module, keep internal Hom constructions opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- A concrete model of the uncompleted derived reduction of a complex P.
The two-term flat resolution [O_E --ell^(n+1)--> O_E] of O_E/ell^(n+1)
shows that this cone represents P tensor^L O_E/ell^(n+1), without any flatness
assumption on P. Source: Stacks 099M and 099N (blueprint: lemma-inverse-image-tensor-product). -/
abbrev integralFiniteComplex (X : Scheme.{u})
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ) (n : ℕ) :=
  CochainComplex.mappingCone (ℓ ^ (n + 1) • 𝟙 P)

/-- The canonical completed inverse-image comparison is invertible when the ordinary
inverse image is derived complete. We use the existing intrinsic completeness predicate
on the equivalent small ringed site, with the actual first residue map. The witness
is a generator of the maximal ideal, not a comparison morphism or a completion object.

This is the same condition as the canonical ell-power cone triangle: exact inverse
image carries the two-term scalar resolutions, their quotient units and transitions
to those on the target. Uniformizer powers and ell powers are cofinal. The principal
Koszul completion criterion identifies intrinsic completeness with invertibility of
that quotient unit; its Roos triangle has the prescribed cone-inclusion product leg.
Exact restriction of scalars preserves products and triangles and detects isomorphisms,
so this is also the completed inverse image after restriction to constant O_E.
Source: Stacks 099M, 099N(5), 0999 and 0A0E; integral models, clause (2)
(blueprint: lemma-inverse-image-tensor-product). -/
def IntegralPullbackIsCompleted {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y))) : Prop :=
  ∃ π : PadicAlgCl.integers ℓ E.val,
    Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.val) ∧
      IntegralModelsEmbedded.completedComplete ℓ E π X
        (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj K)

/-- Integral inverse image, its completed comparison, uncompleted tensor, extension by
zero for a quasi-compact open immersion, and closed direct image preserve Dbc.

Source: blueprint main-20261015, lemma-inverse-image-tensor-product; Stacks 09BP, 09BM and 09AA
(blueprint: lemma-inverse-image-tensor-product).

Proof:
1. The existing exact derived inverse-image preservation theorem gives bounded
constructibility. The coefficient-predicate comparison identifies this with finite
constant-model constructibility. Clause (2) of integral_models then gives intrinsic
derived completeness of the image, for a generator of the maximal ideal. The
canonical completion criterion in IntegralPullbackIsCompleted identifies this with
the completed inverse image, retaining the canonical quotient unit.
2. Apply the existing integral instance of boundedConstructible_tensor_closure,
which proves closure for the ambient uncompleted derived tensor by finite devissage.
3. Apply the exact open-extension preservation theorem.
4. For a closed immersion, condensed open-closed recollement supplies exactness.
The exact derived homology comparisons and constructible closed-image theorem give
bounded constructibility. Identify the exact and right-derived presentations.
-/
theorem integralTensorInverseImage (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
          (((upperStar (Profinite.padicIntegersRingObj ℓ E.val) g).leftDerivedFunctor).obj K) ∧
        IntegralPullbackIsCompleted ℓ E g K) ∧
    (∀ K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) L →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
        (((derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).obj K).obj L)) ∧
    (∀ (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)
        (((openImmersionLowerShriek
          (Profinite.padicIntegersRingObj ℓ E.val) j).mapDerivedCategory).obj K)) ∧
    (∀ (i : X ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) K →
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) Y)
        (((lowerStar (Profinite.padicIntegersRingObj ℓ E.val) i).rightDerivedFunctor).obj K)) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E.val
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : LocallyOfFiniteType (Over.mk (X ↘ Spec (.of k))).hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (Over.mk (X ↘ Spec (.of k))).hom := by
    change QuasiCompact (X ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (Over.mk (X ↘ Spec (.of k))).hom := by
    change IsSeparated (X ↘ Spec (.of k))
    infer_instance
  have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of k))).hom := by
    change LocallyOfFiniteType (Y ↘ Spec (.of k))
    infer_instance
  have : QuasiCompact (Over.mk (Y ↘ Spec (.of k))).hom := by
    change QuasiCompact (Y ↘ Spec (.of k))
    infer_instance
  have : IsSeparated (Over.mk (Y ↘ Spec (.of k))).hom := by
    change IsSeparated (Y ↘ Spec (.of k))
    infer_instance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    have hpull := boundedConstructible_leftDerivedUpperStar_obj Λ ℓ
      (X := Over.mk (X ↘ Spec (.of k))) (Y := Over.mk (Y ↘ Spec (.of k)))
      (Over.homMk g (CategoryTheory.comp_over g (Spec (.of k)))) ⟨K, hK⟩
    refine ⟨hpull, ?_⟩
    obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ℓ E.val
    have hπ' : Ideal.span {π} =
        IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.val) := hπ.symm
    refine ⟨π, hπ', ?_⟩
    have heq := (adicConstructibilityPredicateComparison ℓ X Λ
      (IsEllAdicCoefficient.integral E.val)).2
    have hconstant : constantModelBoundedConstructible Λ X
        (((upperStar Λ g).leftDerivedFunctor).obj K) := by
      rw [← heq]
      exact hpull
    exact (((integral_models k (ringChar k) ℓ (Ne.symm (Fact.out : ringChar k ≠ ℓ))
      X E π hπ').2.2.1 _).2.mp hconstant).1
  · intro K L hK hL
    exact PadicIntegersRingObj.boundedConstructible_tensor_closure
      (X := Over.mk (X ↘ Spec (.of k))) ℓ E.val K L hK hL
  · intro j _ _ _ K hK
    have : IsOpenImmersion (Over.homMk j (CategoryTheory.comp_over j
        (Spec (.of k))) : Over.mk (X ↘ Spec (.of k)) ⟶
          Over.mk (Y ↘ Spec (.of k))).left := by
      change IsOpenImmersion j
      infer_instance
    exact boundedConstructible_openImmersionLowerShriek_obj Λ ℓ
      (U := Over.mk (X ↘ Spec (.of k))) (X := Over.mk (Y ↘ Spec (.of k)))
      (Over.homMk j (CategoryTheory.comp_over j (Spec (.of k)))) ⟨K, hK⟩
  · intro i _ _ K hK
    have : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
      (Y ↘ Spec (.of k))
    have : IsNoetherian Y := ⟨⟩
    let U : Y.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨hex, _⟩ := condensed_open_closed_recollement Λ i U.ι U.range_ι
    let := hex
    let e := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app K
    refine ⟨(DerivedCategory.TStructure.t.bounded).prop_of_iso e.symm
      ((lowerStar Λ i).bounded_mapDerivedCategory_obj hK.1), fun n ↦ ?_⟩
    exact _root_.constructible_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso e.symm)
      (_root_.constructible_of_iso
        (((lowerStar Λ i).mapDerivedCategoryHomologyFunctorIso n).app K)
        ((constructible_open_closed_images Λ U.ι i U.range_ι).2 _ (hK.2 n)))

end AlgebraicGeometry.ProEtale.CondensedRing
