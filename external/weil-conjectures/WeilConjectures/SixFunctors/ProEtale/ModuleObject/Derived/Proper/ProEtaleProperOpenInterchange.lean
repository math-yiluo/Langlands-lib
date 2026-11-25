/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Compactification.Refinement
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
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
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Ring.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Order.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Data.Fintype.Shrink
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenBoundaryZero
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenPullbackGenerators
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# Proper direct image and open extension by zero

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-comp-composition,
proposition-composition-base-change-rf-shriek--1, clauses (1)--(3); Stacks Tag 09AH
(blueprint: proposition-composition-base-change-rf-shriek--1).

The auxiliary maps are constructed from the existing coefficient pullback comparisons and
derived adjunctions. The normalization equation uses the two open units, so it expresses
identity on restriction without choosing an unnormalized isomorphism.

## Main definitions

* `compositionInterchangePullback`: the canonical pullback comparison of the square.
* `compositionInterchangeRestriction`: its adjoint restriction comparison.
* `compositionInterchangeIsNormalized`: the identity-on-restriction condition.

## Main statement

* `properOpenInterchange`: the geometric equality, unique arrow, and localizing isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w v₁

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finiteCoefficientShrinkIso (ℓ : ℕ) (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (hn : ∃ n : ℕ, (ℓ ^ n : A) = 0) :
    ∃ (B : Type) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : DiscreteTopology B) (_ : IsTopologicalRing B),
      Finite B ∧ (∃ n : ℕ, ∀ a : B, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} B)) := by
  let B := Shrink.{0} A
  let : CommRing B := inferInstanceAs (CommRing (Shrink.{0} A))
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  let : IsTopologicalRing B := inferInstance
  let ei : A ≃+* B := (Shrink.ringEquiv.{0} A).symm
  have hc : Continuous ei := continuous_of_discreteTopology
  have hc' : Continuous ei.symm := continuous_of_discreteTopology
  let er : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hc).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop hc').comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply (f.down x)
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply (f.down x) }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨Mon.mkIso ea⟩⟩
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, fun a ↦ ?_⟩
  have hp : (ℓ ^ n : B) = 0 := by
    simpa only [map_pow, map_natCast, map_zero] using congrArg ei hn
  rw [nsmul_eq_mul, Nat.cast_pow, hp, zero_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem interchange_mate_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {U : B ⥤ A} {P : A ⥤ C} {R : C ⥤ A}
    {H : B ⥤ D} {S : D ⥤ B} {K : C ⥤ D} {V : D ⥤ C}
    (a : J ⊣ U) (b : P ⊣ R) (d : H ⊣ S) (e : K ⊣ V)
    (θ : U ⋙ P ≅ H ⋙ V) [IsIso a.unit]
    (hc : ∀ T, IsIso (e.counit.app (H.obj (J.obj T)))) :
    IsIso (Adjunction.exchangeRight d b θ) := by
  have hleft : IsIso (Adjunction.exchangeLeft a e θ) := by
    have hcomp (T) : IsIso ((Adjunction.exchangeLeft a e θ).app T) := by
      rw [Adjunction.exchangeLeft_app]
      have := hc T
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have heq : Adjunction.exchangeRight d b θ =
      conjugateEquiv (a.comp d) (b.comp e) (Adjunction.exchangeLeft a e θ) := by
    ext T
    have ht (N : B) :
        e.unit.app (P.obj (U.obj N)) ≫
          V.map ((Adjunction.exchangeLeft a e θ).app (U.obj N)) =
        P.map (a.unit.app (U.obj N)) ≫ θ.hom.app (J.obj (U.obj N)) := by
      have hh := (e.homEquiv _ _).apply_symm_apply
        (P.map (a.unit.app (U.obj N)) ≫ θ.hom.app (J.obj (U.obj N)))
      simpa only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit,
        Adjunction.exchangeLeft_app, Functor.map_comp, Category.assoc,
        Functor.id_obj, Functor.comp_obj] using hh
    have ht2 (N : B) :
        e.unit.app (P.obj (U.obj N)) ≫
          V.map ((Adjunction.exchangeLeft a e θ).app (U.obj N)) ≫
            V.map (H.map (a.counit.app N)) = θ.hom.app N := by
      have hn := θ.hom.naturality (a.counit.app N)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← Category.assoc, ht, Category.assoc, ← hn]
      simp only [← Category.assoc, ← P.map_comp, a.right_triangle_components]
      erw [P.map_id, Category.id_comp]
    simp only [Adjunction.exchangeRight_app, conjugateEquiv_apply_app,
      Adjunction.comp_unit_app, Adjunction.comp_counit_app,
      Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
    conv_rhs => rw [← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, ht2]
  rw [heq]
  infer_instance

private theorem interchange_unique_normalized
    {C D : Type*} [Category C] [Category D] {J : C ⥤ D} {U : D ⥤ C}
    (a : J ⊣ U) (K N : C) (M : D) (rho : U.obj M ⟶ N) [IsIso rho]
    (f : K ⟶ N) :
    ∃ m : J.obj K ⟶ M, a.homEquiv _ _ m ≫ rho = f ∧
      ∀ m', a.homEquiv _ _ m' ≫ rho = f → m' = m := by
  refine ⟨(a.homEquiv _ _).symm (f ≫ inv rho), ?_, ?_⟩
  · rw [Equiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · intro m hm
    apply (a.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply (cancel_mono rho).mp
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hm

private theorem interchange_restricted_iso
    {C D : Type*} [Category C] [Category D] {J : C ⥤ D} {U : D ⥤ C}
    (a : J ⊣ U) {K N : C} {M : D} (rho : U.obj M ⟶ N) [IsIso rho]
    (f : K ⟶ N) [IsIso f] [IsIso (a.unit.app K)] (m : J.obj K ⟶ M)
    (hm : a.homEquiv _ _ m ≫ rho = f) : IsIso (U.map m) := by
  have h : IsIso (a.homEquiv _ _ m ≫ rho) := by rw [hm]; infer_instance
  rw [Adjunction.homEquiv_unit, Category.assoc] at h
  have : IsIso (U.map m ≫ rho) := IsIso.of_isIso_comp_left (a.unit.app K) _
  exact IsIso.of_isIso_comp_right _ rho

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
  [IsOpenImmersion i] (c : Compactification.BoundaryCompactification (p ≫ i))

/-- The canonical pullback comparison of the compactification square, applied termwise.
Source: blueprint proposition-composition-base-change-rf-shriek--1, proof (2), square restriction
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
noncomputable def compositionInterchangePullback :
    (upperStar Λ i).mapDerivedCategory ⋙ (upperStar Λ p).mapDerivedCategory ≅
      (upperStar Λ c.obj.obj.g).mapDerivedCategory ⋙
        (upperStar Λ c.obj.obj.i).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ p) ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp Λ p i).symm ≪≫
        eqToIso (congrArg (upperStar Λ) c.obj.obj.comm) ≪≫
          upperStarComp Λ c.obj.obj.i c.obj.obj.g) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar Λ c.obj.obj.g) (upperStar Λ c.obj.obj.i)).symm

/-- The restriction comparison `i^* Rr_* B → Rp_* j'^* B`, the adjoint mate of the
canonical pullback square. This construction is defined before proving the square cartesian.
Source: blueprint proposition-composition-base-change-rf-shriek--1, proof (2), Hom calculation
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
noncomputable def compositionInterchangeRestriction
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology c.obj.obj.Z) Ab.{u + 1})
      (condensedRingObj Λ c.obj.obj.Z))) :
    (upperStar Λ i).mapDerivedCategory.obj ((lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj B) ⟶
      (lowerStar Λ p).rightDerivedFunctor.obj
        ((upperStar Λ c.obj.obj.i).mapDerivedCategory.obj B) :=
  ((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ p)).homEquiv _ _
      ((compositionInterchangePullback Λ p i c).hom.app
        ((lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj B) ≫
          (upperStar Λ c.obj.obj.i).mapDerivedCategory.map
            (((derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
              (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g)).counit.app B))

/-- An interchange arrow restricts to the identity precisely when its open adjoint,
followed by the canonical restriction comparison, is `Rp_*` of the source open unit.
Both units are the units of the existing exact open derived adjunctions.
Source: blueprint proposition-composition-base-change-rf-shriek--1, clause (2), proof (2)
(blueprint: proposition-composition-base-change-rf-shriek--1). -/
def compositionInterchangeIsNormalized
    (A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (m : (openImmersionLowerShriek Λ i).mapDerivedCategory.obj
        ((lowerStar Λ p).rightDerivedFunctor.obj A) ⟶
      (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A)) : Prop :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).homEquiv _ _ m ≫
    compositionInterchangeRestriction Λ p i c
      ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A) =
    (lowerStar Λ p).rightDerivedFunctor.map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit.app A)

private theorem interchange_geometry [IsProper p]
    [IsSchemeTheoreticallyDominant c.obj.obj.i] :
    IsPullback p c.obj.obj.i i c.obj.obj.g := by
  have : QuasiCompact c.obj.obj.i := c.obj.property
  exact c.obj.obj.isPullback_of_isProper_of_isSchemeTheoreticallyDominant

private theorem interchange_open_unit {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  have := openUnitIsIso Λ j
  exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit _

private theorem interchange_restriction_iso [IsProper p]
    [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (B : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology c.obj.obj.Z) Ab.{u + 1})
        (condensedRingObj Λ c.obj.obj.Z))) :
    IsIso (compositionInterchangeRestriction Λ p i c B) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
  let b := (derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ p)
  let d := (derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g)
  let e := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i
  have : IsIso a.unit := interchange_open_unit Λ i
  have hc (T) : IsIso (e.counit.app
      ((upperStar Λ c.obj.obj.g).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ i).mapDerivedCategory.obj T))) := by
    have h := cartesianDerivedCounit Λ (interchange_geometry p i c) T
    exact (NatTrans.isIso_app_iff_of_iso e.counit
      ((Functor.mapDerivedCategoryCompIso (openImmersionLowerShriek Λ i)
        (upperStar Λ c.obj.obj.g)).app T)).mpr h
  have := interchange_mate_iso a b d e (compositionInterchangePullback Λ p i c) hc
  have ht : IsIso ((Adjunction.exchangeRight d b
      (compositionInterchangePullback Λ p i c)).app B) := inferInstance
  simpa only [compositionInterchangeRestriction, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc, Adjunction.exchangeRight_app] using ht

private theorem properOpenInterchange_normalized [IsProper p]
    [IsSchemeTheoreticallyDominant c.obj.obj.i] :
    ∀ A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
        ∃ m : (openImmersionLowerShriek Λ i).mapDerivedCategory.obj
            ((lowerStar Λ p).rightDerivedFunctor.obj A) ⟶
          (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A),
          compositionInterchangeIsNormalized Λ p i c A m ∧
          (∀ m', compositionInterchangeIsNormalized Λ p i c A m' → m' = m) := by
  intro A
  let ai := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
  let rho := compositionInterchangeRestriction Λ p i c
    ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A)
  have : IsIso rho := interchange_restriction_iso Λ p i c _
  let f := (lowerStar Λ p).rightDerivedFunctor.map
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit.app A)
  exact interchange_unique_normalized ai _ _ _ rho f

/-- Zero objects are closed under isomorphisms; the instance making functor kernels
closed under isomorphisms is no longer in the imported library. -/
local instance isZero_isClosedUnderIsomorphisms_local {C : Type*} [Category C] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := C)) :=
  ⟨fun e h ↦ h.of_iso e.symm⟩

private theorem kernelTriangulated
    {C : Type v} {D : Type w} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] :
    F.kernel.IsTriangulated := by
  let hshift (n : ℤ) : F.kernel.IsStableUnderShiftBy n := ⟨fun M hM ↦
    (Functor.map_isZero (shiftFunctor D n) hM).of_iso ((F.commShiftIso n).app M)⟩
  let : F.kernel.IsStableUnderShift ℤ := ⟨hshift⟩
  let : F.kernel.ContainsZero := ⟨0, isZero_zero C,
    Functor.map_isZero F (isZero_zero C)⟩
  let : F.kernel.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦
    Pretriangulated.Triangle.isZero₂_of_isZero₁₃ _ (F.map_distinguished T hT) h₁ h₃)
  exact {}

private theorem extend_zero
    {C : Type v} {D : Type w} [Category.{v₁} C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (S : ObjectProperty C) (hloc : IsLocalizingSubcategory (localizingClosure S))
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hsums : ∀ (I : Type v₁) (J : Discrete I ⥤ C),
      (∀ i, localizingClosure S (J.obj (Discrete.mk i))) → PreservesColimit J F)
    (hS : ∀ K, S K → IsZero (F.obj K)) :
    ∀ K, localizingClosure S K → IsZero (F.obj K) := by
  let L := localizingClosure S
  let P : ObjectProperty C := L ⊓ F.kernel
  let : L.IsTriangulated := hloc.1
  let : L.IsClosedUnderIsomorphisms := hloc.2.1
  let := kernelTriangulated F
  have hP : IsLocalizingSubcategory P := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I J hJ hK
    let := hJ
    let := hsums I J (fun i ↦ (hK i).1)
    refine ⟨hloc.2.2 J hJ (fun i ↦ (hK i).1), ?_⟩
    have hF : IsZero (J ⋙ F) := (Functor.isZero_iff _).mpr (fun j ↦ (hK j.as).2)
    exact (isColimitOfPreserves F (colimit.isColimit J)).isZero_pt hF
  intro K hK
  exact (hK P hP (fun M hM ↦ ⟨fun Q hQ hSQ ↦ hSQ M hM, hS M hM⟩)).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem properOpenInterchange_localizing
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Ybar.Over (Spec (.of k))]
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Ybar ↘ Spec (.of k))] [QuasiCompact (Ybar ↘ Spec (.of k))]
    [IsSeparated (Ybar ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [QuasiCompact i] [IsProper p] [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
              (Profinite.padicSubfieldCondensedRing ℓ E.1)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    ∀ A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
      ∀ m : (openImmersionLowerShriek Λ i).mapDerivedCategory.obj
            ((lowerStar Λ p).rightDerivedFunctor.obj A) ⟶
          (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A),
      compositionInterchangeIsNormalized Λ p i c A m →
      localizingClosureProEtale Λ X A → IsIso m  := by
  have hcoeff : IsFiniteSubextensionLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with h | h | h | ⟨E, h | h⟩ | h
    · obtain ⟨R, hR, hfin, ht, hd, htop, hn, ⟨e⟩⟩ := h
      obtain ⟨B, hb, hbt, hbd, hbtop, hbfin, hbn, ⟨eb⟩⟩ :=
        finiteCoefficientShrinkIso ℓ R hn
      exact Or.inl ⟨B, hb, hbt, hbd, hbtop, hbfin, hbn, ⟨e ≪≫ eb⟩⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hcoeff with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have : QuasiCompact c.obj.obj.i := c.obj.property
  let z := i.closedComplement
  let J := (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory
  let R := (lowerStar Λ c.obj.obj.g).rightDerivedFunctor
  let V := (upperStar Λ z).mapDerivedCategory
  let F := J ⋙ R ⋙ V
  let S : ObjectProperty (DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    constantModelBoundedConstructible Λ X ⊓ fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K
  have hloc := (localizingClosure_exists Λ X S).2.2.2.1
  have : CompactSpace Ybar :=
    QuasiCompact.compactSpace_of_compactSpace (Ybar ↘ Spec (.of k))
  have : QuasiSeparatedSpace Ybar :=
    quasiSeparatedSpace_of_quasiSeparated (Ybar ↘ Spec (.of k))
  have hsums := (compactification_localizing Λ ℓ k (p ≫ i) c hadm).2.2.1
  let adj := (upperStarLowerStarAdjunction Λ z).mapDerivedCategoryRightDerivedAdjunction
  let : V.IsLeftAdjoint := adj.isLeftAdjoint
  have hgen (A) (hA : S A) : IsZero (F.obj A) := by
    let q := pullback.fst c.obj.obj.g i
    let ep := (interchange_geometry p i c).flip.isoPullback
    have hsq : IsPullback ep.inv q c.obj.obj.i (𝟙 c.obj.obj.Z) :=
      IsPullback.of_horiz_isIso ⟨by
        dsimp only [q, ep]
        rw [IsPullback.isoPullback_inv_fst, Category.comp_id]⟩
    let aj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ q
    have hε := cartesianDerivedCounit Λ hsq A
    let eF := Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft (openImmersionLowerShriek Λ c.obj.obj.i)
        (upperStarId Λ c.obj.obj.Z) ≪≫
          (openImmersionLowerShriek Λ c.obj.obj.i).rightUnitor)
    have : IsIso (aj.counit.app (J.obj A)) :=
      (NatTrans.isIso_app_iff_of_iso aj.counit (eF.app A)).mp hε
    have hjA := (openImmersionLowerShriek_localizing ℓ k (ringChar k)
      (Nat.Prime.pos Fact.out) (Fact.out : ringChar k ≠ ℓ) Λ hadm c.obj.obj.i).1 ⟨A, hA⟩
    have hqA := openPullback_generators Λ ℓ k (ringChar k)
      (Nat.Prime.pos Fact.out) (Fact.out : ringChar k ≠ ℓ) hadm q ⟨J.obj A, hjA⟩
    let W : Over (Spec (.of k)) := Over.mk (c.obj.obj.Z ↘ Spec (.of k))
    let B : Over (Spec (.of k)) := Over.mk (Ybar ↘ Spec (.of k))
    let U : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
    let Z : Over (Spec (.of k)) := Over.mk (z ≫ (Ybar ↘ Spec (.of k)))
    let rr : W ⟶ B := Over.homMk c.obj.obj.g (comp_over _ _)
    let ii : U ⟶ B := Over.homMk i (comp_over _ _)
    let zz : Z ⟶ B := Over.homMk z rfl
    have : LocallyOfFiniteType W.hom := by
      change LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))
      infer_instance
    have : QuasiCompact W.hom := by
      change QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))
      infer_instance
    have : IsSeparated W.hom := by
      change IsSeparated (c.obj.obj.Z ↘ Spec (.of k))
      infer_instance
    have : LocallyOfFiniteType B.hom := by
      change LocallyOfFiniteType (Ybar ↘ Spec (.of k))
      infer_instance
    have : QuasiCompact B.hom := by
      change QuasiCompact (Ybar ↘ Spec (.of k))
      infer_instance
    have : IsSeparated B.hom := by
      change IsSeparated (Ybar ↘ Spec (.of k))
      infer_instance
    have : LocallyOfFiniteType U.hom := by
      change LocallyOfFiniteType (Y ↘ Spec (.of k))
      infer_instance
    have : QuasiCompact U.hom := by
      change QuasiCompact (Y ↘ Spec (.of k))
      infer_instance
    have : IsSeparated U.hom := by
      change IsSeparated (Y ↘ Spec (.of k))
      infer_instance
    have : LocallyOfFiniteType Z.hom := by
      change LocallyOfFiniteType (z ≫ (Ybar ↘ Spec (.of k)))
      infer_instance
    have : QuasiCompact Z.hom := by
      change QuasiCompact (z ≫ (Ybar ↘ Spec (.of k)))
      infer_instance
    have : IsSeparated Z.hom := by
      change IsSeparated (z ≫ (Ybar ↘ Spec (.of k)))
      infer_instance
    have : IsProper rr.left := by
      change IsProper c.obj.obj.g
      infer_instance
    have : IsOpenImmersion ii.left := by
      change IsOpenImmersion i
      infer_instance
    have : QuasiCompact ii.left := by
      change QuasiCompact i
      infer_instance
    have : IsClosedImmersion zz.left := by
      change IsClosedImmersion z
      infer_instance
    have : IsReduced Z.left := by
      dsimp only [Z, Over.mk_left, z]
      infer_instance
    have hz := proper_open_boundary_zero ℓ Λ hcoeff k W B U Z rr ii zz
      (Scheme.Hom.range_closedComplement i) ⟨_, hqA⟩
    have hz' := hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ z).symm.app _)
    exact hz'.of_iso (((R ⋙ V).mapIso (asIso (aj.counit.app (J.obj A)))).symm)
  intro A m hm hA
  have hz : IsZero (F.obj A) := by
    apply extend_zero S hloc F _ hgen A hA
    intro I K hK
    -- the sum is indexed by the morphism universe: lift its index to the universe of `hsums`
    have : PreservesColimit K (J ⋙ R) := by
      let e := Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)
      have h' : PreservesColimit (e.functor ⋙ K) (J ⋙ R) :=
        hsums (ULift.{u + 2} I) (e.functor ⋙ K) (fun i ↦ hK (Equiv.ulift i))
      exact Functor.Final.preservesColimit_of_comp (F := e.functor)
    change PreservesColimit K ((J ⋙ R) ⋙ V)
    have : PreservesColimit (K ⋙ J ⋙ R) V :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
    exact comp_preservesColimit (J ⋙ R) V
  have hij : IsCompl (Set.range z.base) (Set.range i.base) := by
    dsimp only [z]
    rw [Scheme.Hom.range_closedComplement]
    exact isCompl_compl.symm
  have hdetect := jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ z i hij
  apply hdetect.isIso_of_pairFunctor m
  · apply (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory Λ i) m).2
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i
    let rho := compositionInterchangeRestriction Λ p i c (J.obj A)
    have : IsIso rho := interchange_restriction_iso Λ p i c _
    have : IsIso a.unit := interchange_open_unit Λ i
    have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit :=
      interchange_open_unit Λ c.obj.obj.i
    exact interchange_restricted_iso a rho
      ((lowerStar Λ p).rightDerivedFunctor.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit.app A)) m hm
  · have hzsrc := isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ i z hij.symm.disjoint ((lowerStar Λ p).rightDerivedFunctor.obj A)
    have hztgt := hz.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ z).app _)
    exact hzsrc.isIso hztgt _

/-- Proper/open interchange in the standing scheme setting, for all admissible coefficients.
The coefficient disjunction lists the finite discrete rings killed by an ell power, Z_ell,
Q_ell, integers and fields of finite subextensions, and the finite-subextension condensed Qbar.
Source: blueprint main-20261015, proposition-composition-base-change-rf-shriek--1, clauses (1)--(3)
(blueprint: proposition-composition-base-change-rf-shriek--1).

Proof plan:
1. In V = r^{-1}(Y), X is open and dense. Its map to V is proper, since X is proper
   over Y and V is separated over Y (proper base change and proper-to-separated).
   Its image is closed, hence all of V. The surjective open immersion identifies the
   open subschemes and the commuting compactification triangle identifies r with p.
2. Cartesian coefficients make pullback exact. Apply the open base-change isomorphism
   of proposition-extension-zero-restriction-closed-subscheme termwise and use
   exact-functor-derived- factorization. Termwise-adjunction-homotopy and adjunction-localization
   descend the open adjunctions, with invertible open units. Combine these with module-derived-
   pushpull. The natural Hom calculation identifies i^* Rr_* B with Rp_* j'^* B.
   For B = j'_! A, both open units are invertible, so the identity under this
   identification determines exactly one arrow. This is the displayed normalization.
   Uniqueness also gives naturality and compatibility with shifts.
3. For A in Dctf, proper-image-localizing-open puts j'_! A in Dctf. Proper base change
   (finite, integral or rational as appropriate) identifies restriction to the closed
   complement with pushforward from an empty support, hence zero. Open-closed-detection
   makes the cone zero. The finite-subextension Qbar convention is essential here.
   Compactification-coherence-single gives exactness and coproduct preservation of the
   two functors; determination-localizing propagates invertibility from Dctf to Loc(Dctf).
-/
theorem properOpenInterchange
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Ybar.Over (Spec (.of k))]
    [c.obj.obj.Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Ybar ↘ Spec (.of k))] [QuasiCompact (Ybar ↘ Spec (.of k))]
    [IsSeparated (Ybar ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of k))]
    [QuasiCompact (c.obj.obj.Z ↘ Spec (.of k))]
    [IsSeparated (c.obj.obj.Z ↘ Spec (.of k))]
    [p.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [c.obj.obj.i.IsOver (Spec (.of k))] [c.obj.obj.g.IsOver (Spec (.of k))]
    [QuasiCompact i] [IsProper p] [IsSchemeTheoreticallyDominant c.obj.obj.i]
    (_hΛ :
      (∃ (A : Type u) (_ : CommRing A) (_ : Finite A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        (∃ n : ℕ, (ℓ ^ n : A) = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
              (Profinite.padicSubfieldCondensedRing ℓ E.1)))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    c.obj.obj.g ⁻¹ᵁ i.opensRange = c.obj.obj.i.opensRange ∧
      ∀ A : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)),
        ∃ m : (openImmersionLowerShriek Λ i).mapDerivedCategory.obj
            ((lowerStar Λ p).rightDerivedFunctor.obj A) ⟶
          (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.obj
            ((openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory.obj A),
          compositionInterchangeIsNormalized Λ p i c A m ∧
          (∀ m', compositionInterchangeIsNormalized Λ p i c A m' → m' = m) ∧
          (localizingClosureProEtale Λ X A → IsIso m) := by
  have sq := interchange_geometry p i c
  have hgeom : c.obj.obj.g ⁻¹ᵁ i.opensRange = c.obj.obj.i.opensRange :=
    sq.flip.opensRange_fst.symm
  have hh := properOpenInterchange_normalized Λ p i c
  refine ⟨hgeom, fun A ↦ ?_⟩
  obtain ⟨m, hm, hu⟩ := hh A
  refine ⟨m, hm, hu, ?_⟩
  exact properOpenInterchange_localizing Λ p i c ℓ k _hΛ A m hm

end AlgebraicGeometry.ProEtale.CondensedRing
