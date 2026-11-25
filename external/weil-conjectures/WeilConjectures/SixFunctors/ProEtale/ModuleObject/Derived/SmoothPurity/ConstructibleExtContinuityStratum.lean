/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ClosedSupportStratumHom
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic

import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
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
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import all WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Continuity of derived Hom out of a stratum extension

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-constructible-ext-continuity-stratum.md and its proof
(blueprint: lemma-continuity-ext-out-constructible-complex--1).

The colimit is taken in complexes of coefficient modules, hence degreewise. Derived Hom
is taken in the ordinary unbounded derived category, using the same extension i_* u_! L
as the recorded stratum Hom lemma. The comparison is induced by the colimit cocone.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

noncomputable local instance constructibleExtContinuityStratumHasZeroMorphisms
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

private theorem moduleColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (I : Type (u + 1)) [SmallCategory I] :
    HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  infer_instance

attribute [local instance 2000] moduleColimits

private theorem complexColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (I : Type (u + 1)) [SmallCategory I] :
    HasColimitsOfShape I (CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) := by
  infer_instance

attribute [local instance 2000] complexColimits

-- Keep the categorical comparison independent of the concrete module instances.
private theorem qcqsCostalkContinuityOfRecollement
    {A B C : Type*} [Category.{u + 1} A] [Category.{u + 1} B] [Category.{u + 1} C]
    [Abelian A] [Abelian B] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} A] [IsGrothendieckAbelian.{u + 1} B]
    [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
    [HasDerivedCategory.{u + 1} C]
    (ipush : B ⥤ A) [ipush.Additive] [PreservesFiniteLimits ipush]
    [PreservesFiniteColimits ipush] [ipush.Full] [ipush.Faithful]
    (kstar : A ⥤ C) [kstar.Additive] [PreservesFiniteLimits kstar]
    [PreservesFiniteColimits kstar]
    (kpush : C ⥤ A) [kpush.Additive]
    (H₀ H : A ⥤ B) [H₀.Additive] [H.Additive]
    (ash : ipush ⊣ H₀) (adj : ipush ⊣ H)
    (bi : ipush.mapDerivedCategoryPlus ⊣ H₀.rightDerivedFunctorPlus)
    (bj : kstar.mapDerivedCategoryPlus ⊣ kpush.rightDerivedFunctorPlus)
    (ε : kstar.mapDerivedCategoryPlus ⋙ kpush.rightDerivedFunctorPlus ⟶
      H₀.rightDerivedFunctorPlus ⋙ ipush.mapDerivedCategoryPlus ⋙ shiftFunctor _ (1 : ℤ))
    (hClosed : ∀ K, Triangle.mk (bi.counit.app K) (bj.unit.app K) (ε.app K) ∈
      distTriang (DerivedCategory.Plus A))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    [PreservesColimitsOfShape I kstar]
    (hcont : ∀ (R : I ⥤ CochainComplex C ℤ) (a : ℤ),
      (∀ s, (R.obj s).IsStrictlyGE a) → ∀ r : ℤ,
      IsIso (condensedContinuityComparison R a
        (DerivedCategory.Q ⋙ kpush.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor A r)))
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (hD : ∀ s, (D.obj s).IsStrictlyGE a) (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q)) := by
  classical
  let rawi := H₀.rightDerivedFunctorPlus ⋙ ipush.mapDerivedCategoryPlus
  let rawk := kstar.mapDerivedCategoryPlus ⋙ kpush.rightDerivedFunctorPlus
  let loc := localizationTriangleFunctor rawi rawk bi.counit bj.unit ε
  let loc' := loc ⋙ (DerivedCategory.Plus.ι (C := A)).mapTriangle
  let d := condensedContinuityCocone D a
  have hd : IsColimit d := canonicalContinuityIsColimit D a hD
  have hda : d.pt.IsStrictlyGE a :=
    colimit_isStrictlyGE (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) a
      (fun s ↦ inferInstanceAs (CochainComplex.IsStrictlyGE ((D.obj s).truncGE a) a))
  let Dp : I ⥤ CochainComplex.Plus A :=
    (CochainComplex.plus A).lift D (fun s ↦ ⟨a, hD s⟩)
  let dp : Cocone Dp :=
    { pt := ⟨d.pt, ⟨a, hda⟩⟩
      ι :=
        { app s := ⟨d.ι.app s⟩
          naturality _ _ f := by
            apply ObjectProperty.hom_ext
            exact (d.w f).trans (Category.comp_id _).symm } }
  let TT := Dp ⋙ DerivedCategory.Plus.Q ⋙ loc'
  let tc : Cocone TT := loc'.mapCocone (DerivedCategory.Plus.Q.mapCocone dp)
  have hTT (s : I) : TT.obj s ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.Plus.ι (C := A)).map_distinguished _ (hClosed _)
  have htc : tc.pt ∈ distTriang (DerivedCategory A) :=
    (DerivedCategory.Plus.ι (C := A)).map_distinguished _ (hClosed _)
  let F := DerivedCategory.homologyFunctor A 0
  let eQ : CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ≅
      DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι :=
    (DerivedCategory.Plus.QCompιIso A).symm
  have hid (r : ℤ) : IsIso (triangleComparison TT tc F r Triangle.π₂) := by
    let C := HomologicalComplex.homologyFunctor A (.up ℤ) r
    have hb : IsIso (colimit.desc (D ⋙ C) (C.mapCocone d)) := by
      change IsIso ((IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitOfPreserves C hd)).hom)
      infer_instance
    let e : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ⋙
        DerivedCategory.homologyFunctor A r ≅ CochainComplex.Plus.ι A ⋙ C :=
      Functor.isoWhiskerRight eQ.symm (DerivedCategory.homologyFunctor A r) ≪≫
        Functor.isoWhiskerLeft (CochainComplex.Plus.ι A)
          (DerivedCategory.homologyFunctorFactors A r)
    have hb' : IsIso (colimit.desc (Dp ⋙ CochainComplex.Plus.ι A ⋙ C)
        ((CochainComplex.Plus.ι A ⋙ C).mapCocone dp)) := hb
    exact comparison_ofNatIso Dp dp e.symm
  have hkComp (r : ℤ) : IsIso (triangleComparison TT tc F r Triangle.π₃) := by
    let K : CochainComplex A ℤ ⥤ CochainComplex C ℤ :=
      kstar.mapHomologicalComplex (.up ℤ)
    let R : I ⥤ CochainComplex C ℤ := D ⋙ K
    let cd := K.mapCocone d
    have hR (s : I) : (R.obj s).IsStrictlyGE a := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro t ht
      exact kstar.map_isZero ((D.obj s).isZero_of_isStrictlyGE a t ht)
    have hcd : IsColimit cd := isColimitOfPreserves K hd
    let V := DerivedCategory.Q ⋙ kpush.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor A r
    have hb : IsIso (colimit.desc (R ⋙ V)
        (V.mapCocone (condensedContinuityCocone R a))) :=
      hcont R a hR r
    have hbc : IsIso (colimit.desc (R ⋙ V) (V.mapCocone cd)) :=
      comparison_of_colimitCocone R (condensedContinuityCocone R a) cd
        (canonicalContinuityIsColimit R a hR) hcd V
    let e : DerivedCategory.Plus.Q ⋙ rawk ⋙ DerivedCategory.Plus.ι ⋙
        DerivedCategory.homologyFunctor A r ≅ CochainComplex.Plus.ι A ⋙ K ⋙ V :=
      Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙ kstar.mapDerivedCategoryPlus)
          (Functor.isoWhiskerRight kpush.rightDerivedFunctorPlusCompatibility
            (DerivedCategory.homologyFunctor A r)) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft DerivedCategory.Plus.Q
            kstar.mapDerivedCategoryPlusCompatibility)
          (kpush.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor A r) ≪≫
        Functor.isoWhiskerRight eQ.symm
          (kstar.mapDerivedCategory ⋙ kpush.rightDerivedFunctor ⋙
            DerivedCategory.homologyFunctor A r) ≪≫
        Functor.isoWhiskerLeft (CochainComplex.Plus.ι A)
          (Functor.isoWhiskerRight kstar.mapDerivedCategoryFactors
            (kpush.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor A r))
    have hbc' : IsIso (colimit.desc (Dp ⋙ CochainComplex.Plus.ι A ⋙ K ⋙ V)
        ((CochainComplex.Plus.ι A ⋙ K ⋙ V).mapCocone dp)) := hbc
    exact comparison_ofNatIso Dp dp e.symm
  have hiComp : IsIso (triangleComparison TT tc F q Triangle.π₁) :=
    triangleComparison_isIso TT tc hTT htc F (q - 1) q (by omega)
  let e : DerivedCategory.Plus.Q ⋙ rawi ⋙ DerivedCategory.Plus.ι ⋙
      DerivedCategory.homologyFunctor A q ≅ CochainComplex.Plus.ι A ⋙
        DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor B q ⋙ ipush :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙ H₀.rightDerivedFunctorPlus)
        (ipush.mapDerivedCategoryPlusHomologyFunctorIso q).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft DerivedCategory.Plus.Q H₀.rightDerivedFunctorPlusCompatibility)
        (DerivedCategory.homologyFunctor B q ⋙ ipush) ≪≫
      Functor.isoWhiskerRight eQ.symm
        (H₀.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙ ipush) ≪≫
      Functor.isoWhiskerLeft (CochainComplex.Plus.ι A ⋙ DerivedCategory.Q)
        (Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso (ash.rightAdjointUniq adj))
          (DerivedCategory.homologyFunctor B q ⋙ ipush))
  have hraw : IsIso (colimit.desc (Dp ⋙ DerivedCategory.Plus.Q ⋙ rawi ⋙
      DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor A q)
    ((DerivedCategory.Plus.Q ⋙ rawi ⋙ DerivedCategory.Plus.ι ⋙
      DerivedCategory.homologyFunctor A q).mapCocone dp)) := hiComp
  have hpush : IsIso (colimit.desc (D ⋙ DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor B q ⋙ ipush)
    ((DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q ⋙
      ipush).mapCocone d)) := comparison_ofNatIso Dp dp e
  let V := DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q
  have : PreservesColimitsOfShape I ipush :=
    ash.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hh : IsIso (ipush.map (colimit.desc (D ⋙ V) (V.mapCocone d))) := by
    have hh' : IsIso (colimit.post (D ⋙ V) ipush ≫
        ipush.map (colimit.desc (D ⋙ V) (V.mapCocone d))) := by
      rw [colimit.post_desc]
      exact hpush
    exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ V) ipush) _
  change IsIso (colimit.desc (D ⋙ V) (V.mapCocone d))
  exact isIso_of_reflects_iso _ ipush

set_option synthInstance.maxSize 4096 in
private theorem qcqsCostalkContinuity
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z V : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (k : V ⟶ T) [IsOpenImmersion k] [QuasiCompact k]
    (hik : Set.range k = (Set.range i)ᶜ)
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    [H.Additive] (adj : CondensedRing.lowerStar Λ i ⊣ H)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (a : ℤ) (hD : ∀ s, (D.obj s).IsStrictlyGE a) (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q)) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let B := Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)
  have : HasColimitsOfShape I A := inferInstance
  have : HasExactColimitsOfShape I A := inferInstance
  have : HasColimitsOfShape I B := inferInstance
  have : HasExactColimitsOfShape I B := inferInstance
  have : HasColimitsOfShape I (CochainComplex A ℤ) := inferInstance
  have : HasColimitsOfShape I (CochainComplex B ℤ) := inferInstance
  obtain ⟨hclosed, hr⟩ := CondensedRing.condensed_open_closed_recollement Λ i k hik
  let _ := hclosed
  have hFull := hr.2.2.2.2.2.2.2.2.2.1
  have hFaith := hr.2.2.2.2.2.2.2.2.2.2.1
  rcases hr.2.2.2.2.2.2.2.2.2.2.2.2 with ⟨H₀, hAdd, hLim, ash, aj, bj, ai, bi, hjs, his, hdata⟩
  let _ := hAdd
  let _ := hLim
  let _ := hjs
  let _ := his
  let _ := hFull
  let _ := hFaith
  have htri := hdata.2.2.2.2.2.2.2.2.2.2.2.2
  let ε := htri.choose_spec.choose
  have hClosed := htri.choose_spec.choose_spec.2.2.2.1
  let C := Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)
  have : HasColimitsOfShape I C := inferInstance
  have : HasColimitsOfShape I (CochainComplex C ℤ) := inferInstance
  let kstar : A ⥤ C := CondensedRing.upperStar Λ k
  let kpush : C ⥤ A := CondensedRing.lowerStar Λ k
  let ipush : B ⥤ A := CondensedRing.lowerStar Λ i
  have : PreservesColimitsOfShape I kstar :=
    (CondensedRing.upperStarLowerStarAdjunction Λ k).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  exact qcqsCostalkContinuityOfRecollement ipush kstar kpush H₀ H ash adj bi bj ε hClosed
    (fun R a hR r ↦ condensed_qcqs_pushforward_continuity Λ k R a
      (fun s t ht ↦ by have := hR s; exact (R.obj s).isZero_of_isGE a t ht) r)
    D a hD q

set_option synthInstance.maxSize 4096 in
private theorem qcqsInjectiveCostalkContinuity
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z V : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (k : V ⟶ T) [IsOpenImmersion k] [QuasiCompact k]
    (hik : Set.range k = (Set.range i)ᶜ)
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    [H.Additive] (adj : CondensedRing.lowerStar Λ i ⊣ H)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (J : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (c : Cocone J) (a : ℤ)
    (hJ : ∀ s, (J.obj s).IsStrictlyGE a)
    (hJi : ∀ s r, Injective ((J.obj s).X r))
    (hc : c.pt.IsStrictlyGE a) (hci : ∀ r, Injective (c.pt.X r))
    (hq : QuasiIso (colimit.desc J c)) :
    QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)) := by
  exact injectiveContinuity_of_derived H J c a hJ hJi hc hci hq
    (fun q ↦ qcqsCostalkContinuity T Λ i k hik H adj J a hJ q)

set_option synthInstance.maxSize 4096 in
private theorem qcqsCostalkModel
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {Z U V : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (k : V ⟶ T) [IsOpenImmersion k] [QuasiCompact k]
    (hik : Set.range k = (Set.range i)ᶜ)
    (j : U ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ℤ)
    (hN : ∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((N.obj s).X r))
    (n : ℤ) :
    let F := shiftFunctor
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) n ⋙ preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj P))))
    let G := condensedShiftedHom Λ U ((DerivedCategory.singleFunctor _ 0).obj P) n
    ∃ L : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) ℤ,
      (∃ a : ℤ, ∀ (s : I) (r : ℤ), r < a → IsZero ((L.obj s).X r)) ∧
      ∃ (e : (N ⋙ DerivedCategory.Q) ⋙ F ≅ L ⋙ G)
        (v : F.obj (DerivedCategory.Q.mapCocone (colimit.cocone N)).pt ≅
          G.obj (colimit.cocone L).pt),
        ∀ s : I, F.map ((DerivedCategory.Q.mapCocone (colimit.cocone N)).ι.app s) ≫ v.hom =
          e.hom.app s ≫ G.map ((colimit.cocone L).ι.app s) := by
  /- Proof: choose the exceptional right adjoint H₀ of exact closed pushforward and
  compose it with exact open restriction j*. Its exact left adjoint is i_*j_!.
  Their ordinary derived adjunction identifies the two shifted Hom functors.
  Construct functorial injective embeddings using the Grothendieck K-injective
  resolution functor. Resolve the whole diagram and its colimit cocone with one
  functorial bounded injective resolution preserving every strict lower bound.
  Let L be the result of applying j*H₀ degree by degree. Additive functors preserve
  the zero terms below the common bound. Exact filtered colimits make the
  resolution cocone a quasi-colimit. Closed-costalk injective continuity, followed
  by exact colimit-preserving j*, makes the corresponding L cocone a quasi-colimit.
  The natural right-derived-unit isomorphisms on K-injectives, together with the
  derived adjunction, give the diagram isomorphism. The same comparisons at the
  resolved colimit, followed by the inverse quasi-colimit comparison, give the
  vertex isomorphism. Naturality and the universal colimit-leg equation give the
  required identity on every original leg. This applies also to zero P and empty
  U or Z. -/
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)
  let B := Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)
  have : HasColimitsOfShape I A := moduleColimits Λ T I
  have : HasExactColimitsOfShape I A := inferInstance
  have : HasColimitsOfShape I B := moduleColimits Λ U I
  have : HasColimitsOfShape I (CochainComplex A ℤ) := complexColimits Λ T I
  have : HasColimitsOfShape I (CochainComplex B ℤ) := complexColimits Λ U I
  let H₀ := CondensedRing.closedSupport Λ i k
  have hik' : Set.range i.base = (Set.range k.base)ᶜ := by
    rw [hik, compl_compl]
  let := CondensedRing.closedSupport_lowerStarExact Λ i k hik'
  let ash := CondensedRing.closedSupportAdjunction Λ i k hik'
  have := CondensedRing.closedSupport_leftExact Λ i k hik'
  have := ash.right_adjoint_additive
  let E := CondensedRing.openImmersionLowerShriek Λ j ⋙ CondensedRing.lowerStar Λ i
  let H := H₀ ⋙ CondensedRing.upperStar Λ j
  let adj : E ⊣ H := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).comp ash
  obtain ⟨a, ha⟩ := hN
  have hNa (s : I) : (N.obj s).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ _).2 (ha s)
  have : IsGrothendieckAbelian.{u + 1} A := Mod.isGrothendieckAbelian _
  obtain ⟨J, c, β, βv, hβ, hβq, hβvq, hJa, hca, hJi, hci, hq⟩ :=
    localPieceBoundedInjectiveCocone N a hNa
  have hH₀ := qcqsInjectiveCostalkContinuity T Λ i k hik H₀ ash J c a
    hJa hJi hca hci hq
  have : PreservesColimitsOfShape I (CondensedRing.upperStar Λ j) :=
    (CondensedRing.upperStarLowerStarAdjunction Λ j).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : HasColimit (J ⋙ H.mapHomologicalComplex (.up ℤ)) :=
    HasColimitsOfShape.has_colimit _
  have hH : QuasiIso (colimit.desc (J ⋙ H.mapHomologicalComplex (.up ℤ))
      ((H.mapHomologicalComplex (.up ℤ)).mapCocone c)) := by
    exact quasiIso_desc_mapCocone (CondensedRing.upperStar Λ j)
      (J ⋙ H₀.mapHomologicalComplex (.up ℤ))
      ((H₀.mapHomologicalComplex (.up ℤ)).mapCocone c)
  have hJk (s : I) : (J.obj s).IsKInjective := by
    have := hJa s
    exact CochainComplex.isKInjective_of_injective (J.obj s) a
  have hck : c.pt.IsKInjective := by
    have := hca
    exact CochainComplex.isKInjective_of_injective c.pt a
  let L := J ⋙ H.mapHomologicalComplex (.up ℤ)
  refine ⟨L, ⟨a, ?_⟩, ?_⟩
  · intro s r hr
    exact H.map_isZero ((J.obj s).isZero_of_isStrictlyGE a r hr)
  · exact homCoconeOfInjectiveCocone E H adj P n N J c β βv hβ

set_option synthInstance.maxSize 4096 in
private theorem qcqsFiniteFreeHomEvaluation
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)).obj P))
    (n : ℤ) : Nonempty
      (DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj P)) ≅
        (Mod.ihom P).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
          (condensedModuleSections Λ X).rightDerivedFunctor ⋙
            DerivedCategory.homologyFunctor _ n) := by
  -- Use ordinary internal-module evaluation directly; no ringed-site transport is needed.
  let R := condensedRingObj Λ X
  let F := Mod.ihom P
  let Γ := condensedModuleSections Λ X
  have : PreservesFiniteLimits (Mod.tensorLeft P) :=
    condensed_locally_free_tensor_preservesFiniteLimits R P hP
  have : (Mod.tensorLeft P).Additive := (Mod.ihomAdjunction P).left_adjoint_additive
  have : PreservesLimitsOfSize.{u + 1, u + 1} F :=
    (Mod.ihomAdjunction P).rightAdjoint_preservesLimits
  have : F.PreservesKInjectiveComplexes :=
    (Mod.ihomAdjunction P).preservesKInjectiveComplexes
  have : PreservesColimitsOfSize.{u + 1, u + 1} F :=
    condensed_locally_free_ihom_preservesColimits R P hP
  obtain ⟨e⟩ := condensed_internal_hom_sections X Λ P
  obtain ⟨d⟩ := CategoryTheory.derived_coyoneda_evaluation P n
  let c : (preadditiveCoyoneda.obj (op P)).rightDerivedFunctor ≅
      F.mapDerivedCategory ⋙ Γ.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompIso' F Γ e).symm ≪≫
      Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory _
  exact ⟨Functor.isoWhiskerLeft DerivedCategory.Q d ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.isoWhiskerRight c (DerivedCategory.homologyFunctor _ n)) ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors
      (Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ n)⟩

set_option synthInstance.maxSize 4096 in
private theorem qcqsFiniteFreeHomContinuity
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)).obj P))
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((condensedShiftedHom Λ X
        ((DerivedCategory.singleFunctor _ 0).obj P) n).mapCocone (colimit.cocone N))) := by
  have : HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    moduleColimits Λ X I
  have : HasColimitsOfShape I (CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) :=
    complexColimits Λ X I
  let H := Mod.ihom P
  have : PreservesColimitsOfSize.{u + 1, u + 1} H :=
    condensed_locally_free_ihom_preservesColimits (condensedRingObj Λ X) P hP
  have : PreservesLimitsOfSize.{u + 1, u + 1} H :=
    (Mod.ihomAdjunction P).rightAdjoint_preservesLimits
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let T := DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ n
  let M := N ⋙ Hc
  obtain ⟨a, ha⟩ := hN
  have hb (i : I) : CochainComplex.IsStrictlyGE (M.obj i) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro r hr
    exact H.map_isZero (ha i r hr)
  have : HasColimit (M ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    HasColimitsOfShape.has_colimit _
  have hT : IsIso (condensedContinuityComparison M a T) :=
    condensed_qcqs_globalSections_continuity Λ X M a (fun i r hr ↦ by
      let : CochainComplex.IsStrictlyGE (M.obj i) a := hb i
      exact CochainComplex.isZero_of_isGE _ a r hr) n
  change IsIso (colimit.desc (M ⋙ T) (T.mapCocone (condensedContinuityCocone M a))) at hT
  have hdesc : IsIso (colimit.desc (M ⋙ T) (T.mapCocone (colimit.cocone M))) :=
    comparison_of_colimitCocone M (condensedContinuityCocone M a) (colimit.cocone M)
      (canonicalContinuityIsColimit M a hb) (colimit.isColimit M) T
  obtain ⟨hc⟩ := (colimit.isColimit (M ⋙ T)).nonempty_isColimit_iff_isIso_desc.2 hdesc
  let : PreservesColimit M T :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit M) hc
  have hcomp : IsColimit ((Hc ⋙ T).mapCocone (colimit.cocone N)) :=
    (isColimitOfPreserves T (isColimitOfPreserves Hc (colimit.isColimit N))).ofIsoColimit
      (Functor.mapCoconeMapCocone (colimit.cocone N))
  obtain ⟨e⟩ := qcqsFiniteFreeHomEvaluation X Λ P hP n
  apply (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1
  exact ⟨IsColimit.mapCoconeEquiv e.symm hcomp⟩

set_option synthInstance.maxSize 4096 in
private theorem freeComap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫
    (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫
      biproduct.mapIso (fun _ ↦ ?_)⟩⟩
  simpa using Mod.regularIsoOfIsIso (inv φ)

set_option synthInstance.maxSize 4096 in
private theorem lisseRawCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (P : CondensedRing.supportModules Λ X) (hP : IsLisseCoefficientModule Λ P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  let α := condensedPullbackHom Λ (C.f s)
  let F := (upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)
  let e := (Mod.extendScalarsIsoComapInv α).app (F.obj P)
  obtain ⟨n, ⟨b⟩⟩ := hC s
  have h' : Mod.IsFree _ ((Mod.comap (inv α)).obj (F.obj P)) :=
    ⟨n, ⟨e.symm ≪≫ b⟩⟩
  obtain ⟨m, ⟨c⟩⟩ := freeComap α h'
  let d := (Mod.comapComp α (inv α)).symm ≪≫
    Mod.comapCongr (show α ≫ inv α = 𝟙 _ by simp) ≪≫ Mod.comapId _
  exact ⟨m, ⟨(d.app _).symm ≪≫ c⟩⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] constructibleExtContinuityStratumHasZeroMorphisms
attribute [local instance 2000] moduleColimits complexColimits

set_option linter.unusedVariables false in
-- The preserved statement includes admissibility; the proof works for every coefficient ring.
/-- The canonical map from the filtered colimit of Hom(a!L,K_t[q]) to Hom(a!L,K[q])
is invertible, equivalently bijective, for every integer q and every diagram with one
common strict lower bound. Here a!L is i_*u_!L placed in degree zero.

Source: blueprint stratum continuity lemma and its proof
(blueprint: lemma-continuity-ext-out-constructible-complex--1).
Proof for stage 3, following the updated node:
1. Closed i and the quasi-compact open uS make Z and S qcqs. The complementary
   open j is already quasi-compact by hypothesis.
2. Apply the natural recollement triangle to the uniformly bounded diagram and
   its colimit. Homology and qcqs open pushforward commute with this colimit.
   Exact filtered colimits and the five lemma give closed-costalk continuity;
   exact fully faithful closed pushforward reflects the resulting isomorphism.
3. On bounded-below injective complexes the natural right-derived comparison
   identifies derived costalk with termwise costalk. The representative criterion
   therefore makes the costalk of an injective quasi-colimit a quasi-colimit.
4. Resolve the entire diagram and its colimit functorially by bounded injective
   complexes retaining the common bound. Apply closed costalk and exact open
   restriction. Derived adjunction identifies the original Hom diagram with the
   shifted Hom diagram on S, compatibly at the colimit vertex and on every leg.
5. Transport the lisse trivializations along the coefficient pullback isomorphism.
   Internal Hom from L is exact and colimit-preserving, and its exact tensor left
   adjoint makes it preserve K-injectives. Internal-Hom sections and derived
   coyoneda evaluation identify shifted Hom with derived sections of termwise
   internal Hom. Qcqs sections continuity proves this comparison invertible.
6. The leg identities identify the original comparison, followed by the vertex
   isomorphism, with the colimit of the diagram isomorphism followed by the
   comparison of step 5. Cancel the invertible vertex map. All constructions
   include empty strata and finite free modules of rank zero. -/
theorem constructibleExtContinuityStratum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {S Z V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : V ⟶ X) (uS : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion uS] [QuasiCompact uS]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hΛ : IsAdmissibleCoefficient Λ)
    (L : supportModules Λ S) (hL : ProEtale.IsLisseCoefficientModule Λ L)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (supportModules Λ X) ℤ)
    (b : ℤ) (hK : ∀ (t : I) (n : ℤ), n < b → IsZero ((K.obj t).X n)) (q : ℤ) :
    IsIso (colimit.post K
      (DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory (supportModules Λ X)) q ⋙
        preadditiveCoyoneda.obj
          (op ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj
            ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L)))))) := by
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace uS
  have : QuasiSeparatedSpace S := quasiSeparatedSpace_of_quasiSeparated uS
  have hij' : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  obtain ⟨M, hM, e, v, hleg⟩ := qcqsCostalkModel X Λ i j hij' uS L K ⟨b, hK⟩ q
  let F := shiftFunctor (DerivedCategory (supportModules Λ X)) q ⋙
    preadditiveCoyoneda.obj
      (op ((DerivedCategory.singleFunctor (supportModules Λ X) 0).obj
        ((lowerStar Λ i).obj ((openImmersionLowerShriek Λ uS).obj L))))
  let G := condensedShiftedHom Λ S ((DerivedCategory.singleFunctor _ 0).obj L) q
  have hG : IsIso (colimit.desc (M ⋙ G) (G.mapCocone (colimit.cocone M))) :=
    qcqsFiniteFreeHomContinuity S Λ L (lisseRawCover Λ L hL) M hM q
  have heq : colimit.post K (DerivedCategory.Q ⋙ F) ≫ v.hom =
      colimMap e.hom ≫ colimit.desc (M ⋙ G) (G.mapCocone (colimit.cocone M)) := by
    apply colimit.hom_ext
    intro t
    dsimp only [G] at ⊢
    simp only [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_desc]
    exact hleg t
  have : IsIso (colimit.post K (DerivedCategory.Q ⋙ F) ≫ v.hom) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ v.hom

end AlgebraicGeometry.ProEtale.CondensedRing
