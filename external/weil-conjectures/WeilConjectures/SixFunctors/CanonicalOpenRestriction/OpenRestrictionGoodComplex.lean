/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
import all WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenCoefficientOperationsExistence
import all WeilConjectures.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import all WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.CountableTensorStructures.CountableTensorStructuresSupplement
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.AdditiveTotalTensorConeComparison
import all WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import all WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Good complexes under open restriction

Source: Stacks Project, Cohomology on Sites, Tag 0E8K; Modules on Sites, Tag 03DJ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.CanonicalOpenRestriction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)

open WeilConjectures.OpenSemilinearTensor
attribute [local instance] sliceRingSheafify inverseSliceContinuous sliceCocontinuous
open CategoryTheory.MonoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients

private theorem finiteMap_eq (n : ℕ) :
    o.finiteMap n = (finiteSliceIso l E j n).hom := by
  let A := CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))
  let α := ((Over.forget (openObject j)).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max u (t+1)} ((ProEt.topology X).over (openObject j))
    (ProEt.topology X)).app ((Functor.const X.ProEtᵒᵖ).obj A)
  apply (cancel_epi α.hom).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
  · exact ((sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
      ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).obj
        (rings l E U n) |>.property
  · apply NatTrans.ext
    funext V
    have h := NatTrans.congr_app
      ((Over.forget (openObject j)).toSheafify_pullbackSheafificationCompatibility
        CommRingCat.{max u (t+1)}
        ((ProEt.topology X).over (openObject j)) (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj A)) V
    change (toSheafify ((ProEt.topology X).over (openObject j)) _).app V ≫
      α.hom.hom.app V = _ at h
    change _ ≫ (α.hom.hom.app V ≫ (o.finiteMap n).hom.app V) =
      _ ≫ (α.hom.hom.app V ≫ (finiteSliceIso l E j n).hom.hom.app V)
    have hl := congrArg (fun f ↦ f ≫ (o.finiteMap n).hom.app V) h
    have hr := congrArg (fun f ↦ f ≫ (finiteSliceIso l E j n).hom.hom.app V) h
    have hc := (o.finiteConstants n V.unop).trans
      (constantSliceIso_unit j A V.unop).symm
    exact (Category.assoc _ _ _).symm.trans
      (hl.trans (hc.trans (hr.symm.trans (Category.assoc _ _ _))))

private theorem completedMap_eq :
    o.completedMap = (completedSliceIso l E j).hom := by
  apply (sheafCompose _ (forget₂ CommRingCat.{max u (t+1)}
    RingCat.{max u (t+1)})).map_injective
  let F := (sliceSite j).sheafPushforwardContinuous
    RingCat.{max u (t+1)} ((ProEt.topology X).over (openObject j)) (ProEt.topology U)
  have : (ProEt.sliceEquiv X (openObject j)).symm.inverse.IsContinuous
      ((ProEt.topology X).over (openObject j)) (ProEt.topology U) := sliceContinuous j
  let adj := (ProEt.sliceEquiv X (openObject j)).symm.toAdjunction.sheafPushforwardContinuous
     (E := RingCat.{max u (t+1)})
      (ProEt.topology U) ((ProEt.topology X).over (openObject j))
  have hpres : PreservesLimitsOfShape ℕᵒᵖ F :=
    adj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have hp : PreservesLimit (integralCoefficientSheafSystem l E U) F :=
    hpres.preservesLimit
  apply (hp.preserves (limit.isLimit (integralCoefficientSheafSystem l E U))).some.hom_ext
  intro n
  have h : o.completedMap ≫
      ((sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
        ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).map
          (completedIntegralCommRingProjectionUnrestricted l E U n.unop) =
      (completedSliceIso l E j).hom ≫
      ((sliceSite j).sheafPushforwardContinuous CommRingCat.{max u (t+1)}
        ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).map
          (completedIntegralCommRingProjectionUnrestricted l E U n.unop) :=
    (o.projections n.unop).trans (by
    rw [finiteMap_eq l E j o n.unop]
    exact (completedSliceIso_projection l E j n.unop).symm)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply RingCat.hom_ext
  apply RingHom.ext
  intro x
  exact congrArg (fun f ↦ (((sheafCompose _ (forget₂ CommRingCat.{max u (t+1)}
    RingCat.{max u (t+1)})).map f).hom.app V).hom x) h

/-- Open restriction preserves flat-term K-flat complexes in the prescribed transports.
Source: Stacks, Cohomology on Sites, Tag 0E8K, and Modules on Sites, Tag 03DJ.
(blueprint: lem-sf-open-restriction-good-complex).

Proof: first restrict to the ringed slice. Restriction is exact and commutes with
tensor and direct sums. For an acyclic test complex on the slice, its exact extension
by zero is acyclic; the projection tensor isomorphism and K-flatness of the original
complex show that its tensor with the restricted complex is acyclic. Extension by
zero reflects acyclicity, proving K-flatness. The same argument for a single flat
module proves preservation of flat terms. The forward equivalence o.integral is
the continuous pushforward along the slice/open equivalence and the normalized
completed coefficient isomorphism. Its inverse therefore preserves tensor, direct
sums, and exact sequences. Transporting the previous acyclicity tests along this
monoidal equivalence proves the asserted good-complex predicate. This does not
require completeness, bounds or a nonempty open. -/
theorem restriction_preservesGood
    (Q : CochainComplex (scalarReductionSource l E X) ℤ)
    (hQ : integralOperationsGoodComplex l E X Q) :
    integralOperationsGoodComplex l E U
      (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l E U
  let W := openObject j
  let : EssentiallySmall.{max u (t+1)} X.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t+1)} U.ProEt := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t+1)} (Over W) := essentiallySmallSelf _
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.monoidalCategory (R.over W)
  let : MonoidalCategory (scalarReductionSource l E U) :=
    SheafOfModules.monoidalCategory S
  let : MonoidalCategory (SheafOfModules.{max u (t+1)}
      ((completedIntegralCoefficientSheafUnrestricted l E X).over (openObject j))) :=
    SheafOfModules.monoidalCategory (R.over W)
  have hm : IsIso o.completedMap := by
    rw [completedMap_eq l E j o]
    infer_instance
  let a := (sheafCompose ((ProEt.topology X).over W)
    (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).mapIso
      (asIso o.completedMap)
  let : (sliceSite j).IsCocontinuous ((ProEt.topology X).over W) (ProEt.topology U) :=
    sliceCocontinuous j
  obtain ⟨hmon⟩ := SheafOfModules.ringed_cocontinuous_monoidal (sliceSite j) (R.over W) S a
  let : o.integral.functor.Monoidal := by
    rw [o.integralFunctor]
    exact hmon
  let : o.integral.inverse.Monoidal := o.integral.inverseMonoidal
  let : o.integral.functor.Additive := o.integralAdditive
  let : o.integral.inverse.Additive := o.integral.inverse_additive
  let : o.integral.symm.functor.Additive := inferInstanceAs o.integral.inverse.Additive
  let : o.integral.symm.inverse.Additive := inferInstanceAs o.integral.functor.Additive
  let : MonoidalPreadditive (scalarReductionSource l E U) :=
    SheafOfModules.cochainModulesPreadditive S
  let : MonoidalPreadditive (SheafOfModules.{max u (t+1)}
      ((completedIntegralCoefficientSheafUnrestricted l E X).over (openObject j))) :=
    SheafOfModules.cochainModulesPreadditive (R.over W)
  let : TensorPreservesCountableCoproducts
      (SheafOfModules.{max u (t+1)}
        ((sheafCompose (ProEt.topology U) (forget₂ _ _)).obj S)) :=
    ⟨fun _ _ _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩
  let : TensorPreservesCountableCoproducts
      (SheafOfModules.{max u (t+1)}
        ((sheafCompose ((ProEt.topology X).over W) (forget₂ _ _)).obj (R.over W))) :=
    ⟨fun _ _ _ ↦ inferInstance, fun _ _ _ ↦ inferInstance⟩
  let : TensorPreservesCountableCoproducts (scalarReductionSource l E U) :=
    inferInstanceAs (TensorPreservesCountableCoproducts
      (SheafOfModules.{max u (t+1)}
        ((sheafCompose (ProEt.topology U) (forget₂ _ _)).obj S)))
  let : TensorPreservesCountableCoproducts (SheafOfModules.{max u (t+1)}
      ((completedIntegralCoefficientSheafUnrestricted l E X).over (openObject j))) :=
    inferInstanceAs (TensorPreservesCountableCoproducts
      (SheafOfModules.{max u (t+1)}
        ((sheafCompose ((ProEt.topology X).over W) (forget₂ _ _)).obj (R.over W))))
  let P : CochainComplex (SheafOfModules.{max u (t+1)}
      ((sheafCompose ((ProEt.topology X).over W)
        (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).obj (R.over W))) ℤ :=
    ((SheafOfModules.localizedSystemRestriction.{t+1, t, max u (t+1)} R W).mapHomologicalComplex
       (.up ℤ)).obj Q
  have hk : CochainComplex.IsKFlatIndependentCoefficients (R := R.over W) P :=
    (SheafOfModules.ringedSite_restriction_exact_kflat.{t+1, t, max u (t+1)}
      (ProEt.topology X) R W).2.2 Q hQ.1
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite.{t+1, t, max u (t+1), max u (t+1)}
      (J := (ProEt.topology X).over W) (R := R.over W) (P.X i) := by
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{t+1, t,
      max u (t+1), max u (t+1)}
      (R.over W) ((Q.X i).over W)).2
    intro V n b x hx
    obtain ⟨Z, hZ, h⟩ :=
      (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{t+1, t,
        max u (t+1), max u (t+1)} R (Q.X i)).1
        (hQ.2 i) V.left n b x hx
    refine ⟨(Sieve.overEquiv V).symm Z, ?_, ?_⟩
    · exact ((ProEt.topology X).mem_over_iff _).2 (by simpa using hZ)
    · intro V' f hf
      exact h V'.left f.left hf
  constructor
  · have hleft := (Equivalence.acyclic_tensor_swap P).mpr hk
    have hmap := (Equivalence.acyclic_tensor_map_iff o.integral.symm P).mp hleft
    exact (Equivalence.acyclic_tensor_swap
      ((o.integral.inverse.mapHomologicalComplex (.up ℤ)).obj P)).mp hmap
  · intro i
    have hr := (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (R.over W) (P.X i)) (hf i)
    have hl : ObjectProperty.flat (P.X i) :=
      ⟨(exactFunctor _ _).prop_of_iso
        (BraidedCategory.tensorLeftIsoTensorRight (P.X i)).symm hr, hr⟩
    have ht := Equivalence.flat_map o.integral.symm (P.X i) hl
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S (o.integral.inverse.obj (P.X i))).symm ht.2

end WeilConjectures.CanonicalOpenRestriction
