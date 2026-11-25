/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import all WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all WeilConjectures.SixFunctors.Etale.Derived.Hom
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.Algebra.Category.Grp.Abelian
import all WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import all Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.CategoryTheory.Sites.CoverPreserving

/-! # The normalized completion comparison on the resolving class

Source: Stacks 07A6, 08TC and 0941; the primitive quotient/Roos construction
in completed-operation substitution, steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{t})
attribute [local instance 5000] scalarReductionSourceDerived
attribute [local instance 3000] integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory integralOperationsCountableProducts
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard constantSheaf SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence unrestrictedIntegralTransition
  unrestrictedTowerUnit IntegralOnSlice.augmentation
  CochainComplex.mappingCocone.lift
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
  IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  IntegralOnSlice.finite IntegralOnSlice.projection IntegralOnSlice.tower IntegralOnSlice.level
  IntegralOnSlice.reduction IntegralOnSlice.reductionWitness
  SemilinearSections.moduleAbelian
  IntegralOnSlice.qGood IntegralOnSlice.Good IntegralOnSlice.hasDerived
  scalarReductionSourceDerived
  SheafOfModules.restrictScalars SheafOfModules.unit
  completedIntegralCommRingProjectionUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf

attribute [local irreducible] TrfCompletionRoosNormalized

private theorem lift_transport
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {P : CochainComplex A ℤ} {K L : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (h : K = L) (γ : ∀ n, P ⟶ K.obj (op n)) (δ : ∀ n, P ⟶ L.obj (op n))
    (hγ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ fun n ↦ K.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift γ ≫ towerTransitionEndomorphism (K := fun n : ℕ ↦ K.obj (op n))
          (integralOperationsTowerStep K)) = 0)
    (hδ : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ fun n ↦ L.obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift δ ≫ towerTransitionEndomorphism (K := fun n : ℕ ↦ L.obj (op n))
          (integralOperationsTowerStep L)) = 0)
    (hc : ∀ n, γ n ≫ eqToHom (congrArg (fun T ↦ T.obj (op n)) h) = δ n) :
    CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ K.obj (op n))
          (integralOperationsTowerStep K)) (Pi.lift γ) 0 hγ ≫
        eqToHom (congrArg integralOperationsRoos h) =
      CochainComplex.mappingCocone.lift
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ L.obj (op n))
          (integralOperationsTowerStep L)) (Pi.lift δ) 0 hδ := by
  cases h
  have he : γ = δ := by
    funext n
    simpa only [eqToHom_refl, Category.comp_id] using hc n
  cases he
  exact Category.comp_id _

private theorem localized_transport
    {A B C H : Type*} [Category A] [Category B] [Category C] [Category H]
    (i : A ⥤ B) {F G : B ⥤ C} (h : F = G) (R : C ⥤ B) (Q : B ⥤ H) (P : A)
    (u : i.obj P ⟶ R.obj (F.obj (i.obj P)))
    (v : i.obj P ⟶ R.obj (G.obj (i.obj P)))
    (hu : u ≫ eqToHom (congrArg R.obj (congrArg (fun T ↦ T.obj (i.obj P)) h)) = v) :
    Q.map u ≫ (eqToIso (congrArg (fun T ↦ i ⋙ T ⋙ R ⋙ Q) h)).hom.app P = Q.map v := by
  cases h
  change Q.map u ≫ 𝟙 _ = Q.map v
  rw [Category.comp_id]
  simpa only [eqToHom_refl, Category.comp_id] using congrArg Q.map hu

private theorem globalTower_eq : IntegralOnSlice.tower l E X none =
    trfQuotientTowerFunctor l E X := IntegralOnSlice.globalTower_eq l E X

set_option backward.isDefEq.respectTransparency true in
private theorem augmentation_eq (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (n : ℕ) :
    ((IntegralOnSlice.augmentation l E X none).app P).app (op n) =
      unrestrictedTowerUnit l E X P n := by
  ext i U x
  unfold IntegralOnSlice.augmentation
  change _ = _
  have ha := (IntegralOnSlice.augmentation_existsUnique l E X none).exists.choose_spec
    P n i U x
  have hb := unrestrictedTowerUnit_condition l E X P n i U x
  change _ = _ at ha hb
  exact ha.trans hb.symm

attribute [local implicit_reducible] trfQuotientTowerFunctor integralOperationsGoodComplex

private theorem coneUnit_eq (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    IntegralOnSlice.roosUnit l E X none P ≫
        eqToHom (congrArg integralOperationsRoos
          (show (IntegralOnSlice.tower l E X none).obj P =
              (trfQuotientTowerFunctor l E X).obj P from
            congrArg (fun F ↦ F.obj P) (globalTower_eq l E X))) =
      trfStrictQuotientConeAugmentation l E X P := by
  unfold IntegralOnSlice.roosUnit IntegralOnSlice.productAugmentation
    trfStrictQuotientConeAugmentation
  apply lift_transport (congrArg (fun F ↦ F.obj P)
    (globalTower_eq l E X))
  intro n
  change ((IntegralOnSlice.augmentation l E X none).app P).app (op n) ≫
    eqToHom (show ((IntegralOnSlice.tower l E X none).obj P).obj (op n) =
      ((trfQuotientTowerFunctor l E X).obj P).obj (op n) from by
        unfold IntegralOnSlice.tower trfQuotientTowerFunctor
        rfl) = _
  simpa only [eqToHom_refl, Category.comp_id] using augmentation_eq l E X P n

attribute [local irreducible] IntegralOnSlice.tower trfQuotientTowerFunctor

attribute [local implicit_reducible] IntegralOnSlice.roosGood IntegralOnSlice.roos
  integralOperationsRoosFunctor
attribute [local irreducible] integralOperationsRoosMap integralOperationsRoos

attribute [local semireducible] integralOperationsRoos in
private theorem roosModel_hom
    (C : CoefficientDerivedSystemCalculus l E X)
    (O : CompletionUnit.OrdinaryModel l E X)
    (D : CompletionUnit.DerivedModel l E X C O)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    (roosModel l E X C O D).comparison.hom.app I = D.roos.inv.app I := by
  dsimp only [roosModel, comparisonFromModel, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, NatIso.ofComponents_hom_app, Iso.refl_hom]
  exact Category.comp_id _

private theorem cancel_inverse
    {A B : Type*} [Category A] [Category B] {F G H : A ⥤ B}
    (a : F ⟶ G) (b : F ⟶ H) (c : H ≅ G) (h : a ≫ c.inv = b) :
    ∀ K, b.app K ≫ c.hom.app K = a.app K := by
  intro K
  rw [← h]
  simp only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem descent
    {G D : Type*} [Category G] [Category D] (q : G ⥤ D)
    (ff : ((Functor.whiskeringLeft G D D).obj q).FullyFaithful)
    {F L : D ⥤ D} {R S : G ⥤ D}
    (e : q ⋙ F ≅ R) (z : R ≅ S) (rho : q ⋙ L ≅ S) :
    ∃ c : F ≅ L, ∀ P : G,
      c.inv.app (q.obj P) ≫ e.hom.app P = rho.hom.app P ≫ z.inv.app P := by
  let c := ff.preimageIso (e ≪≫ z ≪≫ rho.symm)
  refine ⟨c, fun P ↦ ?_⟩
  have h := congrArg (fun a ↦ a.app P) (ff.map_preimage ((e ≪≫ z ≪≫ rho.symm).inv))
  change c.inv.app (q.obj P) = _ at h
  rw [h]
  simp only [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

private theorem normalized_descent
    {G D : Type*} [Category G] [Category D] (q : G ⥤ D)
    (ff : ((Functor.whiskeringLeft G D D).obj q).FullyFaithful)
    {F L : D ⥤ D} {R S : G ⥤ D}
    (e : q ⋙ F ≅ R) (z : R ≅ S) (rho : q ⋙ L ≅ S)
    (a : 𝟭 D ⟶ L) (b : 𝟭 D ⟶ F)
    (h : ∀ P, a.app (q.obj P) ≫ rho.hom.app P =
      (b.app (q.obj P) ≫ e.hom.app P) ≫ z.hom.app P) :
    ∃ c : F ≅ L, ∀ K, b.app K ≫ c.hom.app K = a.app K := by
  obtain ⟨c, hc⟩ := descent q ff e z rho
  have he : a ≫ c.inv = b := by
    apply ff.map_injective
    ext P
    apply (cancel_mono (e.hom.app P)).1
    change (a.app (q.obj P) ≫ c.inv.app (q.obj P)) ≫ e.hom.app P = _
    rw [Category.assoc, hc P, ← Category.assoc, h P]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  exact ⟨c, cancel_inverse a b c he⟩

private theorem extract_third {A B C D : Sort*} {T₁ T₂ T₃ T₄ : Prop}
    {P₁ P₂ P₃ P₄ P₅ P₇ : A → B → C → D → Prop} {P₆ : C → Prop}
    (h : T₁ ∧ T₂ ∧ T₃ ∧ T₄ ∧
      ∃ a b c d, P₁ a b c d ∧ P₂ a b c d ∧ P₃ a b c d ∧ P₄ a b c d ∧
      P₅ a b c d ∧ P₆ c ∧ P₇ a b c d) : ∃ c, P₆ c := by
  obtain ⟨_, _, _, _, a, b, c, d, h⟩ := h
  exact ⟨c, h.2.2.2.2.2.1⟩
private theorem descent_data
    (g : X ⟶ X) [IsIso g]
    (C : CoefficientDerivedSystemCalculus l E X)
    (r : IntegralComparisonRoosModel l E X)
    (hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    ∃ rho, TrfCompletionRoosNormalized l E X C r rho := by
  exact extract_third
    (isomorphismMultiplicationConeDescent l E g hl hl C r)

private def actualLocalization : (integralOperationsGoodComplex l E X).FullSubcategory ⥤
    DerivedCategory (scalarReductionSource l E X) := integralOperationsGoodLocalization l E X
attribute [local irreducible] actualLocalization

private def actualCompletion : DerivedCategory (scalarReductionSource l E X) ⥤
    DerivedCategory (scalarReductionSource l E X) := IntegralOnSlice.completion l E X none
private def actualUnit : 𝟭 (DerivedCategory (scalarReductionSource l E X)) ⟶
    actualCompletion l E X := IntegralOnSlice.completionUnit l E X none
private def actualRoos : (integralOperationsGoodComplex l E X).FullSubcategory ⥤
    DerivedCategory (scalarReductionSource l E X) :=
  (integralOperationsGoodComplex l E X).ι ⋙ IntegralOnSlice.tower l E X none ⋙
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
attribute [local semireducible] actualLocalization in
private def actualComparison : actualLocalization l E X ⋙
    actualCompletion l E X ≅ actualRoos l E X :=
  IntegralOnSlice.completionComparison l E X none
attribute [local irreducible] actualCompletion actualUnit actualComparison
attribute [local implicit_reducible] actualRoos

attribute [local semireducible]
  actualUnit actualComparison actualCompletion actualLocalization in
private theorem completionUnit_equation
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (actualUnit l E X).app (DerivedCategory.Q.obj P.obj) ≫
        (actualComparison l E X).hom.app P =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none P.obj) := by
  simpa only [actualUnit, actualComparison, IntegralOnSlice.completionUnit,
    IntegralOnSlice.qGood, Functor.comp_obj, ObjectProperty.ι_obj] using
    (IntegralOnSlice.completionUnit_existsUnique l E X none).exists.choose_spec P

attribute [local irreducible] DerivedCategory DerivedCategory.Q
  roosModel comparisonFromModel IntegralOnSlice.roosUnit
  IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit

attribute [local irreducible] trfStrictQuotientConeAugmentation
  unrestrictedIntegralReductionFunctor unrestrictedIntegralComplexFunctor

attribute [local semireducible] actualLocalization in
private def actualRho (C : CoefficientDerivedSystemCalculus l E X)
    (rho : integralOperationsGoodLocalization l E X ⋙
        (C.reduction ⋙ coefficientSequenceLimit l E X) ≅
      (integralOperationsGoodComplex l E X).ι ⋙ trfQuotientTowerFunctor l E X ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) :
    actualLocalization l E X ⋙ (C.reduction ⋙ coefficientSequenceLimit l E X) ≅
      (integralOperationsGoodComplex l E X).ι ⋙ trfQuotientTowerFunctor l E X ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q := rho
attribute [local irreducible] actualRho

attribute [local semireducible] actualLocalization in
set_option backward.isDefEq.respectTransparency true in
private theorem representative_unit
    (C : CoefficientDerivedSystemCalculus l E X)
    (O : CompletionUnit.OrdinaryModel l E X)
    (D : CompletionUnit.DerivedModel l E X C O)
    (rho : integralOperationsGoodLocalization l E X ⋙
        (C.reduction ⋙ coefficientSequenceLimit l E X) ≅
      (integralOperationsGoodComplex l E X).ι ⋙ trfQuotientTowerFunctor l E X ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    (hrho : TrfCompletionRoosNormalized l E X C
      (roosModel l E X C O D) rho)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    C.adjunction.unit.app (DerivedCategory.Q.obj P.obj) ≫ rho.hom.app P =
      ((actualUnit l E X).app (DerivedCategory.Q.obj P.obj) ≫
        (actualComparison l E X).hom.app P) ≫
        (eqToIso (congrArg
      (fun T ↦ (integralOperationsGoodComplex l E X).ι ⋙ T ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) (globalTower_eq l E X))).hom.app P := by
  have hs := strictQuotientCompletionUnit l E X C O D (roosModel l E X C O D) rho
    (roosModel_hom l E X C O D) hrho P
  have ha := localized_transport (integralOperationsGoodComplex l E X).ι
    (globalTower_eq l E X) integralOperationsRoosFunctor DerivedCategory.Q P
    (IntegralOnSlice.roosUnit l E X none P.obj)
    (trfStrictQuotientConeAugmentation l E X P.obj) (coneUnit_eq l E X P.obj)
  have hb := completionUnit_equation l E X P
  exact hs.trans (ha.symm.trans (congrArg
    (fun f ↦ f ≫ (eqToIso (congrArg
      (fun T ↦ (integralOperationsGoodComplex l E X).ι ⋙ T ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
      (globalTower_eq l E X))).hom.app P) hb.symm))

attribute [local semireducible] actualLocalization in
set_option backward.isDefEq.respectTransparency true in
private theorem completion_whiskering :
    Nonempty (((Functor.whiskeringLeft
      (integralOperationsGoodComplex l E X).FullSubcategory
      (DerivedCategory (scalarReductionSource l E X))
      (DerivedCategory (scalarReductionSource l E X))).obj
        (actualLocalization l E X)).FullyFaithful) := by
  exact IntegralOnSlice.goodWhiskering l E X none
attribute [local semireducible] actualRho actualLocalization in
set_option backward.isDefEq.respectTransparency true in
private theorem completion_from_normalized
    (C : CoefficientDerivedSystemCalculus l E X)
    (O : CompletionUnit.OrdinaryModel l E X)
    (D : CompletionUnit.DerivedModel l E X C O)
    (rho : integralOperationsGoodLocalization l E X ⋙
        (C.reduction ⋙ coefficientSequenceLimit l E X) ≅
      (integralOperationsGoodComplex l E X).ι ⋙ trfQuotientTowerFunctor l E X ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
    (hrho : TrfCompletionRoosNormalized l E X C
      (roosModel l E X C O D) rho) :
    ∃ c : actualCompletion l E X ≅
      C.reduction ⋙ coefficientSequenceLimit l E X,
      ∀ K : DerivedCategory (scalarReductionSource l E X),
        (actualUnit l E X).app K ≫ c.hom.app K =
        C.adjunction.unit.app K := by
  apply normalized_descent (actualLocalization l E X)
    (Classical.choice (completion_whiskering l E X))
    (actualComparison l E X) (eqToIso (congrArg
      (fun T ↦ (integralOperationsGoodComplex l E X).ι ⋙ T ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) (globalTower_eq l E X)))
    (actualRho l E X C rho)
    C.adjunction.unit (actualUnit l E X)
  intro P
  exact representative_unit l E X C O D rho hrho P
set_option backward.isDefEq.respectTransparency true in
attribute [local semireducible] actualCompletion actualUnit in
set_option backward.isDefEq.respectTransparency.types true in
/-- Completion is naturally isomorphic to reduction followed by total derived limit.
Source: Stacks 07A6, 0941; localization of the normalized strict quotient/Roos model.
(blueprint: lem-pur-normalized-completion-realization).

Proof: use the ordinary and derived models to obtain the normalized Roos comparison
on good representatives. Fully faithful whiskering descends this comparison to
completion. Both strict quotient augmentations send every section x to 1 tensor x,
so their product coordinates agree and their shifted coordinates are zero.
Transport of the mapping cocone lift identifies the two augmentations. The strict
quotient completion-unit theorem gives the unit equation on good representatives.
The uniqueness characterization of completionUnit extends it to all objects;
cancel the inverse comparison to obtain the asserted equation. -/
theorem normalizedCompletionRealization
    (C : CoefficientDerivedSystemCalculus l E X)
    (O : CompletionUnit.OrdinaryModel l E X)
    (D : CompletionUnit.DerivedModel l E X C O)
    (hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    ∃ c : (IntegralOnSlice.completion l E X none :
        DerivedCategory (scalarReductionSource l E X) ⥤
          DerivedCategory (scalarReductionSource l E X)) ≅
      C.reduction ⋙ coefficientSequenceLimit l E X,
      ∀ K : DerivedCategory (scalarReductionSource l E X),
        (IntegralOnSlice.completionUnit l E X none).app K ≫ c.hom.app K =
        C.adjunction.unit.app K := by
  let r : IntegralComparisonRoosModel l E X := roosModel l E X C O D
  obtain ⟨rho, hrho⟩ := descent_data l E X (𝟙 X) C r hl
  exact completion_from_normalized l E X C O D rho hrho

end WeilConjectures
