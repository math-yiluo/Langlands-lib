/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.CommutativeConstantSliceRestriction
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ProfiniteCoefficientSliceOrdinary

/-! # Derived coefficient extension under profinite slice restriction

Source: Hemo--Richarz--Scholbach, (3.1)--(3.2), Remark 3.2; Stacks 06YY and 07A4.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits

private noncomputable def restrictedUnitIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u + 1}} (e : R ≅ B) :
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)).obj
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≅
      SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) := by
  let U := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let BB := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  refine (SheafOfModules.fullyFaithfulForget A).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
  · let h : (U.obj (SheafOfModules.unit BB)).val.obj V ≃ₗ[R.obj.obj V]
        (SheafOfModules.unit A).val.obj V :=
      { toFun := e.inv.hom.app V
        invFun := e.hom.hom.app V
        left_inv := fun x ↦ ConcreteCategory.congr_hom
          (congrArg (fun f : B ⟶ B ↦ f.hom.app V) e.inv_hom_id) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom
          (congrArg (fun f : R ⟶ R ↦ f.hom.app V) e.hom_inv_id) x
        map_add' := map_add _
        map_smul' := by
          intro r x
          change B.obj.obj V at x
          change e.inv.hom.app V (e.hom.hom.app V r * x) = r * e.inv.hom.app V x
          rw [map_mul]
          congr 1
          exact ConcreteCategory.congr_hom
            (congrArg (fun f : R ⟶ R ↦ f.hom.app V) e.hom_inv_id) r }
    exact h.toModuleIso
  · intro V W f
    ext x
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) x

private theorem restrictIso_kflat
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u + 1}}
    (e : R ≅ B)
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := B) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          e.hom)).mapHomologicalComplex
          (.up ℤ)).obj K) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let U : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    SheafOfModules.unit _
  have hu : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R) U := by
    have h : ObjectProperty.flat (show SheafOfModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) from U) :=
      ObjectProperty.prop_unit ObjectProperty.flat
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R U).symm h.tensorRight
  have hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (R := R)
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map e.hom)).obj
          (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))) :=
    (exactFunctor _ _).prop_of_iso
      ((SheafOfModules.siteSheafTensorRightIso R U) ≪≫
        (CategoryTheory.MonoidalCategory.curriedTensor _).flip.mapIso
          (restrictedUnitIso e).symm ≪≫
        (SheafOfModules.siteSheafTensorRightIso R _).symm) hu
  exact (SheafOfModules.isKFlat_restrictScalars_of_flat e.hom hflat K hK).1

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (S : Profinite.{u})

end AlgebraicGeometry.ProEtale.CondensedRing
