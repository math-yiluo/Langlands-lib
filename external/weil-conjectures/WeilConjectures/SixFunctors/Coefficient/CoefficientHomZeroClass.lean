/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses
import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Canonical zero-cycle class in derived global Hom

Source: Stacks Project, Tags 08JA and 079P
(blueprint: def-coef-hom-zero-cycle-class).

## Main definitions

- `coefficientGlobalSections`: the recorded total derived section functor.
- `coefficientHomZeroClass`: the actual zero-cycle class via the derived unit.
- `coefficientHomZeroEvaluation`: evaluation by the fixed product projections.
- `coefficientHomZeroEquiv`: the uniquely normalized recorded H⁰ RHom identification.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
universe u c v a b w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] homComplexFunctor

/-- Total derived global sections on the original site and coefficient ring.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class).
This is the derived functor underlying the recorded zeroth hypercohomology. -/
noncomputable def coefficientGlobalSections
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))] :
    DerivedCategory (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ⥤
        @DerivedCategory AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard _) :=
  letI : IsGrothendieckAbelian.{max c v u} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let F := preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))
  F.rightDerivedFunctor

/-- The ordinary global-sections functor, written using Mathlib's module unit.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable abbrev coefficientOrdinarySections
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u}) :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))

/-- The universal right-derived comparison on complexes, before inverting it on
K-injectives. It is used to fix global-section comparisons on simultaneous resolutions.
Source: Stacks 079P (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientRightDerivedComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Abelian A] [Category.{w} B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  ((DerivedCategory.quotientCompQhIso _).app _).inv ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).app K).hom

/-- The canonical site-global-sections comparison, with the Grothendieck instance
at the correct coefficient universe.
Source: Stacks 079P, 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientSiteSectionsComparison
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (K : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (@DerivedCategory.Q AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard _)).obj
        (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (coefficientGlobalSections.{u, c, v} J A).obj (DerivedCategory.Q.obj K) :=
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  letI : IsGrothendieckAbelian.{max c v u} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  coefficientRightDerivedComparison (coefficientOrdinarySections.{u, c, v} J A) K

section RightDerivedUnit

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
  [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions D]

@[no_expose] private noncomputable def zeroRightDerivedUnitNatTrans
    (F : D ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app K := F.rightDerivedFunctorUnitQ K
  naturality {_X _Y} f := F.rightDerivedFunctorUnitQ_naturality f

end RightDerivedUnit

section DerivedHomotopyComparison

variable {D : Type a} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w} D]
  (I : CochainComplex D ℤ ⥤ CochainComplex D ℤ)
  (η : 𝟭 (CochainComplex D ℤ) ⟶ I)
  (hI : ∀ M, (I.obj M).IsKInjective) (hη : ∀ M, QuasiIso (η.app M))

@[no_expose] private noncomputable def zeroResolutionInverse (M : CochainComplex D ℤ) :
    DerivedCategory.Q.obj (I.obj M) ⟶ DerivedCategory.Q.obj M :=
  letI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr (hη M)
  inv (DerivedCategory.Q.map (η.app M))

set_option backward.isDefEq.respectTransparency false in
-- The homotopy-localization comparison checks its chosen localization functors.
@[no_expose] private noncomputable def zeroDerivedHomotopyIso :
    (HomotopyCategory.quotient D (.up ℤ)).op.prod
        (I ⋙ HomotopyCategory.quotient D (.up ℤ)) ⋙
      Functor.uncurry.obj (preadditiveCoyoneda (C := HomotopyCategory D (.up ℤ))) ⋙
        AddCommGrpCat.uliftFunctor.{w, v} ≅
      DerivedCategory.Q.op.prod DerivedCategory.Q ⋙
        Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory D)) ⋙
          AddCommGrpCat.uliftFunctor.{v, w} := by
  classical
  let q := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := D)
  let σ := DerivedCategory.quotientCompQhIso D
  let H := Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory D))
  let HK := Functor.uncurry.obj
    (preadditiveCoyoneda (C := HomotopyCategory D (ComplexShape.up ℤ)))
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let B := q.op.prod (I ⋙ q) ⋙ HK ⋙ U
  let T := Q.op.prod Q ⋙ H ⋙ V
  have hi (M : CochainComplex D ℤ) : IsIso (Q.map (η.app M)) := by
    have := hη M
    infer_instance
  let t (P : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ) :
      (DerivedCategory.Qh.obj (q.obj P.1.unop) ⟶
        DerivedCategory.Qh.obj (q.obj (I.obj P.2))) ≃+
      (Q.obj P.1.unop ⟶ Q.obj P.2) := by
    have := hi P.2
    exact
      { toEquiv := Iso.homCongr (σ.app P.1.unop)
          (σ.app (I.obj P.2) ≪≫ (asIso (Q.map (η.app P.2))).symm)
        map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }
  let e (P : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ) : B.obj P ≃+ T.obj P :=
    AddEquiv.ulift.trans
      ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
        (by have := hI P.2; exact CochainComplex.IsKInjective.Qh_map_bijective _ _)).trans
        ((t P).trans AddEquiv.ulift.symm))
  let b : B ≅ T := NatIso.ofComponents (fun P ↦ (e P).toAddCommGrpIso) (by
    intro P P' f
    ext x
    apply ULift.ext
    dsimp [B, T, e, t, HK, H, U, V, Functor.uncurry,
      preadditiveCoyoneda, preadditiveCoyonedaObj, AddCommGrpCat.uliftFunctor,
      AddEquiv.toAddCommGrpIso, AddEquiv.ofBijective, Iso.homCongr,
      AddEquiv.ulift, Equiv.ulift, Functor.mapAddHom]
    have := hi P.2
    have := hi P'.2
    have hn : Q.map (I.map f.2) ≫ inv (Q.map (η.app P'.2)) =
        inv (Q.map (η.app P.2)) ≫ Q.map f.2 := by
      apply (cancel_epi (Q.map (η.app P.2))).mp
      rw [← Category.assoc, ← Q.map_comp, ← η.naturality f.2, Q.map_comp]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        IsIso.hom_inv_id_assoc, Functor.id_map]
    simp only [AddMonoidHom.mk'_apply, Functor.map_comp, Category.assoc]
    dsimp only [σ]
    rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
    rw [hn])
  exact b

private lemma zeroDerivedHomotopyIso_apply (L M : CochainComplex D ℤ)
    (f : (HomotopyCategory.quotient D (.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient D (.up ℤ)).obj (I.obj M)) :
    ((zeroDerivedHomotopyIso I η hI hη).hom.app (op L, M) (ULift.up f)).down =
      (DerivedCategory.quotientCompQhIso D).inv.app L ≫ DerivedCategory.Qh.map f ≫
        (DerivedCategory.quotientCompQhIso D).hom.app (I.obj M) ≫
          zeroResolutionInverse I η hη M := by
  rfl

private lemma zeroDerivedHomotopyIso_quotient_apply (L M : CochainComplex D ℤ)
    (f : L ⟶ I.obj M) :
    ((zeroDerivedHomotopyIso I η hI hη).hom.app (op L, M)
      (ULift.up ((HomotopyCategory.quotient D (.up ℤ)).map f))).down =
      DerivedCategory.Q.map f ≫ zeroResolutionInverse I η hη M := by
  rw [zeroDerivedHomotopyIso_apply]
  rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rw [Iso.inv_hom_id_app_assoc]

attribute [local irreducible] zeroDerivedHomotopyIso

end DerivedHomotopyComparison

private lemma zeroCycleClasses_surjective
    {X Y Z : AddCommGrpCat.{u}} (π : X ⟶ Y) [Epi π]
    (k : (AddCommGrpCat.uliftFunctor.{w, u}).obj Y ≅
      (AddCommGrpCat.uliftFunctor.{w, u}).obj Z)
    (cl : X → Z) (hcl : ∀ v, k.hom (ULift.up (π v)) = ULift.up (cl v)) :
    Function.Surjective cl := by
  intro x
  obtain ⟨y, hy⟩ := k.addCommGroupIsoToAddEquiv.surjective (ULift.up x)
  obtain ⟨v, hv⟩ := (AddCommGrpCat.epi_iff_surjective π).mp inferInstance y.down
  have heq : ULift.up (π v) = y := by
    apply ULift.ext
    exact hv
  exact ⟨v, congrArg ULift.down ((hcl v).symm.trans ((congrArg k.hom heq).trans hy))⟩

section AssociativeLocalizationComparison

variable {S T K₀ D E G H : Type*}
  [Category* S] [Category* T] [Category* K₀] [Category* D]
  [Category* E] [Category* G] [Category* H]
  (P : S ⥤ T) (R : T ⥤ D) (B : S ⥤ K₀) (Q : K₀ ⥤ D)
  (Γ : D ⥤ E) (H₀ : E ⥤ G) (U : G ⥤ H) (e : P ⋙ R ≅ B ⋙ Q)

@[no_expose] private noncomputable def zeroAssociativeLocalizationIso :
    P ⋙ R ⋙ (Γ ⋙ H₀) ⋙ U ≅ (B ⋙ Q ⋙ Γ ⋙ H₀) ⋙ U :=
  (Functor.associator P R ((Γ ⋙ H₀) ⋙ U)).symm ≪≫
    Functor.isoWhiskerRight e ((Γ ⋙ H₀) ⋙ U) ≪≫
      (Functor.associator (B ⋙ Q) (Γ ⋙ H₀) U).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator B Q (Γ ⋙ H₀)) U

private lemma zeroAssociativeLocalizationIso_inv_app (X : S) :
    (zeroAssociativeLocalizationIso P R B Q Γ H₀ U e).inv.app X =
      U.map ((Γ ⋙ H₀).map (e.inv.app X)) := by
  simp [zeroAssociativeLocalizationIso]

attribute [local irreducible] zeroAssociativeLocalizationIso

end AssociativeLocalizationComparison

section UnliftHomComparison

variable {D : Type a} [Category.{w} D] [Preadditive D]
  (F : Dᵒᵖ × D ⥤ AddCommGrpCat.{v})
  (z : F ⋙ AddCommGrpCat.uliftFunctor.{w, v} ≅
    Functor.uncurry.obj (preadditiveCoyoneda (C := D)) ⋙
      AddCommGrpCat.uliftFunctor.{v, w})

@[no_expose] private noncomputable def zeroUnliftHomEquiv (P : Dᵒᵖ × D) :
    F.obj P ≃+ (P.1.unop ⟶ P.2) :=
  AddEquiv.ulift.symm.trans
    ((z.app P).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

private lemma zeroUnliftHomEquiv_apply (P : Dᵒᵖ × D) (x : F.obj P) :
    zeroUnliftHomEquiv F z P x = (z.hom.app P (ULift.up x)).down := rfl

private lemma zeroUnliftHomEquiv_naturality (P P' : Dᵒᵖ × D) (f : P ⟶ P')
    (x : F.obj P) :
    zeroUnliftHomEquiv F z P' (F.map f x) =
      f.1.unop ≫ zeroUnliftHomEquiv F z P x ≫ f.2 := by
  have hz := ConcreteCategory.congr_hom (z.hom.naturality f) (ULift.up x)
  change ULift.up (zeroUnliftHomEquiv F z P' (F.map f x)) =
    ULift.up ((f.1.unop ≫ zeroUnliftHomEquiv F z P x) ≫ f.2) at hz
  exact (congrArg ULift.down hz).trans (Category.assoc _ _ _)

attribute [local irreducible] zeroUnliftHomEquiv

end UnliftHomComparison

set_option backward.isDefEq.respectTransparency false in
@[no_expose] private noncomputable def zeroGlobalHomologyNatIsoOfComplexIso
    {D : Type a} [Category.{v} D] [Preadditive D]
    (F : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ)
    (e : ∀ X, F.obj X ≅ CochainComplex.HomComplex X.1.unop X.2)
    (he : ∀ {X Y} (f : X ⟶ Y), F.map f ≫ (e Y).hom =
      (e X).hom ≫ CategoryTheory.externalMap f.1.unop f.2) :
    F ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) 0 ≅
      (HomotopyCategory.quotient
        D
          (.up ℤ)).op.prod (HomotopyCategory.quotient _ (.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) 0
  let q := HomotopyCategory.quotient
    D (.up ℤ)
  let iso : F ⋙ H ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda :=
    NatIso.ofComponents
      (fun X ↦ H.mapIso (e X) ≪≫
        CategoryTheory.externalHomologyIso X.1.unop X.2) (by
      intro X Y f
      have h : H.map ((F).map f) ≫
          H.map (e Y).hom =
          H.map (e X).hom ≫
            H.map (CategoryTheory.externalMap f.1.unop f.2) := by
        simpa only [Functor.map_comp, Quiver.Hom.op_unop, Prod.mk.eta] using
          H.congr_map (he f)
      dsimp only [H, q] at h ⊢
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [← Category.assoc, h, Category.assoc]
      change H.map (e X).hom ≫
          HomologicalComplex.homologyMap (CategoryTheory.externalMap f.1.unop f.2) 0 ≫
            (CategoryTheory.externalHomologyIso Y.1.unop Y.2).hom = _
      rw [CategoryTheory.externalHomologyIso_naturality]
      ext a
      change (q.map f.1.unop ≫ _ ≫ q.map f.2) = _
      exact (Category.assoc _ _ _).symm)
  exact iso

private lemma zeroGlobalHomologyNatIsoOfComplexIso_hom_app
    {D : Type a} [Category.{v} D] [Preadditive D]
    (F : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ)
    (e : ∀ X, F.obj X ≅ CochainComplex.HomComplex X.1.unop X.2)
    (he : ∀ {X Y} (f : X ⟶ Y), F.map f ≫ (e Y).hom =
      (e X).hom ≫ CategoryTheory.externalMap f.1.unop f.2)
    (X : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ) :
    (zeroGlobalHomologyNatIsoOfComplexIso F e he).hom.app X =
      HomologicalComplex.homologyMap (e X).hom 0 ≫
        (CategoryTheory.externalHomologyIso X.1.unop X.2).hom := rfl

private lemma zeroHomologyIsoOnCycle
    {D : Type a} [Category.{v} D] [Preadditive D]
    (L M : CochainComplex D ℤ) (K : CochainComplex AddCommGrpCat.{v} ℤ)
    (e : K ≅ CochainComplex.HomComplex L M) (z : K.cycles 0) :
    (HomologicalComplex.homologyMap e.hom 0 ≫
      (CategoryTheory.externalHomologyIso L M).hom) (K.homologyπ 0 z) =
        (HomotopyCategory.quotient D (.up ℤ)).map
          ((HomologicalComplex.cyclesMapIso e 0 ≪≫
            (CochainComplex.HomComplex.leftHomologyData L M 0).cyclesIso).hom z).homOf := by
  let h := CochainComplex.HomComplex.leftHomologyData L
    M 0
  have ha : (HomologicalComplex.homologyMapIso
      e 0 ≪≫ h.homologyIso).hom
        (K.homologyπ 0 z) =
      CochainComplex.HomComplex.CohomologyClass.mk
        ((HomologicalComplex.cyclesMapIso e 0 ≪≫ h.cyclesIso).hom z) := by
    have hh := ConcreteCategory.congr_hom h.homologyπ_comp_homologyIso_hom
      (HomologicalComplex.cyclesMap e.hom 0 z)
    have hh' := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality
      e.hom 0) z
    exact (congrArg h.homologyIso.hom hh').trans hh
  change CategoryTheory.zeroClassEquiv _ _
    ((HomologicalComplex.homologyMapIso e 0 ≪≫
      h.homologyIso).hom _) = _
  rw [ha, CategoryTheory.zeroClassEquiv_mk]

private lemma zeroNaturalFamilies_eq
    {D : Type a} [Category.{v} D] [Preadditive D]
    {K : Type*} [Category* K] (F : Dᵒᵖ × D ⥤ AddCommGrpCat.{u}) (Q : K ⥤ D)
    (flat : K → Prop)
    (e e' : ∀ P Q : D, F.obj (op P, Q) ≃+ (P ⟶ Q))
    (he : ∀ (P Q P' Q' : D) (f : P' ⟶ P) (g : Q ⟶ Q') (x : F.obj (op P, Q)),
      e P' Q' (F.map (Prod.mkHom f.op g) x) = f ≫ e P Q x ≫ g)
    (he' : ∀ (P Q P' Q' : D) (f : P' ⟶ P) (g : Q ⟶ Q') (x : F.obj (op P, Q)),
      e' P' Q' (F.map (Prod.mkHom f.op g) x) = f ≫ e' P Q x ≫ g)
    (hP : ∀ P : D, ∃ L : K, flat L ∧ Nonempty (Q.obj L ≅ P))
    (hQ : ∀ P : D, ∃ M : K, Nonempty (Q.obj M ≅ P))
    (hbase : ∀ L M : K, flat L → ∀ x : F.obj (op (Q.obj L), Q.obj M),
      e (Q.obj L) (Q.obj M) x = e' (Q.obj L) (Q.obj M) x) : e = e' := by
  classical
  funext P R
  apply AddEquiv.ext
  intro x
  obtain ⟨L, hL, ⟨s⟩⟩ := hP P
  obtain ⟨M, ⟨r⟩⟩ := hQ R
  let g : (op (Q.obj L), Q.obj M) ⟶ (op P, R) := (s.inv.op, r.hom)
  have : IsIso g := by
    change IsIso (Prod.mkHom s.inv.op r.hom)
    exact (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  let a := F.map g
  have : IsIso a := inferInstance
  have hn₁ := he (Q.obj L) (Q.obj M) P R s.inv r.hom (inv a x)
  have hn₂ := he' (Q.obj L) (Q.obj M) P R s.inv r.hom (inv a x)
  change e P R (a (inv a x)) = _ at hn₁
  change e' P R (a (inv a x)) = _ at hn₂
  rw [IsIso.inv_hom_id_apply] at hn₁ hn₂
  exact hn₁.trans ((congrArg (fun m ↦ s.inv ≫ m ≫ r.hom)
    (hbase L M hL (inv a x))).trans hn₂.symm)

private lemma zeroWhiskeredIso_apply
    {B D : Type*} [Category* B] [Category* D]
    (S : B ⥤ D) {F G : D ⥤ AddCommGrpCat.{u}} (e : F ≅ G) (X : B)
    (x : F.obj (S.obj X)) :
    (Functor.isoWhiskerLeft S e).hom.app X x = e.hom.app (S.obj X) x := rfl

@[irreducible, no_expose] private noncomputable def zeroWhiskerLeft
    {B D E : Type*} [Category* B] [Category* D] [Category* E]
    (S : B ⥤ D) {F G : D ⥤ E} (α : F ⟶ G) : S ⋙ F ⟶ S ⋙ G :=
  Functor.whiskerLeft S α

private lemma zeroWhiskerLeft_app
    {B D E : Type*} [Category* B] [Category* D] [Category* E]
    (S : B ⥤ D) {F G : D ⥤ E} (α : F ⟶ G) (X : B) :
    (zeroWhiskerLeft S α).app X = α.app (S.obj X) := by
  unfold zeroWhiskerLeft
  rfl

@[irreducible, no_expose] private noncomputable def zeroWhiskerLeftAssoc
    {B D E Z : Type*} [Category* B] [Category* D] [Category* E] [Category* Z]
    (S : B ⥤ D) {F : D ⥤ E} {G : E ⥤ Z} {T : D ⥤ Z}
    (α : F ⋙ G ⟶ T) : (S ⋙ F) ⋙ G ⟶ S ⋙ T :=
  zeroWhiskerLeft S α

private lemma zeroWhiskerLeftAssoc_app
    {B D E Z : Type*} [Category* B] [Category* D] [Category* E] [Category* Z]
    (S : B ⥤ D) {F : D ⥤ E} {G : E ⥤ Z} {T : D ⥤ Z}
    (α : F ⋙ G ⟶ T) (X : B) :
    (zeroWhiskerLeftAssoc S α).app X = α.app (S.obj X) := by
  unfold zeroWhiskerLeftAssoc
  exact zeroWhiskerLeft_app S α X

@[irreducible, no_expose] private noncomputable def zeroWhiskerLeftAssocIso
    {B D E Z V : Type*} [Category* B] [Category* D] [Category* E] [Category* Z] [Category* V]
    (S : B ⥤ D) (F : D ⥤ E) (G : E ⥤ Z) (H : Z ⥤ V) {T : D ⥤ V}
    (e : (F ⋙ G) ⋙ H ≅ T) : ((S ⋙ F) ⋙ G) ⋙ H ≅ S ⋙ T :=
  Functor.isoWhiskerLeft S e

private lemma zeroWhiskerLeftAssocIso_apply
    {B D E Z : Type*} [Category* B] [Category* D] [Category* E] [Category* Z]
    (S : B ⥤ D) (F : D ⥤ E) (G : E ⥤ Z) (H : Z ⥤ AddCommGrpCat.{u})
    {T : D ⥤ AddCommGrpCat.{u}} (e : (F ⋙ G) ⋙ H ≅ T) (X : B)
    (x : H.obj (G.obj (F.obj (S.obj X)))) :
    (zeroWhiskerLeftAssocIso S F G H e).hom.app X x = e.hom.app (S.obj X) x := by
  unfold zeroWhiskerLeftAssocIso
  exact zeroWhiskeredIso_apply S e X x

section HomZeroRepresentatives

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- Ordinary sections of the fixed representative Hom complex.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomSectionComplex
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :=
  ((Functor.uncurry.obj (homComplexFunctor.{c, v, max c v u, max c v u} (R := A)) ⋙
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj
      (op L, (coefficientHomResolution.{u, c, v} J A).obj M))

/-- A zero cycle's actual class in the global derived Hom, via the universal derived unit.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomZeroClass
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :=
  (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).map
    (coefficientSiteSectionsComparison.{u, c, v} J A
      (homComplex.{c, v, max c v u, max c v u} (R := A) L
          ((coefficientHomResolution.{u, c, v} J A).obj M)) ≫
      (coefficientGlobalSections.{u, c, v} J A).map
        (coefficientHomResolutionIso.{u, c, v, w} J A L M).inv)
    ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).inv.app _
      (((coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0) z))

/-- Evaluate a zero cycle on a local section using the actual product projection.
Source: Stacks 08JA, 0A8X (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomZeroEvaluation
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    (((coefficientHomResolution.{u, c, v} J A).obj M).X p).val.obj U :=
  let N := ((coefficientHomResolution.{u, c, v} J A).obj M).X p
  let h := SheafOfModules.homObj (R := A) (L.X p) N
  let s := (coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z ≫
    coefficientHomComponent.{u, c, v} J A L
      ((coefficientHomResolution.{u, c, v} J A).obj M) 0 p p (add_zero p)
  ((SheafOfModules.homObjSectionsEquiv (R := A) (L.X p) N)
    (h.unitHomEquiv s)).val.app U y

private theorem zeroGrothendieck : IsGrothendieckAbelian.{max c v u}
    (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J A).1

private lemma zeroGlobalComplexIso_f
    (L N : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (CategoryTheory.globalComplexIso.{c, v, u} A (op L, N)).hom.f 0 =
      (CategoryTheory.rhomNormalizedHomGlobalCochains.{c, v, u} A L N 0).toAddCommGrpIso.hom :=
  rfl

attribute [local irreducible] CategoryTheory.globalComplexIso

set_option backward.isDefEq.respectTransparency false in
private lemma zeroGlobalEvalApi
    (L N : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (s : ((CategoryTheory.globalBifunctor.{c, v, u} A).obj (op L, N)).X 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    (((CategoryTheory.globalComplexIso.{c, v, u} A (op L, N)).hom.f 0 s).v p p
        (add_zero p)).val.app U y =
      ((SheafOfModules.homObjSectionsEquiv (R := A) (L.X p) (N.X p))
        ((SheafOfModules.homObj (R := A) (L.X p) (N.X p)).unitHomEquiv
          (s ≫ coefficientHomComponent.{u, c, v} J A L N 0 p p (add_zero p)))).val.app U y := by
  have he := congrArg (fun a : CochainComplex.HomComplex.Cochain L N 0 ↦
      (a.v p p (add_zero p)).val.app U y)
    (ConcreteCategory.congr_hom (zeroGlobalComplexIso_f.{u, c, v} J A L N) s)
  have hp := congrArg (fun f : L.X p ⟶ N.X p ↦ f.val.app U y)
    (CategoryTheory.rhomNormalizedHomGlobalCochains_v.{c, v, u} A L N 0 s p p (add_zero p))
  exact he.trans hp

@[no_expose] private noncomputable def zeroGlobalComplexIso
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    coefficientHomSectionComplex.{u, c, v} J A L M ≅
      CochainComplex.HomComplex L ((coefficientHomResolution.{u, c, v} J A).obj M) :=
  CategoryTheory.globalComplexIso.{c, v, u} A
    (op L, (coefficientHomResolution.{u, c, v} J A).obj M)

set_option backward.isDefEq.respectTransparency false in
private lemma zeroGlobalComplexIso_v
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    (((zeroGlobalComplexIso.{u, c, v} J A L M).hom.f 0
      ((coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z)).v p p
        (add_zero p)).val.app U y = coefficientHomZeroEvaluation J A L M z p U y := by
  exact zeroGlobalEvalApi.{u, c, v} J A L
    ((coefficientHomResolution.{u, c, v} J A).obj M) _ p U y

@[no_expose] private noncomputable def zeroCycleCocycle
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0 ≅
      AddCommGrpCat.of (CochainComplex.HomComplex.Cocycle L
        ((coefficientHomResolution.{u, c, v} J A).obj M) 0) :=
  HomologicalComplex.cyclesMapIso (zeroGlobalComplexIso.{u, c, v} J A L M) 0 ≪≫
    (CochainComplex.HomComplex.leftHomologyData L
      ((coefficientHomResolution.{u, c, v} J A).obj M) 0).cyclesIso

private lemma zeroCycleCocycle_val
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :
    (zeroCycleCocycle.{u, c, v} J A L M |>.hom z).val =
      (zeroGlobalComplexIso.{u, c, v} J A L M).hom.f 0
        ((coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z) := by
  let h := CochainComplex.HomComplex.leftHomologyData L
    ((coefficientHomResolution.{u, c, v} J A).obj M) 0
  exact (ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i
    (HomologicalComplex.cyclesMap (zeroGlobalComplexIso.{u, c, v} J A L M).hom 0 z)).trans
      (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
        (zeroGlobalComplexIso.{u, c, v} J A L M).hom 0) z)

attribute [local irreducible] zeroCycleCocycle

private lemma zeroCycleCocycle_homOf
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (f : L ⟶ (coefficientHomResolution.{u, c, v} J A).obj M)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (hz : ∀ (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U),
      coefficientHomZeroEvaluation.{u, c, v} J A L M z p U y = (f.f p).val.app U y) :
    (zeroCycleCocycle.{u, c, v} J A L M |>.hom z).homOf = f := by
  ext p U y
  change (((zeroCycleCocycle.{u, c, v} J A L M).hom z).val.v p p
    (add_zero p)).val.app U y = _
  rw [zeroCycleCocycle_val]
  exact (zeroGlobalComplexIso_v.{u, c, v} J A L M z p U y).trans (hz p U y)

private lemma zeroGlobalComplexIso_naturality
    {X Y : (CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)ᵒᵖ ×
      CochainComplex (SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ}
    (f : X ⟶ Y) :
    (CategoryTheory.globalBifunctor.{c, v, u} A).map f ≫
        (CategoryTheory.globalComplexIso.{c, v, u} A Y).hom =
      (CategoryTheory.globalComplexIso.{c, v, u} A X).hom ≫
        CategoryTheory.externalMap f.1.unop f.2 := by
  simpa only [Quiver.Hom.op_unop, Prod.mk.eta] using
    CategoryTheory.globalComplexIso_naturality.{c, v, u} A f.1.unop f.2

set_option backward.isDefEq.respectTransparency false in
@[no_expose] private noncomputable def zeroGlobalHomologyNatIso :
    CategoryTheory.globalBifunctor.{c, v, u} A ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0 ≅
      (HomotopyCategory.quotient
        (SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))
          (.up ℤ)).op.prod (HomotopyCategory.quotient _ (.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda :=
  zeroGlobalHomologyNatIsoOfComplexIso
    (CategoryTheory.globalBifunctor.{c, v, u} A)
    (CategoryTheory.globalComplexIso.{c, v, u} A)
    (fun {_X _Y} f ↦ zeroGlobalComplexIso_naturality.{u, c, v} J A f)

private lemma zeroGlobalHomologyNatIso_hom_app (X :
    (CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)ᵒᵖ ×
      CochainComplex (SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (zeroGlobalHomologyNatIso.{u, c, v} J A).hom.app X =
      HomologicalComplex.homologyMap
        (CategoryTheory.globalComplexIso.{c, v, u} A X).hom 0 ≫
          (CategoryTheory.externalHomologyIso X.1.unop X.2).hom :=
  zeroGlobalHomologyNatIsoOfComplexIso_hom_app _ _
    (fun {_X _Y} f ↦ zeroGlobalComplexIso_naturality.{u, c, v} J A f) X

attribute [local irreducible] zeroGlobalHomologyNatIso

private lemma zeroGlobalHomologyNatIso_π
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :
    (zeroGlobalHomologyNatIso.{u, c, v} J A).hom.app
      (op L, (coefficientHomResolution.{u, c, v} J A).obj M)
      ((coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0 z) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((zeroCycleCocycle.{u, c, v} J A L M).hom z).homOf := by
  rw [zeroGlobalHomologyNatIso_hom_app]
  unfold zeroCycleCocycle
  exact zeroHomologyIsoOnCycle L ((coefficientHomResolution.{u, c, v} J A).obj M)
    _ (zeroGlobalComplexIso.{u, c, v} J A L M) z

set_option hygiene false in
local notation "Mod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
set_option hygiene false in
local notation "K" => CochainComplex Mod ℤ
set_option hygiene false in
local notation "Der" => DerivedCategory Mod

@[no_expose] private noncomputable def zeroHomLocalizationNatIso :
    DerivedCategory.Q.op.prod DerivedCategory.Q ⋙
        derivedInternalHomOfUniverses.{c, v, u, w} J A ≅
      (𝟭 Kᵒᵖ).prod (coefficientHomResolution.{u, c, v} J A) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := A)) ⋙ DerivedCategory.Q := by
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  exact Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max c v u} _) ⋙
      Functor.uncurry.obj (homComplexFunctor.{c, v, max c v u, max c v u} (R := A)) ⋙
        DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{c, v, u, w} J A _
      (CochainComplex.toKInjectiveResolution.{max c v u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)

private lemma zeroHomLocalizationNatIso_app (L M : K) :
    (zeroHomLocalizationNatIso.{u, c, v, w} J A).app (op L, M) =
      coefficientHomResolutionIso.{u, c, v, w} J A L M := rfl

attribute [local irreducible] zeroHomLocalizationNatIso

@[no_expose] private noncomputable def zeroSectionsComparisonNatTrans :
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ) ⋙
        (@DerivedCategory.Q AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _)) ⟶
      DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A := by
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  exact zeroRightDerivedUnitNatTrans (coefficientOrdinarySections.{u, c, v} J A)

private lemma zeroSectionsComparisonNatTrans_app (L : K) :
    (zeroSectionsComparisonNatTrans.{u, c, v, w} J A).app L =
      coefficientSiteSectionsComparison.{u, c, v, w} J A L := rfl

@[no_expose] private noncomputable def zeroSectionsHomologyComparisonNatTrans :
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0 ⟶
      DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A ⋙
        (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0) :=
  (Functor.isoWhiskerLeft
    ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ))
    (@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0)).inv ≫
    Functor.whiskerRight (zeroSectionsComparisonNatTrans.{u, c, v, w} J A)
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
        (HasDerivedCategory.standard _) 0)

private lemma zeroSectionsHomologyComparisonNatTrans_apply (L : K)
    (x : (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj
      L).homology 0) :
    (zeroSectionsHomologyComparisonNatTrans.{u, c, v, w} J A).app L x =
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
        (HasDerivedCategory.standard _) 0).map
          ((zeroSectionsComparisonNatTrans.{u, c, v, w} J A).app L)
        ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0).inv.app
            (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj L)
          x) := rfl

private lemma zeroSectionsHomologyComparisonNatTrans_site_apply (L : K)
    (x : (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj
      L).homology 0) :
    (zeroSectionsHomologyComparisonNatTrans.{u, c, v, w} J A).app L x =
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
        (HasDerivedCategory.standard _) 0).map
          (coefficientSiteSectionsComparison.{u, c, v, w} J A L)
        ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0).inv.app
            (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj L)
          x) := by
  let H := @DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
    (HasDerivedCategory.standard _) 0
  have h := ConcreteCategory.congr_hom
    (H.congr_map (zeroSectionsComparisonNatTrans_app.{u, c, v, w} J A L))
    ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).inv.app
        (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)).obj L) x)
  exact (zeroSectionsHomologyComparisonNatTrans_apply.{u, c, v, w} J A L x).trans h

set_option backward.isDefEq.respectTransparency false in
private lemma zeroSectionsHomologyComparison_isIso (L : K) [L.IsKInjective] :
    IsIso ((zeroSectionsHomologyComparisonNatTrans.{u, c, v, w} J A).app L) := by
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let Γ := coefficientOrdinarySections.{u, c, v} J A
  let G := Γ.mapHomologicalComplex (.up ℤ)
  have hα : IsIso (coefficientSiteSectionsComparison.{u, c, v, w} J A L) :=
    by
      change IsIso (Γ.rightDerivedFunctorUnitQ L)
      rw [Γ.rightDerivedFunctorUnitQ_eq]
      infer_instance
  dsimp only [zeroSectionsHomologyComparisonNatTrans, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [zeroSectionsComparisonNatTrans_app]
  infer_instance

attribute [local irreducible] zeroSectionsHomologyComparisonNatTrans
  DerivedCategory.homologyFunctor
  coefficientGlobalSections coefficientSiteSectionsComparison

@[implicit_reducible, no_expose] private noncomputable def zeroOrdinaryBifunctor (I : K ⥤ K) :
    Kᵒᵖ × K ⥤ AddCommGrpCat.{max c v u} :=
  ((((𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A))) ⋙
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0)

@[implicit_reducible, no_expose] private noncomputable def zeroHomotopyBifunctor
    (I : K ⥤ K) : Kᵒᵖ × K ⥤ AddCommGrpCat.{max c v u} :=
  (𝟭 Kᵒᵖ).prod I ⋙
    (HomotopyCategory.quotient Mod (.up ℤ)).op.prod
      (HomotopyCategory.quotient Mod (.up ℤ)) ⋙ Functor.uncurry.obj preadditiveCoyoneda

@[no_expose] private noncomputable def zeroOrdinaryBifunctorIso (I : K ⥤ K) :
    zeroOrdinaryBifunctor.{u, c, v} J A I ≅ zeroHomotopyBifunctor.{u, c, v} J A I :=
  zeroWhiskerLeftAssocIso ((𝟭 Kᵒᵖ).prod I)
    (Functor.uncurry.obj (homComplexFunctor (R := A)))
    ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0)
    (zeroGlobalHomologyNatIso.{u, c, v} J A)

private lemma zeroOrdinaryBifunctorIso_apply (I : K ⥤ K) (X : Kᵒᵖ × K)
    (x : (zeroOrdinaryBifunctor.{u, c, v} J A I).obj X) :
    (zeroOrdinaryBifunctorIso.{u, c, v} J A I).hom.app X x =
      (zeroGlobalHomologyNatIso.{u, c, v} J A).hom.app (X.1, I.obj X.2) x :=
  zeroWhiskerLeftAssocIso_apply ((𝟭 Kᵒᵖ).prod I)
    (Functor.uncurry.obj (homComplexFunctor (R := A)))
    ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0)
    (zeroGlobalHomologyNatIso.{u, c, v} J A) X x

@[no_expose] private noncomputable def zeroHomSectionsComparisonNatTrans (I : K ⥤ K) :
    zeroOrdinaryBifunctor.{u, c, v} J A I ⟶
      ((𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A))) ⋙
        DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A ⋙
          (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
            (HasDerivedCategory.standard _) 0) :=
  zeroWhiskerLeftAssoc
    ((𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A)))
    (zeroSectionsHomologyComparisonNatTrans.{u, c, v, w} J A)

private lemma zeroHomSectionsComparisonNatTrans_app (I : K ⥤ K) (L M : K) :
    (zeroHomSectionsComparisonNatTrans.{u, c, v, w} J A I).app (op L, M) =
      (zeroSectionsHomologyComparisonNatTrans.{u, c, v, w} J A).app
        (homComplex (R := A) L (I.obj M)) :=
  zeroWhiskerLeftAssoc_app _ _ (op L, M)

private lemma zeroPreadditiveHomMapIsIso
    {D : Type*} [Category* D] [Preadditive D] {X Y Z : D} (f : Y ⟶ X)
    (h : Function.Bijective (fun g : X ⟶ Z ↦ f ≫ g)) :
    IsIso ((Functor.uncurry.obj (preadditiveCoyoneda : Dᵒᵖ ⥤ D ⥤ _)).map
      (Prod.mkHom f.op (𝟙 Z))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun g : X ⟶ Z ↦ (f ≫ g) ≫ 𝟙 Z)
  simpa only [Category.comp_id] using h

private lemma zeroPreadditiveHomBifunctorMapIsIso
    {D E : Type*} [Category* D] [Category* E] [Preadditive E]
    (q : D ⥤ E) (I : D ⥤ D) {P L : D} (t : P ⟶ L) (M : D)
    (ht : Function.Bijective (fun g : q.obj L ⟶ q.obj (I.obj M) ↦ q.map t ≫ g)) :
    IsIso ((((𝟭 Dᵒᵖ).prod I ⋙ q.op.prod q ⋙
      Functor.uncurry.obj (preadditiveCoyoneda (C := E))).map
        (Prod.mkHom t.op (𝟙 M)))) := by
  let f : (op L, M) ⟶ (op P, M) := (t.op, 𝟙 M)
  let HK := Functor.uncurry.obj (preadditiveCoyoneda (C := E))
  have hp : (q.op.prod q).map (((𝟭 Dᵒᵖ).prod I).map f) =
      Prod.mkHom (q.map t).op (𝟙 (q.obj (I.obj M))) := by
    apply Prod.ext
    · rfl
    · exact (congrArg (fun a : I.obj M ⟶ I.obj M ↦ q.map a)
        (I.map_id M)).trans (q.map_id (I.obj M))
  have hm : (((𝟭 Dᵒᵖ).prod I ⋙ q.op.prod q ⋙ HK).map f) =
      HK.map (Prod.mkHom (q.map t).op (𝟙 (q.obj (I.obj M)))) :=
    congrArg (fun a : (op (q.obj L), q.obj (I.obj M)) ⟶
      (op (q.obj P), q.obj (I.obj M)) ↦ HK.map a) hp
  change IsIso ((((𝟭 Dᵒᵖ).prod I ⋙ q.op.prod q ⋙ HK).map f))
  rw [hm]
  exact zeroPreadditiveHomMapIsIso (q.map t) ht

private lemma zeroIsIso_app_of_isIso_maps
    {D E : Type*} [Category* D] [Category* E] {F G : D ⥤ E}
    (α : F ⟶ G) {X Y : D} (f : X ⟶ Y)
    [IsIso (F.map f)] [IsIso (G.map f)] [IsIso (α.app Y)] : IsIso (α.app X) := by
  have : IsIso (α.app X ≫ G.map f) := by
    rw [← α.naturality f]
    infer_instance
  exact IsIso.of_isIso_comp_right (α.app X) (G.map f)

attribute [local irreducible] zeroOrdinaryBifunctorIso zeroHomSectionsComparisonNatTrans

set_option backward.isDefEq.respectTransparency false in
private theorem zeroHomSectionsComparison_isIso (I : K ⥤ K)
    (hI : ∀ M, (I.obj M).IsKInjective) (L M : K) :
    IsIso ((zeroHomSectionsComparisonNatTrans.{u, c, v, w} J A I).app (op L, M)) := by
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let q := HomotopyCategory.quotient Mod (.up ℤ)
  let Γ := coefficientOrdinarySections.{u, c, v} J A
  let G := Γ.mapHomologicalComplex (.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} 0
  let F := (𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A))
  let := hI M
  obtain ⟨P, t, hP, _, ht, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients L
  let := ht
  let f : (op L, M) ⟶ (op P, M) := (t.op, 𝟙 M)
  have hflat : (homComplex (R := A) P (I.obj M)).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, c, v}
      P (I.obj M) hP
  have hright :
      IsIso ((F ⋙ DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A ⋙ Hd).map f) := by
    have hf : QuasiIso (F.map f) := by
      change QuasiIso (((homComplexFunctor (R := A)).map t.op).app (I.obj M) ≫
        ((homComplexFunctor (R := A)).obj (op P)).map (I.map (𝟙 M)))
      rw [I.map_id]
      exact quasiIso_homComplex_mapOfUniverses.{c, v, u} (𝟙 (I.obj M)) t
    let := hf
    change IsIso (Hd.map ((coefficientGlobalSections.{u, c, v} J A).map
      (DerivedCategory.Q.map (F.map f))))
    infer_instance
  have hleft' : IsIso ((zeroHomotopyBifunctor.{u, c, v} J A I).map f) :=
    zeroPreadditiveHomBifunctorMapIsIso q I t M
      (CochainComplex.IsKInjective.precomp_bijective_of_quasiIso t (I.obj M))
  have hleft : IsIso ((zeroOrdinaryBifunctor.{u, c, v} J A I).map f) :=
    (NatIso.isIso_map_iff (zeroOrdinaryBifunctorIso.{u, c, v} J A I) f).mpr hleft'
  let := hleft
  let := hright
  let : (homComplex (R := A) P (I.obj M)).IsKInjective := hflat
  have hγP : IsIso ((zeroHomSectionsComparisonNatTrans.{u, c, v, w} J A I).app
      (op P, M)) := by
    rw [zeroHomSectionsComparisonNatTrans_app]
    exact @zeroSectionsHomologyComparison_isIso.{u, c, v, w} C _ J _ _ A _
      (homComplex (R := A) P (I.obj M)) hflat
  exact @zeroIsIso_app_of_isIso_maps _ _ _ _ _ _
    (zeroHomSectionsComparisonNatTrans.{u, c, v, w} J A I) _ _
    f hleft hright hγP

private lemma zeroCycleCocycle_evaluation (L M : K)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    coefficientHomZeroEvaluation.{u, c, v} J A L M z p U y =
      ((((zeroCycleCocycle.{u, c, v} J A L M).hom z).homOf).f p).val.app U y := by
  change coefficientHomZeroEvaluation.{u, c, v} J A L M z p U y =
    (((zeroCycleCocycle.{u, c, v} J A L M).hom z).val.v p p (add_zero p)).val.app U y
  rw [zeroCycleCocycle_val]
  exact (zeroGlobalComplexIso_v.{u, c, v} J A L M z p U y).symm

attribute [local irreducible] coefficientHomZeroEvaluation derivedInternalHomOfUniverses

set_option backward.isDefEq.respectTransparency true in
/-- The H⁰ RHom identification is uniquely fixed by taking a cycle to its chain map.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class).
Proof: on a K-flat L and the fixed K-injective replacement I(M), sections of Hom(L,I(M))
have zero cycles the chain maps and boundaries the null-homotopic maps. The universal
sections comparison and the actual Hom localization factorization give the displayed
class. Send it to Q(f) followed by the inverse of Q(M to I(M)). K-injectivity gives an
additive bijection. K-flat resolutions and localization naturality extend it uniquely to
all derived inputs, independently of the chosen resolution. Every cycle determines one
chain map by the product projections, and every derived morphism has such a representative;
these facts also prove uniqueness. This is the recorded rhom-global-sections comparison
with its representative normalization made explicit, not a second cohomology notion. -/
theorem coefficientHomZeroEquiv_exists :
    ∃! e : ∀ P Q : DerivedCategory (SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)),
      ((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).obj
        ((coefficientGlobalSections.{u, c, v} J A).obj
          ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op P, Q)))) ≃+ (P ⟶ Q),
      (∀ (P Q P' Q' : DerivedCategory (SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))
        (f : P' ⟶ P) (g : Q ⟶ Q')
        (x : (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0).obj
            ((coefficientGlobalSections.{u, c, v} J A).obj
              ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op P, Q)))),
        e P' Q'
          ((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
            (HasDerivedCategory.standard _) 0).map
              ((coefficientGlobalSections.{u, c, v} J A).map
                ((derivedInternalHomOfUniverses.{c, v, u, w} J A).map
                  (Prod.mkHom f.op g))) x) = f ≫ e P Q x ≫ g) ∧
      (∀ (L M : CochainComplex (SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
          (J := J) (R := A) L →
        ∀ (f : L ⟶ (coefficientHomResolution.{u, c, v} J A).obj M)
          (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0),
          (∀ (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U),
            coefficientHomZeroEvaluation.{u, c, v} J A L M z p U y = (f.f p).val.app U y) →
          e _ _ (coefficientHomZeroClass.{u, c, v, w} J A L M z) =
            DerivedCategory.Q.map f ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M) := by
  classical
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  let I := coefficientHomResolution.{u, c, v} J A
  let η := CochainComplex.toKInjectiveResolution.{max c v u} Mod
  have hI (M : CochainComplex Mod ℤ) : (I.obj M).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} Mod M
  have hη (M : CochainComplex Mod ℤ) : QuasiIso (η.app M) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} Mod M).2
  let q := HomotopyCategory.quotient Mod (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := Mod)
  let σ := DerivedCategory.quotientCompQhIso Mod
  let H := Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory Mod))
  let HK := Functor.uncurry.obj
    (preadditiveCoyoneda (C := HomotopyCategory Mod (ComplexShape.up ℤ)))
  let U := AddCommGrpCat.uliftFunctor.{w, max c v u}
  let V := AddCommGrpCat.uliftFunctor.{max c v u, w}
  let B := q.op.prod (I ⋙ q) ⋙ HK ⋙ U
  let T := Q.op.prod Q ⋙ H ⋙ V
  let b : B ≅ T := zeroDerivedHomotopyIso I η hI hη
  let Γ := coefficientOrdinarySections.{u, c, v} J A
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} 0
  let HZ := coefficientGlobalSections.{u, c, v} J A ⋙ Hd
  let Rep := (𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A))
  let γ := zeroHomSectionsComparisonNatTrans.{u, c, v, w} J A I
  have hγ : IsIso γ := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨L, M⟩
    exact zeroHomSectionsComparison_isIso.{u, c, v, w} J A I hI L.unop M
  let c : Q.op.prod Q ⋙ derivedInternalHomOfUniverses.{c, v, u, w} J A ≅
      Rep ⋙ Q := zeroHomLocalizationNatIso.{u, c, v, w} J A
  let ac := zeroAssociativeLocalizationIso (Q.op.prod Q)
    (derivedInternalHomOfUniverses.{c, v, u, w} J A) Rep Q
    (coefficientGlobalSections.{u, c, v} J A) Hd U c
  let gd := Functor.isoWhiskerRight (asIso γ) U
  let od := Functor.isoWhiskerRight (zeroOrdinaryBifunctorIso.{u, c, v} J A I) U
  let F := derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙ HZ ⋙ U
  let G := H ⋙ V
  let d : Q.op.prod Q ⋙ F ≅ Q.op.prod Q ⋙ G :=
    ac ≪≫ gd.symm ≪≫ od ≪≫ b
  let W := (HomologicalComplex.quasiIso Mod (.up ℤ)).op.prod
    (HomologicalComplex.quasiIso Mod (.up ℤ))
  let ff := Localization.fullyFaithfulWhiskeringLeft (Q.op.prod Q) W AddCommGrpCat.{max c v u w}
  let z : F ≅ G := ff.preimageIso d
  let E (P : Derᵒᵖ × Der) :
      HZ.obj ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj P) ≃+
        (P.1.unop ⟶ P.2) := zeroUnliftHomEquiv (D := Der)
          (derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙ HZ) z P
  have hnat (P P' : Derᵒᵖ × Der) (f : P ⟶ P')
      (x : HZ.obj ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj P)) :
      E P' (HZ.map ((derivedInternalHomOfUniverses.{c, v, u, w} J A).map f) x) =
        f.1.unop ≫ E P x ≫ f.2 := by
    exact zeroUnliftHomEquiv_naturality (D := Der)
      (derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙ HZ) z P P' f x
  have hzapp (X : Kᵒᵖ × K) :
      z.hom.app ((Q.op.prod Q).obj X) = d.hom.app X := by
    exact congrArg (fun n ↦ n.app X) (ff.map_preimage d.hom)
  have hdrel : gd.hom ≫ ac.inv ≫ d.hom = od.hom ≫ b.hom := by
    simp only [d, Iso.trans_hom, Iso.symm_hom,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have hclass (L M : K)
      (v : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :
      (gd.hom ≫ ac.inv).app (op L, M)
        (ULift.up ((coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0 v)) =
        ULift.up (coefficientHomZeroClass.{u, c, v, w} J A L M v) := by
    let x := (coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0 v
    let KLM := homComplex (R := A) L (I.obj M)
    let a := (@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).inv.app
        ((Γ.mapHomologicalComplex (.up ℤ)).obj KLM) x
    have hγ' := ConcreteCategory.congr_hom
      (zeroHomSectionsComparisonNatTrans_app.{u, c, v, w} J A I L M) x
    have hβ := zeroSectionsHomologyComparisonNatTrans_site_apply.{u, c, v, w} J A KLM x
    have heq := hγ'.trans hβ
    have hcomp := ConcreteCategory.congr_hom
      (Hd.map_comp (coefficientSiteSectionsComparison.{u, c, v, w} J A KLM)
        ((coefficientGlobalSections.{u, c, v} J A).map (c.inv.app (op L, M)))) a
    change Hd.map (coefficientSiteSectionsComparison.{u, c, v, w} J A KLM ≫
        (coefficientGlobalSections.{u, c, v} J A).map (c.inv.app (op L, M))) a =
      HZ.map (c.inv.app (op L, M))
        (Hd.map (coefficientSiteSectionsComparison.{u, c, v, w} J A KLM) a) at hcomp
    have ha := ConcreteCategory.congr_hom
      (zeroAssociativeLocalizationIso_inv_app (Q.op.prod Q)
        (derivedInternalHomOfUniverses.{c, v, u, w} J A) Rep Q
        (coefficientGlobalSections.{u, c, v} J A) Hd U c (op L, M))
      (ULift.up (γ.app (op L, M) x))
    change ac.inv.app (op L, M) (ULift.up (γ.app (op L, M) x)) =
      ULift.up (HZ.map (c.inv.app (op L, M)) (γ.app (op L, M) x)) at ha
    change ac.inv.app (op L, M) (ULift.up (γ.app (op L, M) x)) =
      ULift.up (coefficientHomZeroClass.{u, c, v, w} J A L M v)
    have hc : c.inv.app (op L, M) =
        (coefficientHomResolutionIso.{u, c, v, w} J A L M).inv :=
      congrArg Iso.inv (zeroHomLocalizationNatIso_app.{u, c, v, w} J A L M)
    exact ha.trans (congrArg ULift.up
      (((congrArg (HZ.map (c.inv.app (op L, M))) heq).trans hcomp.symm).trans
        (congrArg (fun f ↦ Hd.map (coefficientSiteSectionsComparison.{u, c, v, w} J A KLM ≫
          (coefficientGlobalSections.{u, c, v} J A).map f) a) hc)))
  have hnorm (L M : K)
      (hL : CochainComplex.IsKFlatIndependentCoefficients (R := A) L)
      (f : L ⟶ I.obj M) (v : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
      (hv : ∀ (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U),
        coefficientHomZeroEvaluation.{u, c, v} J A L M v p U y = (f.f p).val.app U y) :
      E (op (Q.obj L), Q.obj M) (coefficientHomZeroClass.{u, c, v, w} J A L M v) =
        Q.map f ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M := by
    let x := (coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0 v
    have hc := hclass L M v
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hdrel (op L, M)) (ULift.up x)
    change (d.hom.app (op L, M) ((gd.hom ≫ ac.inv).app (op L, M) (ULift.up x))) = _ at hh
    have hh' := (congrArg (d.hom.app (op L, M)) hc).symm.trans hh
    have hcanon : ((b.hom.app (op L, M))
        (ULift.up ((zeroOrdinaryBifunctorIso.{u, c, v} J A I).hom.app (op L, M) x))).down =
        Q.map f ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M := by
      rw [zeroOrdinaryBifunctorIso_apply]
      rw [show (zeroGlobalHomologyNatIso.{u, c, v} J A).hom.app
          (op L, (coefficientHomResolution.{u, c, v} J A).obj M) x = q.map f by
        rw [zeroGlobalHomologyNatIso_π, zeroCycleCocycle_homOf.{u, c, v} J A L M f v hv]]
      exact zeroDerivedHomotopyIso_quotient_apply I η hI hη L M f
    rw [zeroUnliftHomEquiv_apply]
    have hz := ConcreteCategory.congr_hom (hzapp (op L, M))
      (ULift.up (coefficientHomZeroClass.{u, c, v, w} J A L M v))
    exact (congrArg ULift.down (hz.trans hh')).trans hcanon
  have hsurj (L M : K)
      (x : HZ.obj ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
        (op (Q.obj L), Q.obj M))) :
      ∃ v, coefficientHomZeroClass.{u, c, v, w} J A L M v = x := by
    exact zeroCycleClasses_surjective.{max c v u, w}
      (X := (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
      (Y := (coefficientHomSectionComplex.{u, c, v} J A L M).homology 0)
      (Z := HZ.obj ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
        (op (Q.obj L), Q.obj M)))
      ((coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0)
      (gd.app (op L, M) ≪≫ (ac.app (op L, M)).symm)
      (coefficientHomZeroClass.{u, c, v, w} J A L M) (hclass L M) x
  refine ⟨fun P Q ↦ E (op P, Q), ⟨?_, ?_⟩, ?_⟩
  · intro P Q P' Q' f g x
    exact hnat (op P, Q) (op P', Q') (f.op, g) x
  · exact hnorm
  · intro e he
    have hbase (L M : K)
        (hL : CochainComplex.IsKFlatIndependentCoefficients (R := A) L)
        (x : HZ.obj ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
          (op (Q.obj L), Q.obj M))) :
        e (Q.obj L) (Q.obj M) x = E (op (Q.obj L), Q.obj M) x := by
      have hx : ∃ v : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0,
          coefficientHomZeroClass.{u, c, v, w} J A L M v = x := hsurj L M x
      obtain ⟨v, hv⟩ := hx
      let f := ((zeroCycleCocycle.{u, c, v} J A L M).hom v).homOf
      have hvc (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
          coefficientHomZeroEvaluation.{u, c, v} J A L M v p U y = (f.f p).val.app U y :=
        zeroCycleCocycle_evaluation.{u, c, v} J A L M v p U y
      exact (congrArg (e (Q.obj L) (Q.obj M)) hv).symm.trans
        ((he.2 L M hL f v hvc).trans
          ((hnorm L M hL f v hvc).symm.trans
            (congrArg (E (op (Q.obj L), Q.obj M)) hv)))
    apply zeroNaturalFamilies_eq (D := Der) («K» := K)
      (derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙ HZ) Q
      (CochainComplex.IsKFlatIndependentCoefficients (R := A))
      e (fun P Q ↦ E (op P, Q)) he.1
      (fun P Q P' Q' f g x ↦ hnat (op P, Q) (op P', Q') (Prod.mkHom f.op g) x)
    · intro P
      let L₀ := Q.objPreimage P
      obtain ⟨L, t, hL, _, ht, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients L₀
      let := ht
      exact ⟨L, hL, ⟨asIso (Q.map t) ≪≫ Q.objObjPreimageIso P⟩⟩
    · intro P
      exact ⟨Q.objPreimage P, ⟨Q.objObjPreimageIso P⟩⟩
    · exact hbase

/-- The uniquely normalized version of the recorded H⁰ RHom equivalence.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomZeroEquiv :=
  (coefficientHomZeroEquiv_exists.{u, c, v, w} J A).choose

end HomZeroRepresentatives

end WeilConjectures
