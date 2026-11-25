/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Generic normalized scalar comparison

Source: Stacks 03D7, 03EK and 06YY.
(blueprint: lem-sf-system-scalar-package-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe sa sb sw
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SequenceScalarConstruction
variable {C : Type sa} [Category.{sb} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C]

/-- Generic scalar comparison extracted from IntegralComparisonSequenceSystems.
Source: Stacks 03D7, 03EK and 06YY
(blueprint: lem-sf-system-scalar-package-exists).
Proof: Choose the normalized derived counit comparison using the cochain universal property. The
ordinary tensor/restriction adjunction gives its unique unit-normalized adjunction, and the
derived Hom comparison gives the derived adjunction with the required transpose. The unit sends
x to one tensor x by the ordinary unit formula; this constructs the scalar package without
changing its cochain model. -/
theorem scalarPackageExists
    {R S : Sheaf J CommRingCat.{sw}} (φ : R ⟶ S)
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :
    ∃ A : SheafOfModules.SystemScalarModel φ, A.model = D := by
  obtain ⟨ε, hε, hεP⟩ :=
    exists_homotopy_leftDerived_comparison D.E D.T D.ε D.universal
  obtain ⟨_, _, ho⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, ha⟩ := ho D.E D.obj_eq D.map_eq
  obtain ⟨d, hd⟩ := SheafOfModules.sheafRingDerivedHomComparison φ
    D.E D.obj_eq D.map_eq a D.T ε hε
  refine ⟨{ model := D
            ordinaryAdj := a
            unit_normalized := ?_
            adjunction := d
            transpose := adjunction_cochain_transpose D.E _ a D.T D.ε ε
              (fun P ↦ by
                apply (Iso.eq_comp_inv ((DerivedCategory.quotientCompQhIso
                  (ringedSiteModules.{sw}
                    (SheafOfModules.derivedChangeRingIndependentCoefficients J S))).app
                      ((D.E.mapHomologicalComplex (.up ℤ)).obj P))).1
                simpa only [Iso.app_inv, Category.assoc] using hεP P) d hd }, rfl⟩
  intro P U x
  have hu := ha P (D.E.obj P) (eqToHom (D.obj_eq P).symm) U x
  dsimp only [SheafOfModules.systemModelTmul]
  rw [one_smul]
  have ht : ((ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).unit.app
      (P.val.obj U)) x =
        (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x := rfl
  rw [ht]
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
  exact hu

end SequenceScalarConstruction
