/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
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
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedDualizableIndependent
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralReductionTwoTermResolution
import WeilConjectures.SixFunctors.IntegralHom.Reduction.ReductionTensorResolutionComparison
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # A dualizable coefficient model for restricted integral reduction

Source: the two-term coefficient resolution in the integral Hom reduction proof,
paragraph 1; Stacks Project, Tags 06YY, 07A4 and 08J7.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe d t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local irreducible] HasDerivedCategory.standard

-- Elaborating the independent coefficient universes needs extra definitional-equality steps.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Restricted reduction is tensor with a dualizable coefficient object.
Source: Stacks 06YY, 07A4, 08J7; integral Hom reduction, paragraph 1.
Proof: take the two-term resolution of the restricted quotient unit. Its two
nonzero terms are units, hence dualizable, and the other terms are zero, hence
dualizable. Bounded termwise duality descends through K-flat localization in the
independent derived universe. The resolution comparison computes restricted
reduction on all complexes. Compose it with the one-K-flat native tensor
comparison and descend this natural isomorphism through localization.
(blueprint: lem-sf-integral-reduction-dualizable-coefficient). -/
theorem integralReduction_dualizable_coefficient (n : ℕ) :
    let R := completedIntegralCommRingSheaf l E Y D hl
    letI : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) :=
      by
      letI := HasDerivedCategory.standard
        (RingedDerivedNative.Modules.{t + 1, t, u}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R)
      with_unfolding_all exact RingedDerivedNative.monoidal.{t + 1, t, u,
        max u (t + 1) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) R
    ∃ N : completedIntegralDerivedCategory l E Y D hl,
      IsDualizable N ∧ Nonempty
        (integralDerivedReduction l E Y D hl n ⋙ scalarReductionDerivedRestriction l E Y n ≅
          tensorRight N) := by
  classical
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let R := completedIntegralCommRingSheaf l E Y D hl
  let : HasSheafify J AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} Y
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} Y
  let : MonoidalCategory (Modules.{t, u} Y R) := RingedDerivedNative.moduleMonoidal J R
  let : SymmetricCategory (Modules.{t, u} Y R) := RingedDerivedNative.moduleSymmetric J R
  let : MonoidalPreadditive (Modules.{t, u} Y R) :=
    RingedDerivedNative.modulePreadditive J R
  let : MonoidalClosed (Modules.{t, u} Y R) := RingedDerivedNative.moduleClosed J R
  let : IsGrothendieckAbelian.{max u (t + 1)} (Modules.{t, u} Y R) :=
    RingedDerivedNative.moduleGrothendieck J R
  let : Abelian.HasFunctorialFlatResolution (Modules.{t, u} Y R) :=
    RingedDerivedNative.moduleFlat J R
  let : MonoidalCategory (completedIntegralDerivedCategory l E Y D hl) :=
    by
      with_unfolding_all exact RingedDerivedNative.monoidal J R
  obtain ⟨Q, hQ, hz, em, e0, ε, hε⟩ :=
    integralReduction_twoTerm_resolution l E Y D hl n
  have hd (i : ℤ) : IsDualizable (Q.X i) := by
    by_cases hm : i = -1
    · subst i
      exact IsDualizable.of_iso em.symm isDualizable_unit
    · by_cases h0 : i = 0
      · subst i
        exact IsDualizable.of_iso e0.symm isDualizable_unit
      · exact CategoryTheory.IsZero.isDualizable (hz i hm h0)
  have : Q.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have : Q.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hdual : IsDualizable (DerivedCategory.Q.obj Q) :=
    DerivedCategory.isDualizable_Q_obj_independent Q (-1) 0 hd
  obtain ⟨r⟩ := (show Nonempty (DerivedCategory.Q ⋙
      integralDerivedReduction l E Y D hl n ⋙ scalarReductionDerivedRestriction l E Y n ≅
      (totalTensor.{t, u} Y R).flip.obj Q ⋙ DerivedCategory.Q) by
        with_unfolding_all exact
          reduction_tensor_resolution_comparison l E Y D hl n Q hQ ε hε)
  let s : (totalTensor.{t, u} Y R).flip.obj Q ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ tensorRight (DerivedCategory.Q.obj Q) :=
    NatIso.ofComponents
      (fun P ↦ RingedDerivedNative.tensorIso J R P Q (Or.inr hQ)) (by
        intro P P' f
        have ht : (coefficientTotalTensor.{u, t + 1, t} J R).map
            (X := (P, Q)) (Y := (P', Q)) (Prod.mkHom f (𝟙 Q)) =
              ((totalTensor.{t, u} Y R).map f).app Q := by
          change ((totalTensor.{t, u} Y R).map f).app Q ≫
            ((totalTensor.{t, u} Y R).obj P').map (𝟙 Q) = _
          rw [CategoryTheory.Functor.map_id, Category.comp_id]
        have hn := RingedDerivedNative.tensorIso_naturality J R P Q P' Q
          (Or.inr hQ) (Or.inr hQ) f (𝟙 Q)
        rw [ht, CategoryTheory.Functor.map_id, tensorHom_id] at hn
        exact hn)
  exact ⟨DerivedCategory.Q.obj Q, hdual,
    ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ))
      (Derived.{t, u} Y R)).preimageIso (r ≪≫ s)⟩⟩

end WeilConjectures.IntegralHom
