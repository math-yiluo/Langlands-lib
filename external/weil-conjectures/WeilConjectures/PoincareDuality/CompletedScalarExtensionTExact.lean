/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import all WeilConjectures.SmoothPurity.PointDerivedSectionsTensor.PointDerivedSectionsTensorDescent
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Completed integral scalar extension is t-exact

Source: main-20261015 blueprint, prop-constructible-truncations, proof, sentence
"Being characterized by the vanishing of cohomology sheaves"; the corrected integral
argument extracted in (blueprint: lem-pod-completed-scalar-extension-texact).

The restricted functor below is the published strict-tower functor. The auxiliary
integer l+1 only fills an unused characteristic argument of its existing interface;
no characteristic condition on the scheme is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory

attribute [local irreducible] HasDerivedCategory.standard

attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{u})

local instance (priority := 6000) instCompletedScalarExtensionTExact1 :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Y

local instance (priority := 6000) instCompletedScalarExtensionTExact2 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Y

private theorem ordinary_exact :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι Y) ∧
      PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι Y) := by
  classical
  let f : Fin (completedScalarRelativeDegree l E L ι) → integralTowerModules.{u, u} l E Y :=
    fun _ ↦ SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted.{u, u} l E Y)
  let : HasBiproduct f :=
    (Abelian.hasFiniteBiproducts (C := integralTowerModules.{u, u} l E Y)).out _ |>.has_biproduct f
  obtain ⟨b⟩ := (finiteFreeCompletedScalarComparison.{u, u} l E L ι Y).1
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _
  have h := SheafOfModules.scalarFiniteExact.{u + 1, u, u + 1, u + 2}
    (completedCoefficientMap.{u, u} l E L ι Y)
    (completedScalarCochainModel.{u, u} l E L ι Y)
    ⟨completedScalarRelativeDegree l E L ι, ⟨
      Sigma.reindex (Equiv.ulift : ULift.{u + 1} (Fin _) ≃ Fin _) f ≪≫
        (biproductIso f).symm ≪≫ b.symm⟩⟩
  have : PreservesLimitsOfSize.{0, 0}
      (completedOrdinaryScalarExtension.{u, u} l E L ι Y) := h.1
  exact ⟨inferInstance, h.2⟩

/-- Ordinary completed-coefficient extension preserves finite limits.
Source: Bhatt--Scholze Lemma 6.8.2(1), finite-free coordinate argument, and the
integral paragraph of prop-constructible-truncations
(blueprint: lem-pod-completed-scalar-extension-texact).
Proof: the finite-free completed coefficient comparison gives an R-basis of S.
After restriction of scalars, M tensor_R S is the finite direct sum of copies of M.
The inverse coordinate formulas commute with restrictions and sheafification.
Consequently kernels are computed coordinatewise. Restriction of scalars detects
exactness on underlying abelian sheaves. Additivity then gives finite limits.
This is step 2 of the node and uses no flatness of M. -/
@[instance] theorem podCompletedOrdinaryScalarExtension_preservesFiniteLimits :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι Y) := by
  exact (ordinary_exact l E L ι Y).1

/-- Ordinary completed-coefficient extension preserves finite colimits.
Source: Bhatt--Scholze Lemma 6.8.2(1), and prop-constructible-truncations
(blueprint: lem-pod-completed-scalar-extension-texact).
Proof: in the same finite-free coordinates as step 2, sectionwise cokernels and
sheafification commute with the finite direct sum. Thus the functor preserves
cokernels; its already recorded additivity gives preservation of finite colimits.
Equivalently ordinary sheafified extension is left adjoint to restriction. -/
@[instance] theorem podCompletedOrdinaryScalarExtension_preservesFiniteColimits :
    PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι Y) := by
  exact (ordinary_exact l E L ι Y).2

private theorem ordinary_derived_comparison :
    ∃ e : completedDerivedScalarExtension.{u, u} l E L ι Y ≅
        (completedOrdinaryScalarExtension.{u, u} l E L ι Y).mapDerivedCategory,
      ∀ P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension.{u, u} l E L ι Y).mapDerivedCategoryFactors.hom.app P =
          completedScalarCounit.{u, u} l E L ι Y P := by
  obtain ⟨c, hc⟩ := scalar_exact_comparison (l := l) (E := E) (L := L) (ι := ι) Y
  exact ⟨c.symm, hc⟩

end WeilConjectures
