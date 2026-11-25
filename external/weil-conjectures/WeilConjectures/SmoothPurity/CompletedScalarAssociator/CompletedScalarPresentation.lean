/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The recorded scalar extension as a normalized presentation

Source: Stacks Tags 06YY and 07A6; blueprint Proof (3).
(blueprint: lem-pur-completed-scalar-presentation-exists).

This bundles existing scalar functors and counits without choosing a new model.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
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
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedScalarAssociator

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)
  (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

section Presentation

open SheafOfModules.SuccessiveDerivedQuotient

attribute [local semireducible] completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  completedOrdinaryScalarComplex

@[instance_reducible] private def scalarSiteDerived (X : AlgebraicGeometry.Scheme.{t}) :
    ∀ R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)},
      HasDerivedCategory.{max (u + 1) (t + 2)}
        (Modules.{t + 1, t, max u (t + 1)}
          (J := AlgebraicGeometry.Scheme.ProEt.topology X) R) :=
  fun R ↦ HasDerivedCategory.standard
    (Modules.{t + 1, t, max u (t + 1)}
      (J := AlgebraicGeometry.Scheme.ProEt.topology X) R)

private def canonicalPresentation :
    letI := scalarSiteDerived.{t, u} X
    letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
    letI := integralCoefficientAbLocallyBijective.{t, u} X
    letI := integralCoefficientAbSheafify.{t, u} X
    Presentation (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (completedCoefficientMap l E F ι X) :=
  { ordinary := completedOrdinaryScalarExtension l E F ι X
    obj_eq := completedOrdinaryScalarExtension_obj l E F ι X
    map_eq := completedOrdinaryScalarExtension_map l E F ι X
    additive := completedOrdinaryScalarExtension_additive l E F ι X
    derived := completedDerivedScalarExtension l E F ι X
    counit :=
      ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec.choose_spec.2.2)
        |>.choose_spec.choose
    universal :=
      ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec.choose_spec.2.2)
        |>.choose_spec.choose_spec.1 }

private theorem canonicalPresentation_ordinary :
    (canonicalPresentation l E X F ι).ordinary =
      completedOrdinaryScalarExtension l E F ι X := rfl

private theorem canonicalPresentation_derived :
    (canonicalPresentation l E X F ι).derived =
      completedDerivedScalarExtension l E F ι X := rfl

private theorem canonicalPresentation_sectionTensor
    (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U) :
    sectionTensor (canonicalPresentation l E X F ι) M U s x =
      completedScalarTensorSection l E F ι X M U s x := rfl

private theorem canonicalPresentation_counit (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (canonicalPresentation l E X F ι).counit.app ((HomotopyCategory.quotient _ _).obj P) =
      completedScalarCounit l E F ι X P := rfl

attribute [local irreducible] completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection

end Presentation
end CompletedScalarAssociator
end WeilConjectures
