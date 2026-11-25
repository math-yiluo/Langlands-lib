/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SmoothPurity.Point.PointSectionsFiniteness
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.Picard.DerivedTensorSecondFactorFunctor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Point sections and finite coefficient reduction

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
`sk-prop-trace-adic/prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (1)
(blueprint: lem-trf-point-sections-finite-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- The standard small model of the point site in the coefficient universe.
Source: Stacks Tag 0982 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSiteSmall (k : Type u) [Field k] :
    EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- Ring sheafification in the standard coefficient universe.
Source: Stacks Tag 00W1 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance (priority := 2000) pointFiniteReductionRingSheafify
    (k : Type u) [Field k] :
    HasSheafify (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _

/-- The constant coefficient ring sheaf at an algebraically closed point.
Source: Stacks Tags 093J and 0982 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionRingSheaf (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))

/-- Exactness of finite coefficient sections at kernels.
Source: Stacks Tags 0982 and 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSectionsLimits (k : Type u) [Field k]
    [IsAlgClosed k] (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    PreservesFiniteLimits (pointFiniteSections k (Padic.coefficientExtensionRing l E n)) := by
  let A := (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
  letI : PreservesFiniteLimits (pointModuleSections k A) :=
    ((@point_proEtale_sections_exact.{u, u + 1, u + 1} k).2 A).1
  exact inferInstanceAs (PreservesFiniteLimits
    (pointModuleSections k _ ⋙ ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n))))

/-- Exactness of finite coefficient sections at cokernels.
Source: Stacks Tags 0982 and 0946 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable instance pointFiniteReductionSectionsColimits (k : Type u) [Field k]
    [IsAlgClosed k] (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    PreservesFiniteColimits (pointFiniteSections k (Padic.coefficientExtensionRing l E n)) := by
  let A := (constantSheaf.{u, u + 1, u + 1, u + 2} (Scheme.ProEt.topology (Spec (.of k)))
    CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
  letI : PreservesFiniteColimits (pointModuleSections k A) :=
    ((@point_proEtale_sections_exact.{u, u + 1, u + 1} k).2 A).2.1
  letI : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n))) := by
    infer_instance
  exact inferInstanceAs (PreservesFiniteColimits
    (pointModuleSections k _ ⋙ ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointConstantSectionMap k (Padic.coefficientExtensionRing l E n))))

/-- Derived sections at the final point with the canonical finite coefficient action.
Source: Stacks Tags 0946 and 0982 (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable def pointFiniteReductionSections (k : Type u) [Field k] [IsAlgClosed k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    DerivedCategory
      (SheafOfModules.{u + 1}
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
          (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E n))) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) :=
  (pointFiniteSections k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory

/-- The existing module-sheaf category on the small pro-etale point site.
Source: Stacks Tag 06YY (blueprint: lem-trf-point-sections-finite-reduction). -/
noncomputable abbrev pointFiniteReductionSheaves (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  SheafOfModules.{u + 1}
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (Spec (.of k))) (pointFiniteReductionRingSheaf k l E n))

variable (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The standard localization in the established point-sheaf Hom universe.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-finite-reduction-sheaf-model). -/
local instance (priority := 30000) pointFiniteReductionDataDerived (n : ℕ) :
    HasDerivedCategory.{u + 2} (pointFiniteReductionSheaves k l E n) :=
  HasDerivedCategory.standard _


variable [IsAlgClosed k]

end WeilConjectures
