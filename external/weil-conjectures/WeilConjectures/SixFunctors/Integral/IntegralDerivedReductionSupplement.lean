/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
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
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction

/-! # Integral derived reduction

Source: Bhatt--Scholze, Section 6.5, Definition 6.5.1 and Lemma 6.5.4;
Stacks Project, Tags 06YS and 06YY (blueprint: def-weil-integral-derived-reduction).

The natural-number index n denotes the positive exponent n+1. The functor is chosen
from the universal derived-change-of-rings pair, not from an arbitrary existence
statement: the universal property determines it up to unique compatible isomorphism.
-/

@[expose] public section

universe d t u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℕ)

/-- Standard localization for completed coefficient module sheaves.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable instance integralReductionSourceHasDerivedCategory :
    HasDerivedCategory (completedIntegralModuleSheaves l E Y D hl) :=
  HasDerivedCategory.standard _

set_option linter.defProp false in
/-- The recorded derived-change-of-rings theorem applied to the actual limit projection.
It includes the fixed sectionwise tensor action, its derived universal property,
exactness, and its counit isomorphism on every K-flat complex.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralReductionExistence :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheaf l E Y D hl)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjection l E Y D hl n)

/-- Ordinary change of rings along the coefficient projection, with objects and morphisms
fixed by the sectionwise tensor product and sheafification.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralReductionChangeOfRings :
    completedIntegralModuleSheaves l E Y D hl ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  (integralReductionExistence l E Y D hl n).choose

/-- Additivity of the chosen ordinary tensor functor, supplied by its defining witness.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
theorem integralReductionChangeOfRingsAdditive :
    (integralReductionChangeOfRings l E Y D hl n).Additive :=
  (integralReductionExistence l E Y D hl n).choose_spec.choose_spec.choose_spec.choose

attribute [local instance] integralReductionChangeOfRingsAdditive

set_option linter.defProp false in
/-- The full derived pair supplied by the general change-of-rings theorem.
Its universal property, exactness and K-flat computation fix the construction.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralReductionDerivedExistence :
    ∃ (LF : completedIntegralDerivedCategory l E Y D hl ⥤
        DerivedCategory
          (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LF.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (completedIntegralModuleSheaves l E Y D hl)
            (ComplexShape.up ℤ)) ∧
        (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
        ∀ (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients
            (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
            (R := completedIntegralCommRingSheaf l E Y D hl) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
  (integralReductionExistence l E Y D hl n).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived reduction modulo the (n+1)-st power of the chosen uniformizer, the exact
left derived functor of change of rings along the completed coefficient projection.
Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.4; Stacks, Tag 06YY
(blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReduction :
    completedIntegralDerivedCategory l E Y D hl ⥤
      DerivedCategory (SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)) :=
  scalarReductionDerivedExtension l E Y n

/-- The universal comparison to termwise change of rings on homotopy complexes.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReductionCounit :
    DerivedCategory.Qh ⋙ integralDerivedReduction l E Y D hl n ⟶
      (integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (integralReductionDerivedExistence l E Y D hl n).choose_spec.choose

/-- The universal left-derived-functor structure; it determines the functor uniquely
up to the unique isomorphism respecting this counit.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction). -/
theorem integralDerivedReductionUniversal :
    (integralDerivedReduction l E Y D hl n).IsLeftDerivedFunctor
      (integralDerivedReductionCounit l E Y D hl n)
      (HomotopyCategory.quasiIso (completedIntegralModuleSheaves l E Y D hl)
        (ComplexShape.up ℤ)) :=
  (integralReductionDerivedExistence l E Y D hl n).choose_spec.choose_spec.1

attribute [local instance] integralDerivedReductionUniversal

/-- The universal counit computes reduction on every K-flat complex.
Source: Stacks, Tag 06YY (blueprint: def-weil-integral-derived-reduction).
Proof: the last conjunct of the defining derived-change-of-rings witness says
that its counit is an isomorphism at the homotopy image of every K-flat complex.
The named reduction and its counit are exactly that witness's two projections;
the completed commutative ring sheaf has the same underlying ring sheaf.
Substituting the given P and its K-flatness gives this assertion. -/
theorem integralDerivedReduction_counit_isIso
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) P) :
    IsIso ((integralDerivedReductionCounit l E Y D hl n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  exact (integralReductionDerivedExistence l E Y D hl n).choose_spec.choose_spec.2.2 P hP

/-- The canonical computation on a K-flat representative is the counit isomorphism.
For a resolution P → G, precompose this with the inverse of the image of P → G.
Comparisons between resolutions are composites through this same derived object,
so are canonical and compatible with a third resolution.
Source: Bhatt--Scholze, Section 6.5; Stacks, Tag 06YY
(blueprint: def-weil-integral-derived-reduction). -/
noncomputable def integralDerivedReductionKFlatIso
    (P : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) P) :
    (integralDerivedReduction l E Y D hl n).obj
        ((DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≅
      (DerivedCategory.Qh).obj
        (((integralReductionChangeOfRings l E Y D hl n).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
  letI : IsIso ((integralDerivedReductionCounit l E Y D hl n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) :=
    integralDerivedReduction_counit_isIso l E Y D hl n P hP
  asIso ((integralDerivedReductionCounit l E Y D hl n).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))

end WeilConjectures
