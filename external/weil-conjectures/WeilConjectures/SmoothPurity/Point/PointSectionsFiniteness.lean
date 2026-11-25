/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessFiniteTorsion
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessIntegral

/-!
# Finiteness of sections over the algebraically closed coefficient point

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509,
its finite, integral and rational evaluation assertions
(blueprint: lem-weil-point-sections-finiteness).

All assertions are made for every complex representative of the derived object.
Sections are evaluated at the final small pro-etale object. The scalar maps are
actual constant-section maps, and rationalization is termwise scalar extension.
The section-exactness dependency makes these formulas independent of the representative.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- Sections of a finite-torsion constructible complex have bounded finite cohomology;
sections of an integral constructible complex are bounded, finitely generated and derived
complete; their termwise rationalization has bounded finite-dimensional cohomology.

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: lem-weil-point-sections-finiteness).

Proof (the six steps of the node):
1. The finite residue field of O_E gives finitely many representatives modulo the
   uniformizer. Successive expansion in these representatives proves A_(E,n) finite.
   Finite-torsion constructible cohomology comes from a constructible etale sheaf.
   On Spec k the only nonempty locally closed subscheme is itself, and its algebraically
   closed geometric stalk is its sections. The finite-level comparison unit identifies
   these with pro-etale sections. Exact sections commute with cohomology, proving clause 1.
2. The coefficient DVR is Noetherian. Compatible residues modulo uniformizer powers
   have lifts forming a Cauchy sequence in E; completeness and the ultrametric bound
   give a unique limit in O_E. Thus O_E is complete for its uniformizer ideal.
3. Apply exact sections to the integral reduction Roos triangle. Exact countable products
   are sectionwise and their cohomology is coordinatewise. The common interval for all
   reductions bounds section cohomology, with at most one extra top degree. Nilpotent
   torsion in each quotient and the derived-limit completeness theorem give derived
   completeness over O_E, without surjective cohomology transitions.
4. The two-term free resolution [O_E --uniformizer--> O_E] of the residue field,
   completed constant-sheaf reduction and a K-flat representative give the principal
   reduction cone triangle. Exact sections give an injection of H^i/ uniformizer H^i
   into the finite cohomology of the first reduction, so this residue is finitely generated.
5. The Roos description and exact products show that each section cohomology module
   is derived complete. Apply the general derived-complete-module finiteness criterion
   over the complete Noetherian DVR to its finitely generated residue. This gives finite
   generation in every degree, and with step 3 proves clause 2, including completeness.
6. The DVR coefficient theorem identifies E as O_E[1/uniformizer]. Localization is flat,
   so termwise tensor commutes with cohomology. The finite integral generating sets span
   the rational cohomology over E and preserve its finite support, proving clause 3.

Complexes are arbitrary representatives, not bounded termwise or K-flat representatives.
The exact section functor and flat rationalization descend to the derived categories.
ULift changes only coefficient size, leaving the original rings and their actions intact. -/
theorem point_sections_finiteness (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ C : CochainComplex
        (SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology (Spec (.of D.k)))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
                (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))))) ℤ,
      intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
          (DerivedCategory.Q.obj
            (((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapHomologicalComplex
              (.up ℤ)).obj C))) ∧
    (∀ C : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ,
      sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj C) →
        DerivedCategory.pointFgComplete (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
          (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
          (DerivedCategory.Q.obj
            (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)) ∧
        DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars (pointIntegralToField l E)).mapHomologicalComplex
              (.up ℤ)).obj
              (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C)))) := by
  constructor
  · exact point_sections_finiteness_finiteTorsion D l _hl E n hn
  · exact point_sections_finiteness_integral D l _hl E n hn

end WeilConjectures
