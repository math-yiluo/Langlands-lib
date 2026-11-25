/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Topology.SkyscraperComplexStalk
import WeilConjectures.Topology.SkyscraperComplexAcyclic

/-!
# Skyscraper complexes and stalks

Source: Stacks Project, Sheaves, Definition Tag 009A (4) and Lemma Tag 009C, applied
termwise (blueprint: lem-pc-skyscraper-complex).
-/

@[expose] public section

universe u_complex

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace SheafOfModules

/-- Stacks, Tags 009A (4) and 009C (blueprint: lem-pc-skyscraper-complex).
The termwise skyscraper of a complex of stalk modules recovers that complex on taking
its stalk at the same point, and carries acyclic complexes to acyclic sheaf complexes.

Proof: for each open U and degree i, skyscraper sections are M^i if x belongs to U and
zero otherwise, with the original differential or the zero map. If M is acyclic, the
sequence of sections in degrees i-1, i, i+1 is therefore exact for every U, and hence
is exact as a sequence of sheaves. This proves acyclicity in every degree, using
`def-pc-cochain-complex-modules` and `def-pc-acyclic-complex-modules`.
For stalk recovery, the neighbourhood diagram at x has the constant value M^i and
identity transition maps in each degree. Its colimit is M^i. These identifications
commute with the differentials and respect the stalk scalar action because section
scalars act through germs. They assemble to the asserted module complex isomorphism,
using `def-pc-cochain-complex-modules`. No separation assumption on x or X is needed. -/
theorem skyscraper_complex (X : RingedSpace.{u_complex}) (x : X)
    (M : CochainComplex (ModuleCat.{u_complex} (X.presheaf.stalk x)) ℤ) :
    Nonempty (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≅ M) ∧
      (M.Acyclic → (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).Acyclic) := by
  exact ⟨skyscraper_complex_stalk_recovery X x M,
    skyscraper_complex_acyclic X x M⟩

end SheafOfModules
