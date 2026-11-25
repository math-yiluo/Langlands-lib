/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence

/-! # Underived square coherence for arbitrary commutative coefficient rings -/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The canonical underived coefficient comparison square is coherent for modules over any
commutative ring. This specializes the already proved generic `comparison_coherent`, accessed
through the proof-only `import all`; no finiteness assumption is needed.
Source: `ComparisonPullbackCoherence.lean`, `comparison_coherent`, third conjunct;
Stacks Project, Tag 0B65.

Proof: the generic coherence theorem applies to the category of modules over Λ, which has
colimits and sheafification on both sites. Its third conjunct gives the square equation for
all schemes, all four edges, every chosen Cartesian square and every input sheaf. Specialize
these quantifiers to the supplied data. -/
theorem comparison_square_component_of_commRing
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (cs : ChosenCartesianSquare g' f' f g)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ComparisonSquareComponent
      (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs) F := by
  exact (comparison_coherent (ModuleCat.{u + 1} Λ)).2.2 X' X Y' Y g' f' f g cs F

end AlgebraicGeometry.ProEtale
