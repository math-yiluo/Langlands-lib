/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
import WeilConjectures.RingTheory.SelfTorConormalComparisonHomotopyNormalization

/-! Existence of the normalized self-Tor comparison. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The Tate resolution construction supplies a normalized comparison map.
Source: Stacks Project, Tag 09PQ (strictly graded commutative self-Tor), and
Tag 00LS (comparison of free complexes with resolutions).
(blueprint: new-r4-self-tor-conormal-comparison-existence).

Proof: Choose a Tate free strictly commutative dg algebra resolving A/I. The
quotient exact sequence identifies degree-one self-Tor with I/I²: an element
x of I is represented by a degree-one lift whose differential is x. After
base change to A/I this is a cycle, and changing the lift changes its class
by a boundary. Multiplication of n such classes is alternating, even in
characteristic two, by strict graded commutativity. It is A/I-multilinear,
so the exterior universal property gives an A/I-linear map, and restriction
of scalars gives the required A-linear morphism. For a tuple g, send each
Koszul generator to a degree-one lift of its ideal element in the Tate
resolution. This defines a dg algebra map preserving the augmentation;
its value on every wedge is the product just used. Comparison with any
projective resolution P transports this formula to P. Any other chain lift
a has the same effect on homology: the Koszul terms are free, so inductive
lifting against the exact augmented target constructs a chain homotopy
between the two lifts. Tensoring preserves that homotopy. This proves the
normalization for every v and cycle z in the statement. In degree zero the
empty product is the quotient unit. For I=0 positive exterior degrees
vanish, and for I=A the quotient modules vanish; neither case requires a
nonzero ring or a regular sequence. -/
theorem selfTorConormalComparison_exists (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃ c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), IsSelfTorConormalComparison A I n c := by
  obtain ⟨c, hc⟩ := tate_selfTor_conormal_map A I n
  exact ⟨c, tate_comparison_homotopy_normalization A I n c hc⟩

end AlgebraicGeometry
