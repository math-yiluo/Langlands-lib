/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SelfTorConormalComparisonPredicate
import WeilConjectures.RingTheory.SelfTorConormalComparisonExistence
import WeilConjectures.RingTheory.SelfTorConormalComparisonUnique

/-! # The normalized exterior-to-self-Tor map

Source: Stacks Project, Tags 09PQ and 062I.
(blueprint: new-r4-self-tor-conormal-comparison). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- There is a unique comparison with Koszul normalization, without regularity assumptions.

Source: Stacks Project, Tag 09PQ, the resolution-independent strictly commutative Tor
algebra, and the boundary identification Tor_1(A/I,A/I) = I/I² used with Tag 062I.
(blueprint: new-r4-self-tor-conormal-comparison).

Proof: Resolve A/I by a Tate free strictly commutative dg algebra. A lift of an ideal
element to degree one gives a cycle after tensoring with A/I. Changing the lift changes
its homology class by a boundary; the quotient exact sequence identifies this class
with the ideal element modulo I². Multiply n such classes. Strict commutativity makes
this product alternating, including in characteristic two, and it is A/I-multilinear.
The exterior universal property therefore gives the displayed A-linear map. Comparison
of resolutions identifies the product with the top Koszul wedge for every tuple g:
the map from the Koszul dg algebra to the Tate resolution sends each generator to its
chosen degree-one lift. Every chain lift a has the same effect on homology, because
the source is a bounded complex of projective modules and two lifts of its augmentation
to a projective resolution are chain homotopic. Thus the map has the displayed
normalization for every P and a. Conversely these lifts exist, and every pure wedge of
conormal classes has lifts in I. The normalization determines every pure wedge, so
exterior generation gives uniqueness. For n=0 it is the quotient unit; zero quotients
and the zero ideal satisfy the same construction. -/
theorem existsUnique_selfTor_conormal_comparison (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)), IsSelfTorConormalComparison A I n c := by
  obtain ⟨c, hc⟩ := selfTorConormalComparison_exists A I n
  exact ⟨c, hc, fun d hd => (selfTorConormalComparison_unique A I n c d hc hd).symm⟩

/-- The actual normalized exterior-to-self-Tor comparison. The theorem used to select it
fixes its value on all pure wedges, and determines it uniquely.
Source: Stacks Project, Tag 09PQ.
(blueprint: new-r4-self-tor-conormal-comparison). -/
noncomputable def selfTorConormalComparison (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)) :=
  (existsUnique_selfTor_conormal_comparison A I n).exists.choose

/-- The canonical comparison has its defining normalization.
Source: Stacks Project, Tag 09PQ.
(blueprint: new-r4-self-tor-conormal-comparison). -/
theorem selfTorConormalComparison_spec (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :
    IsSelfTorConormalComparison A I n (selfTorConormalComparison A I n) :=
  (existsUnique_selfTor_conormal_comparison A I n).exists.choose_spec

end AlgebraicGeometry
