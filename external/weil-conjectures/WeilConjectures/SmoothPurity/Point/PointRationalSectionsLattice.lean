/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint

/-! # Finite free integral lattices for the point sections functor

Source: step 10 of the point-fibre argument, the bounded zero-differential lattice.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Every bounded finite-dimensional field complex is the rational fibre of an
integral constructible complex.
Source: blueprint finite-coefficient-point, the rational essential-surjectivity
argument in step 10; vector-space basis and cohomology decomposition.
(blueprint: lem-weil-point-rational-sections-lattice).

Proof: choose finite bases of the finitely many nonzero cohomology spaces of V.
Lift their vectors to cycles in a representative complex. This gives a
quasi-isomorphism from the bounded zero-differential complex with E^d_i in degree i
to that representative. The identical ranks define a bounded finite free O_E
complex P. Since O_E is complete, P is derived complete. It therefore belongs to
pointFgComplete; use the inverse of the integral equivalence to obtain K with
integral section complex isomorphic to P. The integral-to-field tensor carries
P to the displayed E-complex. The canonical size-descent counit identifies that
scalar extension with pointIntegralRationalFibre(K), giving the required isomorphism.
For V = 0 use the empty complex. This constructs objects only and makes no claim
about rational Hom groups. -/
theorem pointRationalSectionsLattice
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (hi : (pointIntegralFibre D l hl E).IsEquivalence)
    (V : (DerivedCategory.pointFiniteDimensional E).FullSubcategory) :
    ∃ K : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      Nonempty ((pointIntegralRationalFibre D l hl E).obj K ≅ V) := by
  sorry

end WeilConjectures
