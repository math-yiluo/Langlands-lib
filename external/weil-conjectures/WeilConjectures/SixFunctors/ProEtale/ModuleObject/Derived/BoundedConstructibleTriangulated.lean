/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulatedBasic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekShift

/-!
# The exceptional inverse image on bounded constructible complexes is triangulated

The restricted functor `Rf^!` on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is triangulated, as the right adjoint of the
triangulated functor `Rf_!` (`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`). The other
restricted functors are treated in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulatedBasic`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

instance isTriangulated_boundedConstructibleUpperShriek (f : X ⟶ Y) :
    (boundedConstructibleUpperShriek ℓ f).IsTriangulated :=
  (boundedConstructibleUpperShriekAdjunction ℓ f).isTriangulated_rightAdjoint

end AlgebraicGeometry.ProEtale.CondensedRing
