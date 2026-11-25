/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!
# Base change for every coefficient with constructible pushforward

Source: the blueprint, `chap-Construction-of-f`, unit `sk-def-sfb-base-change-morphism`
(blueprint: sk-def-sfb-base-change-morphism).

The pullback comparison is the existing `boundedConstructiblePullbackSquareComparison`.
The three steps below use the conditional restricted pushforward and its actual restricted
adjunction, with precisely the unit--comparison--counit formula of the source. The imported
coefficient constructions include the finite-subextension-valued condensed algebraic closure.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (H : PreservesBoundedConstructiblePushforwards Λ k)

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- Insert the unit of `Lf'^* ⊣ Rf'_*` after `Lg^* Rf_*`.
Source: blueprint `sk-def-sfb-base-change-morphism`, first step
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeUnitStepOfPreserves :
    boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
    (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g)
    (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H f' ℓ).unit

variable {f g f' g'} in
/-- Transport the unit-inserted functor by the canonical pullback-square comparison, built
from the two composition isomorphisms and the equality in `sq`.
Source: blueprint `sk-def-sfb-base-change-morphism`, second step
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeSquareStepOfPreserves (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') ≅
      (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') :=
  Functor.squareTransport (boundedConstructibleLowerStarOfPreserves Λ H f)
    (boundedConstructibleLowerStarOfPreserves Λ H f')
    (boundedConstructiblePullbackSquareComparison Λ ℓ sq)

/-- Contract the counit of `Lf^* ⊣ Rf_*` under `Lg'^*` and `Rf'_*`.
Source: blueprint `sk-def-sfb-base-change-morphism`, third step
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeCounitStepOfPreserves :
    (boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f' :=
  Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves Λ H f ℓ).counit
    (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f') ≫
    (Functor.leftUnitor _).hom

variable {f g f' g'} in
/-- The base-change morphism `Lg^* Rf_* ⟶ Rf'_* Lg'^*`, in diagrammatic composition order,
for every commutative square and every commutative condensed ring whose derived pushforwards
preserve bounded constructible complexes. Its data are the specified unit insertion,
canonical square transport and counit contraction, with no cartesian or proper hypothesis.
Source: blueprint unit `sk-def-sfb-base-change-morphism`
(blueprint: sk-def-sfb-base-change-morphism). -/
noncomputable def boundedConstructibleBaseChangeOfPreserves (sq : CommSq g' f' f g) :
    boundedConstructibleLowerStarOfPreserves Λ H f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStarOfPreserves Λ H f' :=
  boundedConstructibleBaseChangeUnitStepOfPreserves Λ ℓ H f g f' ≫
    (boundedConstructibleBaseChangeSquareStepOfPreserves Λ ℓ H sq).hom ≫
      boundedConstructibleBaseChangeCounitStepOfPreserves Λ ℓ H f f' g'

end AlgebraicGeometry.ProEtale.CondensedRing
