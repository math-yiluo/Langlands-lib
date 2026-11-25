/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModel
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange

/-!

# The cartesian factor of a weakly étale morphism of models

If the morphism of total spaces of a morphism of models `φ` is weakly étale, the pullback exchange
of the second factor `fromCartesian` of its cartesian factorization is an isomorphism, by weakly
étale base change of `Rj_*`
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_fromCartesian_of_weaklyEtale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom

open Scheme

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- If the morphism of total spaces of `φ` is weakly étale, the pullback exchange of
`fromCartesian` is an isomorphism (weakly étale base change of `Rj_*`). -/
lemma isIso_pullbackExchange_fromCartesian_of_weaklyEtale
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    [WeaklyEtale φ.total] : IsIso (φ.fromCartesian.pullbackExchange Λ) :=
  have : WeaklyEtale φ.fromCartesian.total := ‹WeaklyEtale φ.total›
  φ.fromCartesian.isIso_pullbackExchange_of_weaklyEtale Λ φ.isPullback_fromCartesian

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom
