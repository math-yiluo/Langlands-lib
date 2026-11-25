/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

/-!
# Admissible condensed coefficient rings

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-stratum-hom.md, opening coefficient hypothesis
(blueprint: def-pur-admissible-condensed-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The stated coefficient family, invariant under isomorphism of condensed rings.
Finite rings have the discrete topology; finite extensions have their induced ell-adic
 topology. The algebraic closure is the existing finite-subextension-valued condensed ring.
Source: blueprint stratum Hom lemma, admissible coefficients
(blueprint: def-pur-admissible-condensed-ring). -/
def IsAdmissibleCoefficient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  ∃ (l : ℕ) (_hl : Fact l.Prime),
    (∃ (A : Type) (_hA : CommRing A) (_hfin : Finite A)
      (_htop : TopologicalSpace A) (_hd : DiscreteTopology A) (_hr : IsTopologicalRing A),
      (∃ n : ℕ, (l ^ n : A) = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[l])) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} ℚ_[l])) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj.{u} l E))) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} l))

end AlgebraicGeometry.ProEtale.CondensedRing
