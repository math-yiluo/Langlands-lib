/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateRationalDerived

/-! # The shifted integral Tate datum in terms of its degree-zero datum -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  {k : Type u} [Field k] [NeZero (ℓ : k)] {X X' : Scheme.{u}}

lemma upperStarShiftIntegralTateTwistDerivedIso_hom_eq
    (g : X' ⟶ X) (f : X ⟶ Spec (.of k)) (d : ℕ) (n : ℤ) :
    (upperStarShiftIntegralTateTwistDerivedIso ℓ E g f d n).hom =
      (L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).commShiftIso n).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (integralTateTwistNat X ℓ E d)) ≫
        (upperStarIntegralTateTwistDerivedIso ℓ E g f d).hom⟦n⟧' := rfl

end AlgebraicGeometry.ProEtale
