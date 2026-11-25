/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistDerivedScalar

/-! # Named canonical integral twist and scalar comparisons

Source: blueprint `definition-tate-twists--10`, integral/common-stage paragraph
(blueprint: lem-weil-integral-twist-derived-scalar).

The existing theorem specifies the ordinary comparison on all good K-flat representatives
by its pure-tensor formula and universal counit equation. These determine the natural
isomorphism: localization is essentially surjective and the pure tensors generate locally.
The completed comparison is determined by conjugation with the fixed completion maps.
The definitions below project those specified witnesses, without choosing arbitrary maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (ι : E →ₐ[Padic l] F) (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]

/-- The ordinary beta, fixed by the exact K-flat pure-tensor and descent characterization
in `integral_twist_derived_scalar` (its first existential witness).
Source: blueprint `definition-tate-twists--10`, integral/common-stage paragraph
(blueprint: lem-weil-integral-twist-derived-scalar). -/
def integralTwistOrdinaryBeta (m : ℤ) :
    (sfIntegralConstructible l E S).ι ⋙
        (integralSheafTwist l E S m).mapDerivedCategory ⋙
        completedDerivedScalarExtension l E F ι S ≅
      (sfIntegralConstructible l E S).ι ⋙ completedDerivedScalarExtension l E F ι S ⋙
        (integralSheafTwist l F S m).mapDerivedCategory :=
  (integral_twist_derived_scalar l E F ι S m).choose

end WeilConjectures
