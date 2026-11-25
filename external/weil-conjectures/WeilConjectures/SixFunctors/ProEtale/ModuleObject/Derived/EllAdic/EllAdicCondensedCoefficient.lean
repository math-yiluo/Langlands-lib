/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-! # The three condensed coefficient rings used for the exceptional inverse image

Source: the coefficient list in the bounded constructible exceptional inverse image.
(blueprint: def-sfb-adic-coefficient-certificate)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Admissibility for the three coefficient families in the bounded constructible upper
shriek construction. The multiplication and unit are indices as well as the sheaf, so this
predicate cannot accidentally certify another ring structure on the same underlying sheaf.

Source: blueprint, the three examples of proper pushforward admitting a right adjoint.
(blueprint: def-sfb-adic-coefficient-certificate) -/
inductive IsEllAdicCoefficient (ℓ : ℕ) [Fact ℓ.Prime] :
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) → MonObj Λ → Prop
  | continuous (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
      [FiniteDimensional ℚ_[ℓ] E] :
      IsEllAdicCoefficient ℓ (Profinite.continuousMapRingObj E) inferInstance
  | integral (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
      [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
      IsEllAdicCoefficient ℓ (Profinite.padicIntegersRingObj ℓ E) inferInstance
  | algebraicClosure :
      IsEllAdicCoefficient ℓ (Profinite.padicAlgClRingObj ℓ) inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
