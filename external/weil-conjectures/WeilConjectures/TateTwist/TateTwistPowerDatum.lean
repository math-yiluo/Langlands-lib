/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TateTwist.Pullback
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTensorPowerInduction

/-!
# The pullback data of the Tate twists `ℚ̄_ℓ(d)` from that of `ℚ̄_ℓ(1)`

For an endomorphism `g : X ⟶ X` (the Frobenius of the geometric fibre), the pairs
`(ℚ̄_ℓ,X(d), g^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X(d))` (`AlgebraicGeometry.ProEtale.upperStarTateTwistNatIso`)
are the tensor powers of the pair for `d = 1`
(`AlgebraicGeometry.ProEtale.tensorPowPair_tateTwistOnePair`). Hence a trivialization
`ℚ̄_ℓ,X(1) ≅ ℚ̄_ℓ,X` carrying the pullback datum to a scalar `s` times the unit constraint gives,
for every `d`, a trivialization `ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X` carrying it to `s^d`
(`AlgebraicGeometry.ProEtale.exists_iso_tateTwistNat_of_one`): the Frobenius acts on `ℚ̄_ℓ(d)` by
`χ_ℓ(σ)^d`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : k)] {X : Scheme.{u}}
  (g : X ⟶ X) (f : X ⟶ Spec (.of k))

/-- The unit datum `g^* ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,X`: the inverse unit constraint of the monoidal pullback
`g^*`. It is a `def` so that it is a fixed constant (no comparison of monoidal instances). -/
noncomputable def tateUnitDatum :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).obj (𝟙_ _) ⟶ 𝟙_ _ :=
  η (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g)

/-- The pair `(ℚ̄_ℓ,X(1), g^* ℚ̄_ℓ,X(1) ≅ ℚ̄_ℓ,X(1))`. -/
noncomputable def tateTwistOnePair :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g) :=
  IsoAlgebra.mk (tateTwistOne X ℓ) (upperStarTateTwistOneIso ℓ g f)

/-- The pairs `(ℚ̄_ℓ,X(d), g^* ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X(d))` are the tensor powers of the pair for
`d = 1`. -/
theorem tensorPowPair_tateTwistOnePair :
    ∀ d : ℕ, IsoAlgebra.tensorPowPair _ (tateTwistOnePair ℓ g f) d =
      IsoAlgebra.mk (tateTwistNat X ℓ d) (upperStarTateTwistNatIso ℓ g f d)
  | 0 => rfl
  | d + 1 => by
    rw [IsoAlgebra.tensorPowPair_succ, tensorPowPair_tateTwistOnePair d]
    simp only [IsoAlgebra.tensorWith, IsoAlgebra.mk_str, tateTwistOnePair]
    rfl

/-- **The Frobenius acts on `ℚ̄_ℓ(d)` by the `d`-th power of its action on `ℚ̄_ℓ(1)`**: a
trivialization `ℚ̄_ℓ,X(1) ≅ ℚ̄_ℓ,X` carrying the pullback datum of `ℚ̄_ℓ,X(1)` to `ε⁻¹ ≫ s` gives
trivializations `ℚ̄_ℓ,X(d) ≅ ℚ̄_ℓ,X` carrying the pullback data to `ε⁻¹ ≫ s^d`. -/
theorem exists_iso_tateTwistNat_of_one (s : 𝟙_ _ ≅ 𝟙_ _)
    (e : tateTwistOnePair ℓ g f ≅ IsoAlgebra.unitScalarPair _ s) (d : ℕ) :
    ∃ ê : tateTwistNat X ℓ d ≅ 𝟙_ _,
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map ê.hom ≫
          (tateUnitDatum ℓ g ≫ (IsoAlgebra.scalarPow s d).hom) =
        (upperStarTateTwistNatIso ℓ g f d).hom ≫ ê.hom := by
  have key := IsoAlgebra.exists_iso_tensorPowPair_carrier _ e d
  rw [tensorPowPair_tateTwistOnePair] at key
  exact key

end AlgebraicGeometry.ProEtale
