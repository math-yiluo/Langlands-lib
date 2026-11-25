/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.SixFunctors.ProEtale.SeparableClosureCover
public import WeilConjectures.TateTwist.LocallyFreeOfTrivial
public import WeilConjectures.TateTwist.TateModuleTrivialization
public import WeilConjectures.TateTwist.UpperStarExtendScalars

/-!
# The Tate twists are locally free of rank one

Let `X` be a scheme over a field `k` in which the prime `ℓ` is invertible. Every Tate twist
`ℚ̄_ℓ,X(d)`, `d ∈ ℤ`, is a locally free `ℚ̄_ℓ,X`-module of rank one
(`AlgebraicGeometry.ProEtale.isLocallyFree_tateTwist`; blueprint
`definition-tate-twists` (3)): over the pro-étale cover `X ×_k Spec kˢᵉᵖ ⟶ X`, a
compatible system of primitive `ℓⁿ`-th roots of unity of `kˢᵉᵖ`
(`IsSepClosed.exists_isPrimitiveRoot_pow_eq`) trivializes the Tate module `ℤ_ℓ(1)`
(`ProEtale.upperStarMapModTateModuleIsoUnit`), hence `ℚ̄_ℓ(1)`
(`ProEtale.upperStarMapModExtendScalarsIsoUnit`), hence all its tensor powers and their duals
(`ProEtale.isLocallyFree_tateTwist_of_iso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **The Tate twists are locally free of rank one** (blueprint
`definition-tate-twists` (3)): for a scheme `X` over a field `k` in which `ℓ` is
invertible, every `ℚ̄_ℓ,X(d)` is a locally free `ℚ̄_ℓ,X`-module, trivial over `X ×_k Spec kˢᵉᵖ`. -/
theorem isLocallyFree_tateTwist {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : k)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (d : ℤ) :
    IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (tateTwist X ℓ d) := by
  have : NeZero (ℓ : SeparableClosure k) :=
    ‹NeZero (ℓ : k)›.of_injective (algebraMap k (SeparableClosure k)).injective
  obtain ⟨ζ, hζ, hζ'⟩ := IsSepClosed.exists_isPrimitiveRoot_pow_eq (SeparableClosure k) ℓ
  refine isLocallyFree_tateTwist_of_iso ℓ (sepClosureCover f) (fun _ ↦ ⟨?_⟩) d
  exact upperStarMapModExtendScalarsIsoUnit (pullback.fst f (specSepClosureHom k))
    (Profinite.padicIntRingObjToPadicAlgCl ℓ) _
    (upperStarMapModTateModuleIsoUnit (pullback.fst f (specSepClosureHom k))
      (pullback.snd f (specSepClosureHom k)) ℓ hζ hζ')

end AlgebraicGeometry.ProEtale
