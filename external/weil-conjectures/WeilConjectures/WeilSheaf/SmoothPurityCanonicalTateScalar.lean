/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeScalarNamed
public import WeilConjectures.WeilSheaf.SmoothPurityScalarDatumNamed
import WeilConjectures.Tactic.ExactModProofs

/-! # The scalar Frobenius law for the canonical geometric Tate line -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  {ζ : ℕ → AlgebraicClosure k} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

local instance : NeZero (ℓ : k) := ⟨by
  rw [Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k _) Fact.out]
  exact Fact.out⟩
local instance : NeZero (ℓ : AlgebraicClosure k) :=
  WeilSheaf.purity_neZero_natCast_algebraicClosure k ℓ

/-- A root trivialization of the geometric Tate line, using its canonical pullback
from the finite-base model. -/
noncomputable def purityCanonicalTateOneTrivialization :
    tateTwistOne a.geometricFiber ℓ ≅
      𝟙_ (Mod (Sheaf (ProEt.topology a.geometricFiber) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) a.geometricFiber)) :=
  purityScalarCanonicalTrivialization ℓ a hζ hζ'

/-- The canonical geometric Tate datum has the expected q-scalar law under the
root trivialization. -/
lemma purityCanonicalTateOneTrivialization_weil :
    (Nat.card k : ℤ) •
        ((upperStarTateTwistOneIso ℓ a.geometricGaloisFrobenius.asIso.hom
          a.geometricFiberToAlgebraicClosure).hom ≫
          (purityCanonicalTateOneTrivialization ℓ a hζ hζ').hom) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        a.geometricGaloisFrobenius.asIso.hom).map
          (purityCanonicalTateOneTrivialization ℓ a hζ hζ').hom ≫
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            a.geometricGaloisFrobenius.asIso.hom)).inv := by
  have h := CategoryTheory.K4Native.scalarEquation_conjugate_named
    (purityScalarFrobeniusPull ℓ a)
    (purityScalarTateCompare ℓ a) (purityScalarUnitCompare ℓ a)
    (purityScalarSourceDatum ℓ a) (purityScalarSourceUnitDatum ℓ a)
    (purityScalarTargetDatum ℓ a) (purityScalarTargetUnitDatum ℓ a)
    (purityScalarTateCompare_comm ℓ a) (purityScalarUnitCompare_comm ℓ a)
    (purityScalarRootTrivialization ℓ a hζ hζ')
    (purityScalarCanonicalTrivialization ℓ a hζ hζ')
    (purityScalarCanonicalTrivialization_eq ℓ a hζ hζ') (Nat.card k : ℤ)
    (K4Native.scalarRootEquation_named a hζ hζ')
  have h' := purityScalarCanonicalEquation ℓ a hζ hζ' h
  dsimp only [purityCanonicalTateOneTrivialization]
  exact_mod_proofs h'

end AlgebraicGeometry.ProEtale
