/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible
public import WeilConjectures.TateTwist.Pullback

/-!
# Pullback of the bounded constructible Tate twists

Let `ℓ` be a prime and `k` a field of characteristic `p > 0` with `p ≠ ℓ`, so that `ℓ` is
invertible on every `k`-scheme. For a morphism `g : X' ⟶ X` of separated `k`-schemes of finite
type, the derived pullback `Lg^* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(X')⟦ℚ̲̄_ℓ⟧` sends the shifted Tate twist
`ℚ̄_ℓ,X(d)[n]` to `ℚ̄_ℓ,X'(d)[n]`
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarTateTwistIso`). This is
the restriction to bounded constructible complexes of
`AlgebraicGeometry.ProEtale.upperStarShiftTateTwistDerivedIso`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

omit [Fact (ringChar k).Prime] in
/-- The prime `ℓ` is invertible in a field `k` whose characteristic is different from `ℓ`. -/
lemma neZero_natCast_of_ringChar_ne : NeZero (ℓ : k) :=
  ⟨fun h ↦ (Fact.out : ringChar k ≠ ℓ)
    (((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h)).resolve_left
      CharP.ringChar_ne_one)⟩

variable {X X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- **The pullback of the Tate twists**: for a morphism `g : X' ⟶ X` of separated `k`-schemes
of finite type, `Lg^* ℚ̄_ℓ,X(d)[n] ≅ ℚ̄_ℓ,X'(d)[n]` in `Dᵇc(X')⟦ℚ̲̄_ℓ⟧`. -/
noncomputable def boundedConstructibleUpperStarTateTwistIso (g : X' ⟶ X) (d n : ℤ) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj
        (boundedConstructibleTateTwist ℓ X d n) ≅ boundedConstructibleTateTwist ℓ X' d n :=
  have := neZero_natCast_of_ringChar_ne ℓ (k := k)
  (boundedConstructible _).fullyFaithfulι.preimageIso
    (upperStarShiftTateTwistDerivedIso ℓ g.left X.hom d n)

end AlgebraicGeometry.ProEtale.CondensedRing
