/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!

# Weil objects in the bounded constructible derived category of `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ` the condensed ring of `ℚ̄_ℓ`, and let
`X` be a scheme with an endomorphism `Φ : X ⟶ X`. The *Frobenius pullback* on the bounded
constructible derived category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of `ℚ̄_ℓ`-sheaves, the module objects over
`ℚ̲̄_ℓ,X = p_X^* ℚ̲̄_ℓ`, is the restricted derived pullback
`LΦ^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ Φ`. The coefficients are kept fixed by
construction: the pullback on module objects is the extension of scalars along the coefficient
isomorphism `α_Φ : Φ^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, and the preservation of bounded constructibility is the
input `boundedConstructible_leftDerivedUpperStar_obj`.

A *Weil object* of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `Φ` is an object `K` together with an isomorphism
`φ_K : LΦ^* K ≅ K` as structure data, that is an object of
`CategoryTheory.Endofunctor.IsoAlgebra (LΦ^*)`
(`ProEtale.CondensedRing.WeilBoundedConstructible`). Morphisms are morphisms of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
commuting with the structure isomorphisms.

Forgetting bounded constructibility, a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is a Weil object of the
ambient derived category `D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback `L((Φ)^*⟦ℚ̲̄_ℓ⟧)`: this is
the transport of algebras along the inclusion, using the compatibility isomorphism
`boundedConstructibleUpperStarCompatibility`
(`ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory`).

## The setting

The setting is that of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, specialized to
the coefficient ring `ℚ̲̄_ℓ`: a prime `ℓ`, a field `k` of characteristic `p > 0` with `p ≠ ℓ`,
and `X` separated and of finite type over `Spec k`. The endomorphism `Φ : X ⟶ X` is a morphism
of `Over (Spec (.of k))`, the bounded constructible pullback being defined for morphisms of
`Over (Spec (.of k))` only.

## The two Frobenii

The structure morphism is an endomorphism `Φ` and not an automorphism, so that both Frobenii
of the geometric fiber `X = X₀ ×_{𝔽_q} k̄` of a scheme `X₀` over a finite field fit:

* the *relative Frobenius* `Φ = F_{X₀} × 𝟙` is a morphism over `Spec k̄`, but not an
  isomorphism; it is the Frobenius of the Lefschetz trace formula, whose fixed points are the
  points of `X₀(𝔽_{q^m})` (`WeilConjectures.TraceFormula`);
* an *automorphism* `e : X ≅ X` over `Spec k` gives the Weil objects for `Φ = e.hom`. For these
  the Frobenius pullback is an equivalence, which is what the Weil structures on `Rf_*`, `Rf_!`,
  `Rf^!` and `RHom` of `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar`,
  `LowerUpperShriek` and `TensorHom` use.

The geometric Galois Frobenius `Scheme.Hom.geometricFrobenius` is semilinear over `k̄`, not a
morphism over `Spec k̄`, so it is neither of the two. Since the absolute Frobenius acts trivially
on the étale topos, it induces the same Weil objects as the relative Frobenius.

## Main definitions

- `ProEtale.CondensedRing.WeilBoundedConstructible`: the category of Weil objects of
  `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for an endomorphism `Φ` of `X` over `Spec k`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.forget`: the forgetful functor to
  `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory`: the functor to the Weil
  objects of `D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback along `Φ`.

-/
@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (Φ : X ⟶ X)

/-- A *Weil object* of the bounded constructible derived category `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` of
`ℚ̄_ℓ`-sheaves for an endomorphism `Φ : X ⟶ X` over `Spec k` is an object `K` together with an
isomorphism `φ_K : LΦ^* K ≅ K`, where `LΦ^* = boundedConstructibleUpperStar ℚ̲̄_ℓ ℓ Φ` is
the restricted derived pullback along `Φ`. The isomorphism `φ_K` is structure data, and
morphisms are morphisms of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` commuting with the structure isomorphisms. -/
abbrev WeilBoundedConstructible : Type _ :=
  IsoAlgebra (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)

namespace WeilBoundedConstructible

/-- The forgetful functor from Weil objects of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` to `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`, discarding the
Frobenius structure isomorphisms. -/
noncomputable def forget :
    WeilBoundedConstructible ℓ Φ ⥤ Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  IsoAlgebra.forget (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)

/-- A Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` is a Weil object of the ambient derived category
`D(Mod_{ℚ̲̄_ℓ,X})` for the derived pullback `L((Φ)^*⟦ℚ̲̄_ℓ⟧)`: the transport of algebras along
the inclusion, the structure isomorphism of `K` being
`L((Φ)^*⟦ℚ̲̄_ℓ⟧) K ≅ LΦ^* K ≅ K` through `boundedConstructibleUpperStarCompatibility`. -/
noncomputable def toDerivedCategory :
    WeilBoundedConstructible ℓ Φ ⥤
      IsoAlgebra L((Φ.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  IsoAlgebra.mapOfNatIso
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ Φ).symm

@[simp]
lemma toDerivedCategory_obj_carrier (K : WeilBoundedConstructible ℓ Φ) :
    ((toDerivedCategory ℓ Φ).obj K).carrier = K.carrier.obj :=
  rfl

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
