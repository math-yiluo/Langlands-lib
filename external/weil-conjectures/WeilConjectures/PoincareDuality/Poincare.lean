/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SmoothPurity.Defs

/-!

# Poincaré duality for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime, `k` a field of characteristic `≠ ℓ` and `p : X ⟶ S` a smooth morphism of
pure relative dimension `d` of separated `k`-schemes of finite type. Smooth purity
(`ProEtale.CondensedRing.smoothPurityIso`, the inverse of the adjoint of the trace
`ProEtale.CondensedRing.smoothTrace`) provides the isomorphism
`pur_p : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]`, and this file defines from it, through the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract`:

* the **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S`, the composite of `Rp_!(pur_p⁻¹)` and the
  counit of `Rp_! ⊣ Rp^!`;
* the **Poincaré duality morphism** `PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`, the
  composite of `Rp_*(pur_p⁻¹)`, the identification `Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)` and
  the Verdier exchange morphism `Φ_{p,ℚ̄_ℓ,X,ℚ̄_ℓ,S}`;
* the **compact-support cup product** `cup_c : Rp_! K ⊗ᴸ Rp_* L ⟶ Rp_!(K ⊗ᴸ L)` of arbitrary
  bounded constructible `ℚ̄_ℓ`-module objects `K` and `L` on `X`, from the derived exceptional
  projection morphism and the counit of `Lp^* ⊣ Rp_*` (this does not use purity).

The trace and `PD_p` share the normalization of `pur_p`, and the transpose of `PD_p` is exactly
`Tr_p ∘ cup_c` for `K = ℚ̄_ℓ,X` and `L = ℚ̄_ℓ,X(d)[2d]`, up to `ℚ̄_ℓ,X ⊗ᴸ L ≅ L`
(`ProEtale.CondensedRing.uncurry_poincareMap`), and `PD_p` is an isomorphism by Verdier
duality (`ProEtale.CondensedRing.isIso_poincareMap`), which is **Poincaré duality** in the
form `𝔻_S(Rp_! ℚ̄_ℓ,X) ≅ Rp_* ℚ̄_ℓ,X(d)[2d]`.

All objects live in the bounded constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`, which are
monoidal closed subcategories of the ambient derived categories
(`ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`). As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `X` and `S` are
objects of `Over (Spec (.of k))` and `p` a morphism of `Over (Spec (.of k))`.

## Not treated here

* The passage from the derived statement to the perfect pairing
  `H^i_c(X, ℚ̄_ℓ) × H^{2d-i}(X, ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ` on cohomology groups over `S = Spec k̄`, which
  requires the perfectness of `Rp_! ℚ̄_ℓ,X` and the comparison of `RΓ(S, RHom(-, ℚ̄_ℓ,S))` with the
  linear dual.
* The Frobenius equivariance, which belongs to the Weil sheaf formalism.
* The compatibility with the compactly supported base change isomorphism and with the
  compactification and composition comparisons, which are commutativity conditions on the maps
  defined here, to be stated once those comparisons are available.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom]
  (p : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d p.left]

/-! ### Smooth purity on bounded constructible complexes -/

/-- The purity isomorphism `pur_p : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]` of
`ProEtale.CondensedRing.smoothPurityIso`, as an isomorphism in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: the inverse of
the adjoint `ProEtale.CondensedRing.smoothPurityMap` of the trace. No new choice is made: it is
the only normalization entering the trace and Poincaré duality below. -/
noncomputable def boundedConstructibleSmoothPurityIso :
    (boundedConstructibleUpperShriek ℓ p).obj (𝟙_ _) ≅
      boundedConstructibleTateTwist ℓ X d (2 * d) :=
  (asIso (smoothPurityMap ℓ p d)).symm

/-- The **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of a smooth morphism `p : X ⟶ S` of pure
relative dimension `d`: `Rp_!(pur_p⁻¹)` followed by the counit of `Rp_! ⊣
Rp^!`. -/
noncomputable def trace :
    (boundedConstructibleLowerShriek ℓ p).obj
      (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶ 𝟙_ _ :=
  Verdier.trace (boundedConstructibleUpperShriekAdjunction ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

/-- The **Poincaré duality morphism**
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`: `Rp_*(pur_p⁻¹)`, the
identification `Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)`, and the Verdier exchange morphism. -/
noncomputable def poincareMap :
    (boundedConstructibleLowerStar ℓ p).obj
        (boundedConstructibleTateTwist ℓ X d (2 * d)) ⟶
      (ihom ((boundedConstructibleLowerShriek ℓ p).obj
        (𝟙_ _))).obj (𝟙_ _) :=
  Verdier.poincareMap (boundedConstructibleUpperStarLowerStarAdjunction ℓ p)
    (boundedConstructibleUpperShriekAdjunction ℓ p)
    (boundedConstructibleExceptionalProjection ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

/-- The **compact-support cup product** `cup_c : Rp_! K ⊗ᴸ Rp_* L ⟶ Rp_!(K ⊗ᴸ L)` of two
bounded constructible `ℚ̄_ℓ`-module objects `K` and `L` on `X`: the derived exceptional projection
morphism `PF^!_{p,K,Rp_* L}`, followed by `Rp_!(K ⊗ᴸ -)` of the counit `Lp^* Rp_* L ⟶ L`. -/
noncomputable def cupProduct (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ p).obj K ⊗ (boundedConstructibleLowerStar ℓ p).obj L ⟶
      (boundedConstructibleLowerShriek ℓ p).obj (K ⊗ L) :=
  Verdier.cupProduct (boundedConstructibleUpperStarLowerStarAdjunction ℓ p)
    (boundedConstructibleExceptionalProjection ℓ p) K L

/-- **Poincaré duality is the trace–cup pairing**: the transpose
`Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of the Poincaré duality morphism is the cup product
`Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_!(ℚ̄_ℓ,X ⊗ᴸ ℚ̄_ℓ,X(d)[2d]) ≅ Rp_! ℚ̄_ℓ,X(d)[2d]` followed by
the trace. -/
theorem uncurry_poincareMap :
    uncurry (poincareMap ℓ p d) =
      cupProduct ℓ p (𝟙_ _) (boundedConstructibleTateTwist ℓ X d (2 * d)) ≫
        (boundedConstructibleLowerShriek ℓ p).map (λ_ _).hom ≫ trace ℓ p d :=
  Verdier.uncurry_poincareMap _ _ _ _

/-- **Poincaré duality**: the Poincaré duality morphism
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)` is an isomorphism, by Verdier duality. -/
theorem isIso_poincareMap : IsIso (poincareMap ℓ p d) := by
  have := isIso_verdierExchange ℓ p (𝟙_ _) (𝟙_ _)
  unfold poincareMap Verdier.poincareMap
  exact inferInstanceAs (IsIso (_ ≫ verdierExchange ℓ p (𝟙_ _) (𝟙_ _)))

end AlgebraicGeometry.ProEtale.CondensedRing
