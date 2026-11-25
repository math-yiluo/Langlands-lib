/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeLeftAdjunct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedQbarExchangeRightAdjunct

/-! # The exchange equality for condensed finite-to-Qbar coefficient change -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- Coefficient extension respects the specified unit-square-counit exchange arrow.
Source: `ModuleObject/Colimit/TwoColimit.lean`, final transport paragraph;
`ModuleObject/ChangeOfCoefficients.lean`, Derived section; mate pasting in
`Mathlib/CategoryTheory/Adjunction/Mates.lean`
(blueprint: lem-weil-pbc-qbar-condensed-exchange-equality).

Proof in words. Write T for scalar extension, l_h for derived pullback, r_h for derived
pushforward, α_h: T l_h,E ≅ l_h,Ω T for the pull comparison, and δ_h: T r_h,E → r_h,Ω T
for the push comparison. By their definitions from the same restriction/direct-image
isomorphism, δ_h is the mate of α_h inverse along the two pull/push adjunctions. This follows
by expanding pullIsoOfComapIso and pushHomOfComapIso: conjugation is the mate correspondence
for the composite adjunctions, and the two successive transpositions cancel. In particular,
the adjunct of δ_h at K is α_h inverse at r_h,E(K), followed by T of the E-counit.

The α comparisons respect composition of scheme morphisms. At the underived module level,
both composites are induced by the identical associativity map on inverse images and the
balanced tensor map b ⊗ (a ⊗ m) ↦ ba ⊗ m. The coefficient square commutes by naturality of
the coefficient map. This gives equality of natural transformations by the tensor and
sheafification universal properties. Exact pullback and flat scalar extension compute their
derived functors termwise; restriction preserves K-injectives since its left adjoint is
exact. Thus the same coherence descends through localization and agrees with the derived
comparisons defined by conjugation. The composition comparisons are the derived ones used
in boundedConstructiblePullbackSquareComparison, rather than newly chosen comparisons.

Let θ_A: l_f',A l_g,A ≅ l_g',A l_f,A be the square comparison. Coherence gives the following
commuting diagram, suppressing object arguments and the canonical associators:
T(θ_E), then α_g', then l_g',Ω(α_f) equals α_f', then l_f',Ω(α_g), then θ_Ω(T).
Both routes start at T l_f',E l_g,E and end at l_g',Ω l_f,Ω T. The equality also respects
the commutativity proof in the square: substitution by equal morphisms is natural, and
proof irrelevance identifies proofs of that equality.

Take mates of this equality along l_f,E ⊣ r_f,E and l_f',E ⊣ r_f',E, and along the analogous
Ω-adjunctions. Mate pasting preserves equality and composition (mateEquiv_hcomp and
mateEquiv_vcomp, equivalently mateEquiv_square). The mate of θ_A is exactly the specified
exchange B_A: expanding the mate is unit insertion, square transport, then counit contraction.
The edge mates are δ_f and δ_f', by the first paragraph. Thus the resulting equality is
B_Ω(T(K)) ∘ l_g,Ω(δ_f(K)) ∘ α_g(r_f,E(K)) =
r_f',Ω(α_g'(K)) ∘ δ_f'(l_g',E(K)) ∘ T(B_E(K)), exactly the asserted formula.
The bounded constructible adjunction and square comparison are restrictions along fully
faithful inclusions, which preserve the displayed units, counits, and composition constraints.
Neither δ nor B is
inverted; properness and Cartesianity are unnecessary. -/
theorem constructibleToQbar_exchange_equality
    (sq : CommSq g' f' f g) (K : PadicSubfieldConstructible X ℓ E) :
    constructibleToQbarSourceHom ℓ k E f g K ≫
        (boundedConstructibleBaseChange ℓ (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl X ℓ E).obj K) =
      (constructibleToPadicAlgCl Y' ℓ E).map
          ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
            (sq.asOver (Spec (.of k)))).app K) ≫
        constructibleToQbarTargetHom ℓ k E f' g' K := by
  apply ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
    (f'.asOver (Spec (.of k)))).homEquiv _ _).symm.injective
  exact (constructibleToQbar_exchange_left_adjunct ℓ k E f g f' g' sq K).trans
    (constructibleToQbar_exchange_right_adjunct ℓ k E f g f' g' sq K).symm

end AlgebraicGeometry.ProEtale.CondensedRing
