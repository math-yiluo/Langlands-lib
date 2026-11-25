/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.PoincareDuality.Abstract

/-!
# Biduality for dualizable objects

Let `C` be a braided monoidal closed category and `ω` an object of `C`. The double-dual morphism
`CategoryTheory.Verdier.bidualityMap ω K : K ⟶ D D K`, `D = RHom(-, ω)`, of the abstract Verdier
formalism is the double-dual map `CategoryTheory.MonoidalClosed.toIhomIhom ω K`. This file
records the consequences of this identification. The first one is the formal "lisse" step of
constructible biduality (blueprint `theorem-verdier-biduality`): when `ω` is invertible, as the
dualizing complex `ω_S ≅ Λ_S(d)[2d]` of a smooth stratum `S` is, and `K` is dualizable, as a
lisse complex is, the double-dual morphism `δ_K` is an isomorphism.

## Main statements

- `CategoryTheory.Verdier.bidualityMap_eq_toIhomIhom`: `δ_K` is the double-dual map
  `toIhomIhom ω K`.
- `CategoryTheory.Verdier.isIso_bidualityMap_of_isDualizable`: `δ_K` is an isomorphism for a
  dualizable `K` and an object `ω` isomorphic to an invertible object.
- `CategoryTheory.Verdier.isIso_bidualityMap_iff_of_iso`: whether `δ_K` is an isomorphism only
  depends on the isomorphism class of `K`.
-/

@[expose] public section

namespace CategoryTheory.Verdier

open MonoidalCategory MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]

/-- The double-dual morphism `δ_K : K ⟶ D D K` of the Verdier formalism is the double-dual map
`CategoryTheory.MonoidalClosed.toIhomIhom`. -/
lemma bidualityMap_eq_toIhomIhom (ω K : C) : bidualityMap ω K = toIhomIhom ω K :=
  rfl

/-- **Biduality for dualizable objects** (the formal lisse step of the blueprint theorem
`theorem-verdier-biduality`): if `ω` is isomorphic to an invertible object and `K` is
dualizable, the double-dual morphism `δ_K : K ⟶ D D K`, `D = RHom(-, ω)`, is an isomorphism. -/
theorem isIso_bidualityMap_of_isDualizable {T ω : C} (γ : T ≅ ω) (hT : IsInvertible T) {K : C}
    (hK : IsDualizable K) : IsIso (bidualityMap ω K) :=
  isIso_toIhomIhom_of_isDualizable γ hT hK

/-- The double-dual morphism `δ_K` is an isomorphism if and only if `δ_{K'}` is, for `K ≅ K'`:
the double-dual morphisms form a natural transformation. -/
lemma isIso_bidualityMap_iff_of_iso (ω : C) {K K' : C} (e : K ≅ K') :
    IsIso (bidualityMap ω K) ↔ IsIso (bidualityMap ω K') :=
  NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans ω) e

end CategoryTheory.Verdier
