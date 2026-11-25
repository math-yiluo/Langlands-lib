/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

/-!
# The projection formula on the localizing categories `Loc(Dbc)`

Let `Λ` be a commutative condensed ring and `p : X ⟶ Y` a morphism of schemes. This file proves
the formal part of the projection formula on the localizing categories (blueprint
`proposition-projection-formula-rational-coefficients--2`,
`lemma-projection-formula-integral-coefficients--1` (2)): if

* the projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` is an isomorphism for `M` in `Dbc(X, Λ)` and
  `L` in `Dbc(Y, Λ)`,
* `Rp_*` maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there,
* `Lp^*` maps `Dbc(Y, Λ)` into `Dbc(X, Λ)`, and `Dbc(X, Λ)` is closed under `⊗ᴸ`,

then the projection map is an isomorphism for `M` in `Loc(Dbc(X, Λ))` and `L` in
`Loc(Dbc(Y, Λ))`. Both sides are exact functors of each variable preserving direct sums, and the
projection map is compatible with the shifts in each variable
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift`), so this is the
two-variable determination argument
`CategoryTheory.NatTrans.isIso_app_app_of_localizingClosure` (blueprint
`lemma-checking-isomorphisms-constructible-complexes--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- The derived pullback maps `Loc(Dbc(Y, Λ))` into `Loc(Dbc(X, Λ))` if it maps `Dbc(Y, Λ)` into
`Dbc(X, Λ)`: it is exact and preserves direct sums. -/
lemma localizingBoundedConstructible_leftDerivedUpperStar
    (hpull : ∀ L : 𝔻(Y), boundedConstructible (condensedRingObj Λ Y) L →
      boundedConstructible (condensedRingObj Λ X) (L((p)^*⟦Λ⟧).obj L))
    {L : 𝔻(Y)} (hL : localizingBoundedConstructible Λ Y L) :
    localizingBoundedConstructible Λ X (L((p)^*⟦Λ⟧).obj L) :=
  ObjectProperty.localizingClosure_map _ _ L((p)^*⟦Λ⟧)
    (Functor.preservesCoproductsOn_of_preservesColimitsOfShape _ _)
    (fun L' hL' ↦ le_localizingBoundedConstructible Λ X _ (hpull L' hL')) hL

/-- The formal part of blueprint `proposition-projection-formula-rational-coefficients--2` and
`lemma-projection-formula-integral-coefficients--1` (2), for an arbitrary condensed ring `Λ`: the
projection formula extends from `Dbc` to `Loc(Dbc)`.

Assume that the projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` is an isomorphism for `M` in
`Dbc(X, Λ)` and `L` in `Dbc(Y, Λ)`, that `Rp_*` maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and
preserves direct sums there, that `Lp^*` maps `Dbc(Y, Λ)` into `Dbc(X, Λ)` and that `Dbc(X, Λ)`
is closed under `⊗ᴸ`. Then the projection map is an isomorphism for `M` in `Loc(Dbc(X, Λ))` and
`L` in `Loc(Dbc(Y, Λ))`. First fix `L` in `Dbc(Y, Λ)`: both sides are exact functors of `M`
preserving direct sums on `Loc(Dbc(X, Λ))` and the map is an isomorphism on `Dbc(X, Λ)`, hence on
`Loc(Dbc(X, Λ))`; then fix `M` in `Loc(Dbc(X, Λ))` and argue in the same way in `L`. -/
theorem isIso_projectionMap_of_localizingBoundedConstructible
    (hpush : ∀ M : 𝔻(X), localizingBoundedConstructible Λ X M →
      localizingBoundedConstructible Λ Y (R((p)_*⟦Λ⟧).obj M))
    (hsum : R((p)_*⟦Λ⟧).PreservesCoproductsOn.{u + 1} (localizingBoundedConstructible Λ X))
    (hpull : ∀ L : 𝔻(Y), boundedConstructible (condensedRingObj Λ Y) L →
      boundedConstructible (condensedRingObj Λ X) (L((p)^*⟦Λ⟧).obj L))
    (htensor : ∀ A B : 𝔻(X), boundedConstructible (condensedRingObj Λ X) A →
      boundedConstructible (condensedRingObj Λ X) B →
        boundedConstructible (condensedRingObj Λ X) (A ⊗ B))
    (hPF : ∀ (M : 𝔻(X)) (L : 𝔻(Y)), boundedConstructible (condensedRingObj Λ X) M →
      boundedConstructible (condensedRingObj Λ Y) L → IsIso (((projectionMap Λ p).app M).app L))
    {M : 𝔻(X)} {L : 𝔻(Y)} (hM : localizingBoundedConstructible Λ X M)
    (hL : localizingBoundedConstructible Λ Y L) :
    IsIso (((projectionMap Λ p).app M).app L) := by
  have : ∀ M : 𝔻(X), NatTrans.CommShift ((projectionMap Λ p).app M) ℤ :=
    commShift_projectionMap_app Λ p
  have : ∀ L : 𝔻(Y), NatTrans.CommShift (NatTrans.flipApp (projectionMap Λ p) L) ℤ :=
    commShift_projectionMap_flipApp Λ p
  have htensor' {A B : 𝔻(X)} (hA : localizingBoundedConstructible Λ X A)
      (hB : localizingBoundedConstructible Λ X B) : localizingBoundedConstructible Λ X (A ⊗ B) :=
    localizingBoundedConstructible_tensor Λ htensor hA hB
  refine NatTrans.isIso_app_app_of_localizingClosure (projectionMap Λ p)
    (P := boundedConstructible (condensedRingObj Λ X))
    (P' := boundedConstructible (condensedRingObj Λ Y)) ?_ ?_ ?_ ?_ hPF hM hL
  · exact fun L _ ↦ hsum.comp (preservesCoproductsOn_tensorRight Λ L _)
      (fun M hM ↦ hpush M hM)
  · exact fun L hL ↦ (preservesCoproductsOn_tensorRight Λ _ _).comp hsum
      (fun M hM ↦ htensor' hM (le_localizingBoundedConstructible Λ X _ (hpull L hL)))
  · exact fun M _ ↦ Functor.preservesCoproductsOn_of_preservesColimitsOfShape
      ((curriedTensor 𝔻(Y)).obj (R((p)_*⟦Λ⟧).obj M)) _
  · intro M hM
    exact ((Functor.preservesCoproductsOn_of_preservesColimitsOfShape L((p)^*⟦Λ⟧) _).comp
      (Functor.preservesCoproductsOn_of_preservesColimitsOfShape ((curriedTensor 𝔻(X)).obj M) _)
      (fun L hL ↦ localizingBoundedConstructible_leftDerivedUpperStar Λ p hpull hL)).comp hsum
      (fun L hL ↦ htensor' hM (localizingBoundedConstructible_leftDerivedUpperStar Λ p hpull hL))

end AlgebraicGeometry.ProEtale.CondensedRing
