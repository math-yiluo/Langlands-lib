/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.Basic

/-!
# The base change property `BC(f, n, q₀)`

For a morphism `f : X ⟶ S`, an integer `n ≥ 1` and `q₀`, the property `BC(f, n, q₀)` of the
Künneth chapter says that for every base change `f' : X' ⟶ S'` of `f`, every quasi-compact
quasi-separated `g : T ⟶ S'` with base change `Y = X' ×_{S'} T`, and every sheaf `F` of
`ℤ/n`-modules on `T_ét`, the exchange morphism `f'^* Rg_* F ⟶ Rh_* e^* F` is an isomorphism on
cohomology sheaves in degrees `q ≤ q₀`
(`AlgebraicGeometry.Etale.KunnethBaseChangeProperty`, blueprint
`lemma-kunneth-finite-direct-image--1`).

It is the universal base change property `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`
of the smooth base change chapter, for the coefficients `ℤ/n` and all degrees `q ≤ q₀`. The
coefficients `ℤ/n` are read as `ULift (ZMod n)`, so that their modules live in the universe of
étale sheaves; sheaves of `ℤ/n`-modules are the abelian sheaves annihilated by `n`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Etale

variable {X S : Scheme.{u}}

/-- Blueprint `lemma-kunneth-finite-direct-image--1`: the base change property `BC(f, n, q₀)`.

`BC(f, n, q₀)` holds if for every base change `f' : X' ⟶ S'` of `f` along some `S' ⟶ S`, every
quasi-compact quasi-separated `g : T ⟶ S'`, the cartesian square `Y = X' ×_{S'} T` with
projections `e : Y ⟶ T`, `h : Y ⟶ X'`, every sheaf `F` of `ℤ/n`-modules on `T_ét` (an abelian
sheaf annihilated by `n`) and every `q ≤ q₀`, the exchange morphism `f'^* Rg_* F ⟶ Rh_* e^* F`
is an isomorphism on `q`-th cohomology sheaves, i.e. the base change map
`f'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of `AlgebraicGeometry.Etale.baseChangeHomologyMap` is an
isomorphism. The integer `n` is not required to be invertible on `S`. The unfolded form is
`AlgebraicGeometry.Etale.kunnethBaseChangeProperty_iff`, and the form with the unbounded exchange
morphism is `AlgebraicGeometry.Etale.kunnethBaseChangeProperty_iff_unboundedExchange`. -/
def KunnethBaseChangeProperty (f : X ⟶ S) (n : ℕ) (q₀ : ℤ) : Prop :=
  ∀ q ≤ q₀, Etale.UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f q

/-- The unfolded form of the base change property `BC(f, n, q₀)` of
`AlgebraicGeometry.Etale.KunnethBaseChangeProperty`: for every diagram of cartesian squares

```
Y --h--> X' --b--> X
|        |         |
e        f'        f
v        v         v
T --g--> S' --a--> S
```

with `g` quasi-compact and quasi-separated, every sheaf `F` of `ℤ/n`-modules on `T_ét` and every
`q ≤ q₀`, the degree-`q` base change map `f'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism. -/
lemma kunnethBaseChangeProperty_iff (f : X ⟶ S) (n : ℕ) (q₀ : ℤ) :
    KunnethBaseChangeProperty f n q₀ ↔
      ∀ ⦃S' X' T Y : Scheme.{u}⦄ (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S'),
        IsPullback b f' f a → ∀ (g : T ⟶ S') (e : Y ⟶ T) (h : Y ⟶ X') [QuasiCompact g]
          [QuasiSeparated g] (sq : IsPullback e h g f')
          (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (q : ℤ),
          q ≤ q₀ → IsIso (Etale.baseChangeHomologyMap _ sq q F) :=
  ⟨fun H _ _ _ _ a b f' hf g e h _ _ sq F q hq ↦ H q hq a b f' hf g e h sq F,
    fun H q hq _ _ a b f' hf _ _ g e h _ _ sq F ↦ H a b f' hf g e h sq F q hq⟩

open _root_.DerivedCategory in
/-- The base change property `BC(f, n, q₀)` in terms of the unbounded exchange morphism
`AlgebraicGeometry.Etale.unboundedExchange` (`definition-derived-base-change-map`): it holds if and
only if, for every diagram as in `AlgebraicGeometry.Etale.kunnethBaseChangeProperty_iff` and every
sheaf `F` of `ℤ/n`-modules on `T_ét`, the exchange morphism `f'^* Rg_* F ⟶ Rh_* e^* F` induces
isomorphisms on the cohomology sheaves in degrees `q ≤ q₀`. -/
lemma kunnethBaseChangeProperty_iff_unboundedExchange (f : X ⟶ S) (n : ℕ) (q₀ : ℤ) :
    KunnethBaseChangeProperty f n q₀ ↔
      ∀ ⦃S' X' T Y : Scheme.{u}⦄ (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S'),
        IsPullback b f' f a → ∀ (g : T ⟶ S') (e : Y ⟶ T) (h : Y ⟶ X') [QuasiCompact g]
          [QuasiSeparated g] (sq : IsPullback e h g f')
          (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (q : ℤ),
          q ≤ q₀ → IsIso ((homologyFunctor _ q).map (Etale.unboundedExchange _ sq.toCommSq
            (Plus.ι.obj ((Plus.singleFunctor _ 0).obj F)))) := by
  rw [kunnethBaseChangeProperty_iff]
  simp only [Etale.isIso_baseChangeHomologyMap_iff_isIso_homology_unboundedExchange]

end Etale

end AlgebraicGeometry
