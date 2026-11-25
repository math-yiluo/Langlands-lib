/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ProjectionPairing
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The derived Poincaré pairing

Let `a : X ⟶ Y` be a morphism admitting a compactification and `γ : T[2d] ≅ Ra^! Λ_Y` a purity
isomorphism, as given by an orientation of `a` of relative dimension `d` with twist
`T = Λ_X(d)`. The derived Poincaré pairing is assembled from three ingredients:

* the *mixed-support cup product* `⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`, the projection map
  of `Ra_!` followed by the counit `La^* Ra_* L ⟶ L`;
* the *evaluation* `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X`
  (`AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`);
* the *smooth trace* `Tr_γ : Ra_!(T[2d]) ⟶ Λ_Y`, the counit of `Ra_! ⊣ Ra^!` read through
  `γ`.

Composing them gives the *derived Poincaré pairing*

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

which over `Y = Spec k` is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`. It is perfect for `K`
perfect as soon as the projection formula for `Ra_!` holds at `K`; in particular at finite
coefficients `ModuleCat Λ`, where the projection formula is available.

## Main definitions

- `AlgebraicGeometry.Etale.mixedSupportCupProduct` (`theorem-poincare-duality--6`,
`theorem-global-verdier-duality--3`,
  `theorem-global-verdier-duality--3`): `⌣_c`.
- `AlgebraicGeometry.Etale.smoothTrace` (`theorem-poincare-duality--6`): `Tr_o`.
- `AlgebraicGeometry.Etale.poincarePairing` (`definition-perfect-pairing`,
`theorem-poincare-duality--6`,
  `theorem-poincare-duality--6`): `β_K`.
- `AlgebraicGeometry.Etale.properPoincarePairing`: `β_K` read through `Ra_! ≅ Ra_*` for proper
  `a`.
- `AlgebraicGeometry.Etale.poincarePairingOfTrace`: the pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ T` of a trace `(Ra_! Λ_X)[n] ⟶ T`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`
  (`theorem-poincare-duality--7`): the derived Poincaré pairing `β_K` of a perfect `K` is perfect,
  provided the projection formula holds at a class of test objects detecting isomorphisms.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_hasProjectionFormula`
  (`theorem-poincare-duality--7`): the same with all objects as test objects.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`
(`corollary-degreewise-duality-over-fields`): at
  finite coefficients, the derived Poincaré pairing of an orientation is perfect for `K`
  dualizable.
- `AlgebraicGeometry.Etale.isPerfectPairing_properPoincarePairing`
  (`theorem-poincare-duality--8`): the same for the pairing of a proper morphism read
  through `Ra_! ≅ Ra_*`.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed`
  (`theorem-poincare-duality--7`): over a separably closed field, `β_K` is perfect in the point
  category as soon as the projection formula holds at the shifts `Λ_s[r]`, which detect
  isomorphisms there (`theorem-poincare-duality`).

## Implementation notes

The definitions take the shape of a purity isomorphism as an argument: an isomorphism
`γ : T[2d] ≅ Ra^! Λ_Y = ω_X` for an object `T` of `D(X_ét)`. An orientation `o`
(`AlgebraicGeometry.Etale.Orientation`), with twist the Tate twist `T = Λ_X(d)`, provides it as
`o.dualizingComplexIso e` for an identification `e : La^* Λ_Y ≅ Λ_X`, which exists
(`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_unit`); for `A = ModuleCat Λ` with a
Tate twist datum it is `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`.

The exceptional inverse image enters only through the adjunction `Ra_! ⊣ Ra^!`, so the smooth
trace and the pairing are defined for an arbitrary adjunction `adj : Ra_! ⊣ G`, with
`γ : T[2d] ≅ G Λ_Y`: at a finite coefficient ring `Λ` it is
`AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction`, and for other coefficients (such as
the integral stage `𝒪_E`) any right adjoint of `Ra_!`, e.g. `Adjunction.ofIsLeftAdjoint`.

The proof of perfectness is the formal Yoneda argument of the blueprint, isolated in
`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`. It is applied to `β_K` by
unification after unfolding the definition of `β_K`, so that the kernel never has to compare
`β_K` with a re-elaborated copy of it (such comparisons time out).

All objects are written with `AlgebraicGeometry.Etale.derivedTensor` rather than `⊗`, so that
the definitions can be specialised to `A = ModuleCat Λ` and composed there with other maps
written with `derivedTensor`; see `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a] {d : ℕ}
  {G : 𝐃(Y, A) ⥤ 𝐃(X, A)} (adj : R(a)_![A] ⊣ G)

/-- Blueprint `theorem-poincare-duality--6`: The pairing data. This is also blueprint
`theorem-global-verdier-duality--3` (Mixed-support cup product) and blueprint
`theorem-global-verdier-duality--3` (Mixed-support cup product, at the finite stage).

The *mixed-support cup product* of the pairing data,

`⌣_c : Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, L) ⟶ RΓ_c(X, K ⊗ᴸ L)` read in `D(Y_ét)`: the projection map of
`Ra_!` followed by `Ra_!` of `K ⊗ᴸ ε_L`, for the counit `ε_L : La^* Ra_* L ⟶ L` of
`La^* ⊣ Ra_*`,
```
                       projection map                              Ra_!(K ⊗ᴸ ε_L)
Ra_! K ⊗ᴸ Ra_* L ───────────────────────▶ Ra_!(K ⊗ᴸ La^* Ra_* L) ─────────────────▶ Ra_!(K ⊗ᴸ L)
```
-/
noncomputable def mixedSupportCupProduct (K L : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj ((R((a)_*[A])).obj L) ⟶
      (R(a)_![A]).obj (((derivedTensor A X).obj K).obj L) :=
  ((projectionMap A a).app K).app ((R((a)_*[A])).obj L) ≫
    (R(a)_![A]).map (((derivedTensor A X).obj K).map
      ((derivedUpperStarLowerStarAdjunction A a).counit.app L))

variable {A a}

/-- Blueprint `theorem-poincare-duality--6`: The pairing data.

The *smooth trace* of the pairing data, `Tr_γ : Ra_!(T[2d]) ⟶ Λ_Y` for a right adjoint `G` of
`Ra_!` (for finite coefficients, `G = Ra^!`) and an isomorphism `γ : T[2d] ≅ G Λ_Y` (for an
orientation `o`, `γ = o.dualizingComplexIso e` with `T = Λ_X(d)`): the counit of
`Ra_! ⊣ G` at `Λ_Y`, read through `γ`,
```
               Ra_!(γ)                  counit
Ra_!(T[2d]) ─────────▶ Ra_! G Λ_Y ──────────▶ Λ_Y
```
It is the normalized trace of the blueprint when `γ` comes from the normalized orientation. -/
noncomputable def smoothTrace {T : 𝐃(X, A)} (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) :
    (R(a)_![A]).obj (T⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (R(a)_![A]).map γ.hom ≫ adj.counit.app (𝟙_ _)

/-- The *twisted evaluation* `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` for an object `T` of `D(X_ét)`,
```
                     α⁻¹                         ev_K ⊗ᴸ T                  λ
K ⊗ᴸ (K^∨ ⊗ᴸ T) ─────────▶ (K ⊗ᴸ K^∨) ⊗ᴸ T ───────────────▶ Λ_X ⊗ᴸ T ─────▶ T
```
For `T = Λ_X(d)` it is `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`. -/
noncomputable def twistedEvaluation (T K : 𝐃(X, A)) :
    ((derivedTensor A X).obj K).obj
        (((derivedTensor A X).obj ((DerivedCategory.coefficientDual A X).obj (op K))).obj T) ⟶
      T :=
  (derivedTensorAssociator A X _ _ _).inv ≫
    ((derivedTensor A X).map (DerivedCategory.coefficientEvaluation K)).app T ≫
      (derivedTensorLeftUnitor A X T).hom

variable (a)

/-- The unshifted core of the derived Poincaré pairing,
```
                          ⌣_c                                Ra_!(twisted evaluation)
Ra_! K ⊗ᴸ Ra_*(K^∨ ⊗ᴸ T) ─────▶ Ra_!(K ⊗ᴸ (K^∨ ⊗ᴸ T)) ────────────────────────────▶ Ra_! T
```
-/
noncomputable def poincarePairingEvaluation (T K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        ((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T)) ⟶
      (R(a)_![A]).obj T :=
  mixedSupportCupProduct A a _ _ ≫ (R(a)_![A]).map (twistedEvaluation T K)

variable {a} in
/-- Blueprint `definition-perfect-pairing`: The derived pairing, and perfectness of a pairing. This
is also blueprint `theorem-poincare-duality--6` and `theorem-poincare-duality--6` (Derived Poincaré
pairing); perfectness of a pairing is `AlgebraicGeometry.Etale.IsPerfectPairing`.

The *derived Poincaré pairing* of a purity isomorphism `γ : T[2d] ≅ G Λ_Y`, for a right
adjoint `G` of `Ra_!` (for finite coefficients, `G = Ra^!`, and `G Λ_Y = ω_X`),

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` read in `D(Y_ét)`: the shift is moved out, then
come the mixed-support cup product, `Ra_!` of the twisted evaluation, the shift compatibility
of `Ra_!` and the smooth trace,
```
                              shift out                                    (⌣_c)[2d]
Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ─────────▶ (Ra_! K ⊗ᴸ Ra_*(K^∨ ⊗ᴸ T))[2d] ──────────▶
                                   (Ra_!(ev))[2d]                ≅                      Tr_o
  (Ra_!(K ⊗ᴸ (K^∨ ⊗ᴸ T)))[2d] ─────────────────▶ (Ra_! T)[2d] ─────▶ Ra_!(T[2d]) ──────▶ Λ_Y
```
The blueprint asks `K` to be perfect over `Λ_X`; the composite makes sense for every `K`. -/
noncomputable def poincarePairing {T : 𝐃(X, A)} (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    (K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (poincarePairingEvaluation a T K)⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![A]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ smoothTrace adj γ

section Proper

variable [IsProper a]

variable {a} in
/-- The derived Poincaré pairing of a proper morphism `a`, read through the identification
`Ra_! ≅ Ra_*` of `AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`:

`Ra_* K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`,

that is `RΓ(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` over `Y = Spec k`, for a purity isomorphism
`γ : T[2d] ≅ G Λ_Y`. -/
noncomputable def properPoincarePairing {T : 𝐃(X, A)}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)) (K : 𝐃(X, A)) :
    ((derivedTensor A Y).obj ((R((a)_*[A])).obj K)).obj
        (((R((a)_*[A])).obj (((derivedTensor A X).obj
          ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  (rightDerivedLowerShriekIsoRightDerivedLowerStar A a).inv.app K ▷ _ ≫ poincarePairing adj γ K

omit [HasSmallSiteSheafify A] in
variable {a adj} in
/-- If the derived Poincaré pairing of a proper morphism is perfect, so is the pairing
`AlgebraicGeometry.Etale.properPoincarePairing` read through `Ra_! ≅ Ra_*`. -/
theorem IsPerfectPairing.properPoincarePairing {T : 𝐃(X, A)}
    {γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _)} {K : 𝐃(X, A)}
    (h : IsPerfectPairing (poincarePairing adj γ K)) :
    IsPerfectPairing (properPoincarePairing adj γ K) :=
  MonoidalClosed.IsPerfectPairing.whiskerRight_comp h _

end Proper

/-- The *pairing of a trace* `t : (Ra_! Λ_X)[n] ⟶ T`,

`Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ T`:

the shift is moved out, then come the mixed-support cup product, `Ra_!` of the evaluation
`ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` and `t`,
```
                          shift out                             (⌣_c)[n]
Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ─────────▶ (Ra_! K ⊗ᴸ Ra_* K^∨)[n] ─────────▶
                                (Ra_!(ev_K))[n]                t
  (Ra_!(K ⊗ᴸ K^∨))[n] ─────────────────▶ (Ra_! Λ_X)[n] ──────▶ T
```
For the untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)` of a Tate orientation this is the
untwisted, line-valued Poincaré pairing
(`AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`). -/
noncomputable def poincarePairingOfTrace (K : 𝐃(X, A)) {T : 𝐃(Y, A)} (n : ℤ)
    (t : ((R(a)_![A]).obj (𝟙_ _))⟦n⟧ ⟶ T) :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).obj
        (((R((a)_*[A])).obj ((DerivedCategory.coefficientDual A X).obj (op K)))⟦n⟧) ⟶ T :=
  ((((derivedTensor A Y).obj ((R(a)_![A]).obj K)).commShiftIso n).hom.app _ ≫
    (mixedSupportCupProduct A a K _ ≫
      (R(a)_![A]).map (DerivedCategory.coefficientEvaluation K))⟦n⟧') ≫ t

section Perfectness

variable (A)

omit [ConcreteCategory A FA] [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] in
/-- For a perfect `K`, the twisted evaluation `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` is a counit: every map
`K ⊗ᴸ Z ⟶ T` factors uniquely as `K ⊗ᴸ y` followed by the twisted evaluation, for a map
`y : Z ⟶ K^∨ ⊗ᴸ T`. In other words `K^∨ ⊗ᴸ T` is the internal hom `RHom(K, T)`. -/
theorem bijective_derivedTensor_map_comp_twistedEvaluation
    {T K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (Z : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Function.Bijective (fun y : Z ⟶ ((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T ↦
      ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  have hi : IsIso (MonoidalClosed.ihomUnitTensorToIhom K T) :=
    MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K T
  have ht : twistedEvaluation T K =
      MonoidalClosed.uncurry (MonoidalClosed.ihomUnitTensorToIhom K T) := by
    rw [MonoidalClosed.ihomUnitTensorToIhom, MonoidalClosed.uncurry_curry]
    rfl
  have he : (fun y : Z ⟶ ((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T ↦
      ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) =
      MonoidalClosed.uncurry ∘ (fun y ↦ y ≫ MonoidalClosed.ihomUnitTensorToIhom K T) := by
    funext y
    rw [ht]
    exact (MonoidalClosed.uncurry_natural_left _ _).symm
  rw [he]
  exact Function.Bijective.comp ⟨MonoidalClosed.uncurry_injective,
    fun g ↦ ⟨MonoidalClosed.curry g, MonoidalClosed.uncurry_curry g⟩⟩
    ((isIso_iff_yoneda_map_bijective _).1 hi _)

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] [HasCompactification a] in
/-- The adjoint description of the evaluation part of the derived Poincaré pairing: for `K`
perfect and any `N`, maps `h : N ⟶ Ra_*(K^∨ ⊗ᴸ T)` correspond bijectively to maps
`K ⊗ᴸ La^* N ⟶ T`, through `K ⊗ᴸ La^* h`, `K ⊗ᴸ` the counit of `La^* ⊣ Ra_*` and the twisted
evaluation. -/
theorem bijective_derivedTensor_map_comp_counit_comp_twistedEvaluation {T : 𝐃(X, A)}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    Function.Bijective (fun h : N ⟶ (R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          twistedEvaluation T K) := by
  have e : (fun h : N ⟶ (R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T) ↦
      ((derivedTensor A X).obj K).map ((L((a)^*[A])).map h) ≫
        ((derivedTensor A X).obj K).map ((derivedUpperStarLowerStarAdjunction A a).counit.app _) ≫
          twistedEvaluation T K) =
      (fun y ↦ ((derivedTensor A X).obj K).map y ≫ twistedEvaluation T K) ∘
        ((derivedUpperStarLowerStarAdjunction A a).homEquiv _ _).symm := by
    funext h
    simp [Adjunction.homEquiv_counit]
  rw [e]
  exact (bijective_derivedTensor_map_comp_twistedEvaluation A hK _).comp (Equiv.bijective _)

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- The trace part of the derived Poincaré pairing is a counit: maps `z : U ⟶ T` correspond
bijectively to maps `Ra_!(U[2d]) ⟶ Λ_Y`, through `Ra_!(z[2d])` followed by the smooth trace
`Tr_o`. This is the adjunction `Ra_! ⊣ G` read through `T[2d] ≅ G Λ_Y`. -/
theorem bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace {T : 𝐃(X, A)}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    (U : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Function.Bijective (fun z : U ⟶ T ↦ (R(a)_![A]).map (z⟦(2 * d : ℤ)⟧') ≫
      smoothTrace adj γ) := by
  have e' : (fun z : U ⟶ T ↦ (R(a)_![A]).map (z⟦(2 * d : ℤ)⟧') ≫ smoothTrace adj γ) =
      (adj.homEquiv _ _).symm ∘
        (fun z' ↦ z' ≫ γ.hom) ∘ (fun z ↦ z⟦(2 * d : ℤ)⟧') := by
    funext z
    simp only [Function.comp_apply, Adjunction.homEquiv_counit, smoothTrace, Functor.map_comp,
      Category.assoc]
  rw [e']
  exact (Equiv.bijective _).comp (((isIso_iff_yoneda_map_bijective _).1 inferInstance _).comp
    ⟨(shiftFunctor _ _).map_injective, (shiftFunctor _ _).map_surjective⟩)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `theorem-poincare-duality--7`: the pairing is the duality isomorphism.

**The derived Poincaré pairing is perfect.** Let `a : X ⟶ Y` admit a compactification, let
`γ : T[2d] ≅ Ra^! Λ_Y` be a purity isomorphism, and let `K` be perfect over
`Λ_X`. If the projection map `Ra_! K ⊗ᴸ N ⟶ Ra_!(K ⊗ᴸ La^* N)` is an isomorphism at every test
object `N` of a class `S` detecting isomorphisms after the shift by `2d`, then the derived
Poincaré pairing `β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.poincarePairing`) is perfect: its tensor–internal-hom adjoint
`(Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨` is an isomorphism.

Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`. Following the blueprint, the
adjoint is identified on test objects `N[2d]` with the chain of bijections
```
(N ⟶ Ra_*(K^∨ ⊗ᴸ T)) ≃ (La^* N ⟶ K^∨ ⊗ᴸ T) ≃ (K ⊗ᴸ La^* N ⟶ T) ≃ ((K ⊗ᴸ La^* N)[2d] ⟶ Ra^! Λ_Y)
  ≃ (Ra_!(K ⊗ᴸ La^* N)[2d] ⟶ Λ_Y) ≃ ((Ra_! K ⊗ᴸ N)[2d] ⟶ Λ_Y) ≃ (N[2d] ⟶ (Ra_! K)^∨)
```
given by the adjunctions `La^* ⊣ Ra_*`, `K ⊗ᴸ - ⊣ K^∨ ⊗ᴸ -`, `Ra_! ⊣ Ra^!`, the orientation
`T[2d] ≅ Ra^! Λ_Y` and the projection formula; see
`CategoryTheory.MonoidalClosed.isIso_curry_of_projection`.

This is only the "in particular, `β_K` is perfect" part of `theorem-poincare-duality--7`. The
identification of the inverse of the adjoint with the global-duality isomorphism composed with
`𝔻_X K ≅ K^∨(d)[2d]` is not formalised yet, since those isomorphisms are only known to exist
(`Nonempty`). -/
theorem isPerfectPairing_poincarePairing_of_isDetecting {T : 𝐃(X, A)}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (S : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) → Prop)
    (hS : ∀ ⦃P Q : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)⦄ (u : P ⟶ Q),
      (∀ N, S N → Function.Bijective (fun g : N⟦(2 * d : ℤ)⟧ ⟶ P ↦ g ≫ u)) → IsIso u)
    (hPF : ∀ N, S N → HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairing adj γ K) := by
  constructor
  rw [poincarePairing, poincarePairingEvaluation, mixedSupportCupProduct]
  exact MonoidalClosed.isIso_curry_of_projection _ _ _ _ _ _ _ _ _ S hS hPF
    (bijective_derivedTensor_map_comp_counit_comp_twistedEvaluation A a hK)
    (bijective_rightDerivedLowerShriek_map_shift_comp_smoothTrace A a adj γ)

omit [HasSmallSiteSheafify A] in
/-- Blueprint `theorem-poincare-duality--7`: the pairing is the duality isomorphism.

The derived Poincaré pairing of a perfect `K` is perfect whenever the projection formula
holds for `a` at `K` and every object of `D(Y_ét)`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting` with all objects as
test objects). -/
theorem isPerfectPairing_poincarePairing_of_hasProjectionFormula {T : 𝐃(X, A)}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (hPF : ∀ N, HasProjectionFormula A a K N) :
    IsPerfectPairing (poincarePairing adj γ K) :=
  isPerfectPairing_poincarePairing_of_isDetecting A a adj γ hK (fun _ ↦ True)
    (fun _ _ u hu ↦ isIso_of_bijective_comp_shift (2 * d : ℤ) u fun N ↦ hu N trivial)
    (fun N _ ↦ hPF N)

end Perfectness

section ModuleCat

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `theorem-poincare-duality--6`: Derived Poincaré duality, at a finite
coefficient stage `Λ = A`. This is also the derived part of blueprint
`corollary-degreewise-duality-over-fields`.

**The derived pairing is perfect.** For a finite coefficient ring `Λ`, a purity isomorphism
`γ : T[2d] ≅ Ra^! Λ_Y` of `a : X ⟶ Y` (from an orientation, with `T = Λ_X(d)`), and `K`
dualizable (perfect over `Λ_X`), the derived Poincaré pairing `β_K`
(`AlgebraicGeometry.Etale.poincarePairing`, for the adjunction `Ra_! ⊣ Ra^!`) is perfect: its
tensor–internal-hom adjoint

`(Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ (Ra_! K)^∨`

is an isomorphism. Over `Y = Spec k` this is `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`.

The blueprint also asks the exponent of `Λ` to be invertible on `Y` and `K` to lie in
`D^b_{ctf}(X, Λ)`; neither is needed once the purity isomorphism is given. The proof is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_hasProjectionFormula` together
with the projection formula at finite coefficients
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`). -/
theorem isPerfectPairing_poincarePairing {T : DerivedCategoryModule Λ X}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) {K : DerivedCategoryModule Λ X}
    (hKd : IsDualizable K) :
    IsPerfectPairing (poincarePairing (rightDerivedUpperShriekAdjunction Λ a) γ K) :=
  isPerfectPairing_poincarePairing_of_hasProjectionFormula _ a _ γ hKd fun N ↦
    hasProjectionFormula_of_finite Λ a K N

/-- Blueprint `theorem-poincare-duality--8`: Proper Poincaré duality.

For `a` proper, a finite coefficient ring `Λ` and `K` dualizable, the derived Poincaré pairing
read through `Ra_! ≅ Ra_*`,

`Ra_* K ⊗ᴸ (Ra_*(K^∨ ⊗ᴸ T))[2d] ⟶ Λ_Y`

(`AlgebraicGeometry.Etale.properPoincarePairing`), is perfect. Over `Y = Spec k` this is
`RΓ(X, K^∨(d))[2d] ≅ RΓ(X, K)^∨`. As for
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`, the blueprint hypotheses that the
exponent of `Λ` is invertible on `Y` and that `K ∈ D^b_{ctf}(X, Λ)` are not needed. -/
theorem isPerfectPairing_properPoincarePairing [IsProper a] {T : DerivedCategoryModule Λ X}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) {K : DerivedCategoryModule Λ X}
    (hKd : IsDualizable K) :
    IsPerfectPairing (properPoincarePairing (rightDerivedUpperShriekAdjunction Λ a) γ K) :=
  (isPerfectPairing_poincarePairing a Λ γ hKd).properPoincarePairing

end ModuleCat

section Point

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [HasCompactification a]
  {G : _root_.DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
  (adj : R(a)_![ModuleCat.{u + 1} Λ] ⊣ G) {d : ℕ}

/-- Blueprint `theorem-poincare-duality--7`: The derived Poincaré pairing is the duality
isomorphism.
This is also blueprint `theorem-poincare-duality--7` (Identification of the
Poincaré pairing with Verdier duality), the part asserting that `b_K^♯` is an isomorphism.

**The derived Poincaré pairing is perfect in the point category.** Let `k` be separably closed,
`a : X ⟶ Spec k` admit a compactification, `γ : V[2d] ≅ ω_X` be a purity isomorphism (from an
orientation of `a` of relative dimension `d`, with `V = Λ_X(d)`), and `K` be perfect over
`Λ_X`. If the projection formula holds for `a` at `K` and the shifts `Λ_s[r]` of the constant
complex of the point `s = Spec k`, then the tensor–internal-hom adjoint of the derived Poincaré
pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is an isomorphism `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨` of the point category; that is, `β_K` is
perfect. Following the blueprint, it suffices to check this after applying `Hom(Λ_s[r], -)`
for all `r` (`AlgebraicGeometry.Etale.isIso_iff_bijective_comp_of_isSepClosed`, blueprint
`theorem-poincare-duality`), and there the adjoint of `β_K` is identified with the chain of the
tensor–hom exchange (`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`).
-/
theorem isPerfectPairing_poincarePairing_of_isSepClosed
    {V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : V⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K)
    (hPF : ∀ r : ℤ, HasProjectionFormula (ModuleCat.{u + 1} Λ) a K
      (((_root_.DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
        (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))⟦r⟧)) :
    IsPerfectPairing (poincarePairing adj γ K) := by
  set T := (_root_.DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
    (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
  refine isPerfectPairing_poincarePairing_of_isDetecting _ a adj γ hK (fun N ↦ ∃ r : ℤ, N = T⟦r⟧)
    (fun P Q u hu ↦ ?_) (fun N ⟨r, hr⟩ ↦ hr ▸ hPF r)
  refine (isIso_iff_bijective_comp_of_isSepClosed u).2 fun r ↦ ?_
  let E : (T⟦r - 2 * d⟧)⟦(2 * d : ℤ)⟧ ≅ T⟦r⟧ :=
    ((shiftFunctorAdd' _ (r - 2 * d) (2 * d) r (by omega)).app T).symm
  have hc : (fun g : T⟦r⟧ ⟶ P ↦ g ≫ u) =
      (fun g ↦ E.inv ≫ g) ∘ (fun g : (T⟦r - 2 * d⟧)⟦(2 * d : ℤ)⟧ ⟶ P ↦ g ≫ u) ∘
        (fun g ↦ E.hom ≫ g) := by
    funext g
    simp
  rw [hc]
  exact ((isIso_iff_coyoneda_map_bijective E.inv).1 inferInstance _).comp
    ((hu _ ⟨r - 2 * d, rfl⟩).comp ((isIso_iff_coyoneda_map_bijective E.hom).1 inferInstance _))

/-- Blueprint `theorem-poincare-duality--6`: Derived Poincaré duality, at every
coefficient ring `Λ`, in particular at the integral stage `Λ = 𝒪_E`.

**The derived Poincaré pairing over a separably closed field is perfect.** Let `k` be
separably closed, `Λ` a commutative ring, `a : X ⟶ Spec k` admit a compactification for which
`Ra_!` has a right adjoint `Ra^!` (any right adjoint `G`, with adjunction `adj`),
`γ : V[2d] ≅ Ra^! Λ` a purity isomorphism (for `V = Λ_X(d)` the smooth purity orientation),
and `K` perfect over `Λ_X`. Then the derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

is perfect: its adjoint `RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨` is an isomorphism of the point
category `D(Spec k_ét, Λ)`.

The proof is that of `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`: perfectness
reduces to the projection formula at the objects `Λ_s[r]`, which detect isomorphisms at the
point (`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed`),
and it holds there for every coefficient ring, the `Λ_s[r]` being dualizable
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_isDualizable`). So, unlike
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`, no finiteness of `Λ` is used: at
`Λ = 𝒪_E` the only inputs are the right adjoint `Ra^!` and the purity isomorphism `γ` of the
`𝒪_E` stage. -/
theorem isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable
    {V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : V⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    IsPerfectPairing (poincarePairing adj γ K) :=
  isPerfectPairing_poincarePairing_of_isSepClosed a adj γ hK fun r ↦
    hasProjectionFormula_of_isDualizable _ a K
      (IsDualizable.of_iso ((shiftFunctor _ r).mapIso
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) (Spec (.of k))).symm)
        (DerivedCategory.isDualizable_of_isInvertible
          (DerivedCategory.isInvertible_shift isInvertible_unit r)))

end Point

end Etale

end AlgebraicGeometry
