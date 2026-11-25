/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.PairingComparison
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# Finite reduction of the Poincaré pairing

Let `a : X ⟶ Y` admit a compactification, and let `G : D(Y_ét, A) ⥤ D(Y_ét, A')` be a change of
coefficients on the base, lax monoidal (for the finite reduction `A_{E,n} → A_{E,m}` it is the
derived reduction `- ⊗ᴸ_{A_n} A_m`). Suppose that the derived Poincaré pairings `β_K` over `A` and
`β_{K'}` over `A'` (for `K'` the reduction of `K`) are identified by comparison maps
`c_X : Ra_! K' ⟶ G(Ra_! K)` (compact support), `c_Y : G(RΓ(K^∨(d))[2d]) ⟶ RΓ(K'^∨(d))[2d]`
(ordinary global sections) and `e : G Λ ⟶ Λ'`. Then the square of the inverses of the
tensor–internal-hom adjoints of the pairings commutes, and the comparison on ordinary global
sections is an isomorphism as soon as the comparison of the duals of the compactly supported
cohomology is. This is blueprint `theorem-poincare-duality--9`.

## Main statements

- `AlgebraicGeometry.Etale.map_inv_curry_poincarePairing_comp` (`theorem-poincare-duality--9`).
- `AlgebraicGeometry.Etale.isIso_of_map_poincarePairing` (`theorem-poincare-duality--9`).

## Implementation notes

As for the other compatibilities with changes of coefficients in the repository (see
`WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` and
`AlgebraicGeometry.Etale.derivedHomRightDerivedLowerShriekIso_hom_app_comp_mateEquiv`), the
coefficient comparison maps are parameters: no derived change-of-coefficients functor between
étale derived categories over different rings is constructed. The identification of the two
pairings through them is the composite of the coefficient compatibilities of the cup product,
the evaluation and the trace (blueprints `proposition-six-operations-change-coefficients` and
`proposition-compatibility-purity-change-coefficients`), and it is the hypothesis `h` below.
-/

@[expose] public section

universe u' u'' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {A' : Type u''} [Category.{u + 1} A'] [Abelian A'] [IsGrothendieckAbelian.{u + 1} A']
  [MonoidalCategory A'] [MonoidalPreadditive A'] [SymmetricCategory A'] [MonoidalClosed A']
  [Abelian.HasFunctorialFlatResolution A']
  {FA' : A' → A' → Type (u + 1)} {CA' : A' → Type (u + 1)}
  [∀ X Y, FunLike (FA' X Y) (CA' X) (CA' Y)] [ConcreteCategory.{u + 1} A' FA']
  [Etale.UpperStarPreservesFlat A']
  [(CategoryTheory.forget A').ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A')]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A')]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

variable {X Y : Scheme.{u}} {a : X ⟶ Y} [HasCompactification a] {P : 𝐃(Y, A) ⥤ 𝐃(X, A)}
  (adj : R(a)_![A] ⊣ P) {P' : 𝐃(Y, A') ⥤ 𝐃(X, A')} (adj' : R(a)_![A'] ⊣ P')
  (G : 𝐃(Y, A) ⥤ 𝐃(Y, A')) [G.LaxMonoidal] {d : ℕ}
  {T : 𝐃(X, A)} {T' : 𝐃(X, A')} (γ : T⟦(2 * d : ℤ)⟧ ≅ P.obj (𝟙_ _))
  (γ' : T'⟦(2 * d : ℤ)⟧ ≅ P'.obj (𝟙_ _)) {K : 𝐃(X, A)} {K' : 𝐃(X, A')}

/-- Blueprint `theorem-poincare-duality--9`: Finite reduction of the Poincaré pairing.

Let `G : D(Y_ét, A) ⥤ D(Y_ét, A')` be a lax monoidal change of coefficients (the finite
reduction `A_n → A_m`), `K` over `A` and `K'` over `A'` perfect, and assume the projection
formula for both. Suppose the coefficient comparisons
`c_X : Ra_! K' ⟶ G(Ra_! K)`, `c_Y : G(Ra_*(K^∨ ⊗ᴸ T)[2d]) ⟶ Ra_*(K'^∨ ⊗ᴸ T')[2d]` and
`e : G Λ_Y ⟶ Λ'_Y` identify the reduction of the derived Poincaré pairing `β_K` with `β_{K'}`
(hypothesis `h`). Then the square
```
G(RΓ_c(X, K)^∨) ──G(β_K^♯)⁻¹──▶ G(RΓ(X, K^∨(d))[2d])
       │                                 │
       │ dual comparison                 │ c_Y
       ▼                                 ▼
RΓ_c(X, K')^∨ ─────(β_{K'}^♯)⁻¹───▶ RΓ(X, K'^∨(d))[2d]
```
of the inverses of the tensor–internal-hom adjoints commutes, where the dual comparison is
`CategoryTheory.MonoidalClosed.unitDualComparison G c_X e`. -/
theorem map_inv_curry_poincarePairing_comp (hK : IsDualizable K) (hK' : IsDualizable K')
    (hPF : ∀ N, HasProjectionFormula A a K N) (hPF' : ∀ N, HasProjectionFormula A' a K' N)
    (cX : (R(a)_![A']).obj K' ⟶ G.obj ((R(a)_![A]).obj K))
    (cY : G.obj (((R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      ((R((a)_*[A'])).obj (((derivedTensor A' X).obj
        ((DerivedCategory.coefficientDual A' X).obj (op K'))).obj T'))⟦(2 * d : ℤ)⟧)
    (e : G.obj (𝟙_ _) ⟶ 𝟙_ _)
    (h : (R(a)_![A']).obj K' ◁ cY ≫ poincarePairing adj' γ' K' =
      cX ▷ _ ≫ μ G _ _ ≫ G.map (poincarePairing adj γ K) ≫ e) :
    G.map (isPerfectPairing_poincarePairing_of_hasProjectionFormula A a adj γ hK hPF).iso.inv ≫ cY =
      unitDualComparison G cX e ≫
        (isPerfectPairing_poincarePairing_of_hasProjectionFormula A' a adj' γ' hK' hPF').iso.inv :=
  map_inv_curry_comp G _ _ cX cY e h

/-- Blueprint `theorem-poincare-duality--9`: Finite reduction of the Poincaré pairing, the
comparison on ordinary global sections is an isomorphism.

In the situation of `AlgebraicGeometry.Etale.map_inv_curry_poincarePairing_comp`, if the
comparison `G(RΓ_c(X, K)^∨) ⟶ RΓ_c(X, K')^∨` of the duals is an isomorphism (in the blueprint:
`RΓ_c(X, K)` is perfect, `lemma-perfect-complexes-geometric-point`, so its dual commutes with
reduction), then the comparison `c_Y : G(RΓ(X, K^∨(d))[2d]) ⟶ RΓ(X, K'^∨(d))[2d]` on ordinary global
sections is an isomorphism. -/
theorem isIso_of_map_poincarePairing (hK : IsDualizable K) (hK' : IsDualizable K')
    (hPF : ∀ N, HasProjectionFormula A a K N) (hPF' : ∀ N, HasProjectionFormula A' a K' N)
    (cX : (R(a)_![A']).obj K' ⟶ G.obj ((R(a)_![A]).obj K))
    (cY : G.obj (((R((a)_*[A])).obj (((derivedTensor A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op K))).obj T))⟦(2 * d : ℤ)⟧) ⟶
      ((R((a)_*[A'])).obj (((derivedTensor A' X).obj
        ((DerivedCategory.coefficientDual A' X).obj (op K'))).obj T'))⟦(2 * d : ℤ)⟧)
    (e : G.obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso (unitDualComparison G cX e)]
    (h : (R(a)_![A']).obj K' ◁ cY ≫ poincarePairing adj' γ' K' =
      cX ▷ _ ≫ μ G _ _ ≫ G.map (poincarePairing adj γ K) ≫ e) :
    IsIso cY :=
  isIso_of_map_curry_comp_unitDualComparison G
    (isPerfectPairing_poincarePairing_of_hasProjectionFormula A a adj γ hK hPF)
    (isPerfectPairing_poincarePairing_of_hasProjectionFormula A' a adj' γ' hK' hPF') cX cY e h

end Etale

end AlgebraicGeometry
