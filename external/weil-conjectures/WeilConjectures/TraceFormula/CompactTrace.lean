/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# The complexes whose traces occur

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` with
structure morphism `a_X : X ⟶ Spec k`, and `Λ` a finite commutative ring whose exponent is
invertible in `k` (an `ℓ`-primary ring with `ℓ ≠ char k`). For `K ∈ Dctf(X, Λ)` the complexes
`RΓ_c(X, K)` and `K_x̄`, for `x̄` a geometric point of `X`, are perfect complexes of
`Λ`-modules, so the traces of their endomorphisms are defined
(`DerivedCategory.IsPerfect.categoricalTrace`). This is blueprint
`lemma-perfect-complexes-geometric-point`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleFiniteTor_rightDerivedLowerShriek_and_geometricStalk`
  (`lemma-perfect-complexes-geometric-point`): `Ra_{X!} K ∈ Dctf(Spec k, Λ)`, and every geometric
  stalk `K_x̄` is bounded with finitely generated cohomology and of finite Tor amplitude.
- `AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections_and_geometricStalk`
  (`lemma-perfect-complexes-geometric-point`, `lemma-perfect-complexes-geometric-point--1`):
  `RΓ_c(X, K)` and every `K_x̄` are perfect.

## Implementation notes

The algebraic statement `lemma-perfect-complexes-geometric-point--1` (a bounded complex over a
Noetherian, e.g. finite, ring with finitely generated cohomology and finite Tor amplitude is
perfect) is `DerivedCategory.isPerfect_of_finiteTorAmplitude` and is not restated here.

The geometric stalk of `K` at `x̄ : Spec Ω ⟶ X`, `Ω` separably closed, is
`RΓ(Spec Ω, Lx̄^* K)`, as in `AlgebraicGeometry.Etale.isPerfect_geometricStalk`. The
hypotheses "separated of finite type" on `a_X` are `LocallyOfFiniteType`, `QuasiCompact` and
`HasCompactification` (which forces separatedness); "`ℓ`-primary with `ℓ ≠ char k`" is
`HasInvertibleExponent Λ (Spec k)`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}

/-- Blueprint `lemma-perfect-complexes-geometric-point`: the point objects in the compact trace
lemma.

Let `k` be algebraically closed, `X` separated of finite type over `k` with structure morphism
`a_X`, `Λ` a finite ring whose exponent is invertible in `k` and `K ∈ Dctf(X, Λ)`. Then
`Ra_{X!} K` lies in `Dctf(Spec k, Λ)` (`proposition-six-operations-dctf`, clause (iv), for
`f = a_X`), and for every geometric point `x̄ : Spec Ω ⟶ X` the stalk `K_x̄ = RΓ(Spec Ω, Lx̄^* K)`
is a bounded complex of `Λ`-modules with finitely generated cohomology modules and finite Tor
amplitude: `Lx̄^*` preserves `Dctf`, and `RΓ` over the separably closed point `Spec Ω` is exact
and preserves finiteness and Tor amplitude. -/
theorem constructibleFiniteTor_rightDerivedLowerShriek_and_geometricStalk
    {k : Type u} [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) (Spec (.of k))
        ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K) ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        let C := (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
          ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K)
        _root_.DerivedCategory.TStructure.t.bounded C ∧
          (∀ i : ℤ, Module.Finite Λ
            ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj C)) ∧
          _root_.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) C := by
  refine ⟨constructibleFiniteTor_rightDerivedLowerShriek Λ (𝟙 _) aX hK, fun Ω _ _ x ↦ ?_⟩
  obtain ⟨⟨hb, hc⟩, a, b, hta⟩ := constructibleFiniteTor_leftDerivedUpperStar _ x hK
  obtain ⟨c, d, hcd⟩ := (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).2 hb
  exact ⟨(_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded _).1
      ⟨c, d, homologyConcentratedIn_rightDerivedGlobalSections_of_isSepClosed _ hcd⟩,
    fun i ↦ moduleFinite_homology_rightDerivedGlobalSections_of_isSepClosed _ i
      (Scheme.IsConstructibleSheaf.isFiniteSheaf (hc i)),
    a, b, torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed hta⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point`: The complexes whose traces occur.

Also blueprint `lemma-perfect-complexes-geometric-point--1` (its consequence for `RΓ_c(X, K)` and
the geometric stalks).

Let `k` be separably (e.g. algebraically) closed, `X` separated of finite type over `k` with
structure morphism `a_X`, `Λ` a finite ring whose exponent is invertible in `k` and
`K ∈ Dctf(X, Λ)`. Then `RΓ_c(X, K)` and every geometric stalk `K_x̄ = RΓ(Spec Ω, Lx̄^* K)` are
perfect complexes of `Λ`-modules, so the traces of their endomorphisms are defined
(`DerivedCategory.IsPerfect.categoricalTrace`). Both are bounded with finitely generated
cohomology and of finite Tor amplitude (`lemma-perfect-complexes-geometric-point`), hence perfect
over the finite ring `Λ` (`DerivedCategory.isPerfect_of_finiteTorAmplitude`). -/
theorem isPerfect_compactlySupportedGlobalSections_and_geometricStalk
    {k : Type u} [Field k] [IsSepClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [HasCompactification aX]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X),
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
          ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K)).IsPerfect :=
  ⟨isPerfect_compactlySupportedGlobalSections Λ aX K hK,
    fun _ _ _ x ↦ isPerfect_geometricStalk Λ x K hK⟩

end Etale

end AlgebraicGeometry
