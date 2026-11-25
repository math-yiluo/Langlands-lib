/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The Verdier dual on `Dctf`: boundary exchange

For a finite coefficient ring `Λ` whose exponent is invertible on a field `k` and schemes
separated of finite type over `k`, this file states

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_verdierDual`
  (`corollary-verdier-exchange-formulas--3`): `Ri^! 𝔻_T K ≅ 𝔻_Z (i^* K)`;
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`
  (`corollary-verdier-exchange-formulas--7`): for a closed immersion `i : Z ⟶ T` the boundary
  exchange `i^* 𝔻_T L ≅ 𝔻_Z Ri^! L` holds on `Dctf(T)`;
- `AlgebraicGeometry.Etale.HasBoundaryDuality` (`corollary-verdier-exchange-formulas--7`) and
  `AlgebraicGeometry.Etale.hasBoundaryDuality` (`corollary-verdier-exchange-formulas--7`): the
  finite-stage boundary duality input, and that it holds over an algebraically closed field;
- `AlgebraicGeometry.Etale.verdierDual_finiteStage` (`theorem-verdier-biduality`, finite stages):
  `𝔻_X` is an involution of `Dctf(X, Λ)` with the Tor bound `[-b - 2d, -a]`.

The canonical exchange map of the blueprint is not constructed; the exchange is stated as the
existence of an isomorphism, as in `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- The exceptional inverse image of an internal hom: for `f : X ⟶ Y` admitting a
compactification and a finite ring `Λ`,

`Rf^! RHom_Y(M, N) ≅ RHom_X(Lf^* M, Rf^! N)`.

Both sides are right adjoint to functors of `Z ∈ D(X_ét)`: the left one to `M ⊗ᴸ Rf_! Z`, the
right one to `Rf_!(Lf^* M ⊗ᴸ Z)`, and these agree by the projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and the symmetry of `⊗ᴸ`. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)^![Λ]).obj
        ((RHom(Y)[ModuleCat.{u + 1} Λ].obj (op M)).obj N) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M))).obj
        ((R(f)^![Λ]).obj N)) := by
  have := isIso_projectionMap_of_finite Λ f
  obtain ⟨βY⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) Y
  obtain ⟨βX⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) X
  let adj₁ := (rightDerivedUpperShriekAdjunction Λ f).comp
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) M)
  let adj₂ := (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)).comp
    (rightDerivedUpperShriekAdjunction Λ f)
  let P : R(f)_![ModuleCat.{u + 1} Λ] ⋙ (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip.obj M ≅
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M) ⋙
        R(f)_![ModuleCat.{u + 1} Λ] :=
    NatIso.ofComponents (fun Z ↦ asIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app Z).app M))
      fun g ↦ NatTrans.congr_app ((projectionMap (ModuleCat.{u + 1} Λ) f).naturality g) M
  let e := Functor.isoWhiskerLeft (R(f)_![ModuleCat.{u + 1} Λ]) (βY.app M) ≪≫ P ≪≫
    Functor.isoWhiskerRight (βX.app _).symm (R(f)_![ModuleCat.{u + 1} Λ])
  exact ⟨(adj₁.rightAdjointUniq (adj₂.ofNatIsoLeft e.symm)).app N⟩

/-- Blueprint `corollary-verdier-exchange-formulas--3`: Exceptional restriction of a Verdier dual.

For a morphism `i : Z ⟶ T` (in the blueprint a closed immersion) such that `i`, the structure
morphism `a_T : T ⟶ S` and `a_Z = i ≫ a_T` admit compactifications, and finite coefficients `Λ`,
there is an isomorphism `α_K : Ri^! 𝔻_T K ≅ 𝔻_Z (i^* K)` for every `K`, where
`𝔻_T = RHom(-, ω_T)` and `𝔻_Z = RHom(-, ω_Z)`. It is the exchange
`Ri^! RHom(K, ω_T) ≅ RHom(i^* K, Ri^! ω_T)`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedHom`) combined with
`Ri^! ω_T ≅ ω_Z` (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex`).
No finiteness of `K` is needed. -/
theorem nonempty_iso_rightDerivedUpperShriek_verdierDual {Z T S : Scheme.{u}} (aT : T ⟶ S)
    [HasCompactification aT] (i : Z ⟶ T) [HasCompactification i] [HasCompactification (i ≫ aT)]
    [QuasiCompact (i ≫ aT)]
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(i)^![Λ]).obj
        ((verdierDual Λ aT).obj (op K)) ≅
      (verdierDual Λ (i ≫ aT)).obj
        (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_derivedHom Λ i K (dualizingComplex _ aT)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_dualizingComplex Λ i aT
  exact ⟨e₁ ≪≫ ((RHom(Z)[ModuleCat.{u + 1} Λ]).obj _).mapIso e₂⟩

/-- Blueprint `corollary-verdier-exchange-formulas--7`: Discharge of the boundary duality input.

Let `k` be algebraically closed, and let `i : Z ⟶ T` be a closed immersion of schemes
separated of finite type over `k` (for instance two locally closed pieces of a separated
finite-type `Y`). For every `L ∈ Dctf(T, Λ)` the boundary exchange
`β_L : i^* 𝔻_T L ⟶ 𝔻_Z Ri^! L` is an isomorphism; here it is stated as the existence of an
isomorphism. That `𝔻_T` preserves `Dctf(T, Λ)`, the first clause of the boundary duality input,
is `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`. -/
theorem nonempty_iso_leftDerivedUpperStar_verdierDual [IsAlgClosed k] {Z T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasCompactification aT] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [HasCompactification (i ≫ aT)]
    {L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T L) :
    Nonempty ((L((i)^*[ModuleCat.{u + 1} Λ])).obj
        ((verdierDual Λ aT).obj (op L)) ≅
      (verdierDual Λ (i ≫ aT)).obj
        (op ((R(i)^![Λ]).obj L))) := by
  -- `𝔻_Z (i^* K) ≅ Ri^! 𝔻_T K`, from `Ri^! RHom(K, ω_T) ≅ RHom(i^* K, Ri^! ω_T)` and
  -- `Ri^! ω_T ≅ ω_Z`
  have hex (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    (nonempty_iso_rightDerivedUpperShriek_verdierDual Λ aT i K).map Iso.symm
  have hD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) T
      ((verdierDual Λ aT).obj (op L)) :=
    constructibleFiniteTor_verdierDual Λ aT hL
  have hiD : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z
      ((L((i)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aT).obj (op L))) :=
    constructibleFiniteTor_leftDerivedUpperStar _ i hD
  obtain ⟨e₁⟩ := hex ((verdierDual Λ aT).obj (op L))
  obtain ⟨b₁⟩ := nonempty_iso_verdierDual_verdierDual Λ aT hL
  obtain ⟨b₂⟩ := nonempty_iso_verdierDual_verdierDual Λ (i ≫ aT) hiD
  -- `𝔻_Z (i^* 𝔻_T L) ≅ Ri^! L`, then dualize once more on `Z`
  let e : (verdierDual Λ (i ≫ aT)).obj
      (op ((L((i)^*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ aT).obj
        (op L)))) ≅ (R(i)^![Λ]).obj L :=
    e₁ ≪≫ (R(i)^![Λ]).mapIso b₁.symm
  exact ⟨b₂ ≪≫ (verdierDual Λ (i ≫ aT)).mapIso e.symm.op⟩

/-- Blueprint `corollary-verdier-exchange-formulas--7`: The finite-stage boundary duality input.

For a finite coefficient ring `Λ` and a scheme `Y` with structure morphism `a_Y : Y ⟶ Spec k`,
the boundary duality input for `(Y, Λ)` consists of two assertions about the locally closed
pieces `s : T ⟶ Y` of `Y` (quasi-compact immersions, with `a_T = s ≫ a_Y` admitting a
compactification), with `ω_T = Ra_T^! Λ` and `𝔻_T = RHom(-, ω_T)`:

1. `𝔻_T` carries `Dctf(T, Λ)` into itself;
2. for every closed immersion `i : Z ⟶ T` between such pieces and every `L ∈ Dctf(T, Λ)`, the
   ordinary and exceptional restrictions are exchanged: `i^* 𝔻_T L ≅ 𝔻_Z Ri^! L`.

The blueprint's second clause is about a specific map, the boundary exchange `β_L`, and adds its
compatibility with evaluation; here it asserts the existence of an isomorphism, as do
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual` and
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`. -/
def HasBoundaryDuality {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) : Prop :=
  (∀ {T : Scheme.{u}} (s : T ⟶ Y) [IsImmersion s] [QuasiCompact s]
      [HasCompactification (s ≫ aY)]
      {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) T K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) T
          ((verdierDual Λ (s ≫ aY)).obj (op K))) ∧
  ∀ {Z T : Scheme.{u}} (s : T ⟶ Y) [IsImmersion s] [QuasiCompact s]
    [HasCompactification (s ≫ aY)] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    [HasCompactification (i ≫ s ≫ aY)]
    {L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) T L →
      Nonempty ((L((i)^*[ModuleCat.{u + 1} Λ])).obj
          ((verdierDual Λ (s ≫ aY)).obj (op L)) ≅
        (verdierDual Λ (i ≫ s ≫ aY)).obj
          (op ((R(i)^![Λ]).obj L)))

/-- Blueprint `corollary-verdier-exchange-formulas--7`: The finite-stage boundary input is a
consequence.

For `k` algebraically closed, a finite coefficient ring `Λ` whose exponent is invertible on `k`
and `Y` separated of finite type over `k`, the boundary duality input
`AlgebraicGeometry.Etale.HasBoundaryDuality` holds: its first clause is the preservation
`AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`, its second the boundary exchange
`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_verdierDual`, on the pieces `T`,
which are again separated of finite type over `k`. -/
theorem hasBoundaryDuality [IsAlgClosed k] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    HasBoundaryDuality Λ aY := by
  refine ⟨fun s _ _ _ K hK ↦ ?_, fun s _ _ _ i _ _ _ L hL ↦ ?_⟩
  · have : IsSeparated s := inferInstance
    exact constructibleFiniteTor_verdierDual Λ (s ≫ aY) hK
  · have : IsSeparated s := inferInstance
    exact nonempty_iso_leftDerivedUpperStar_verdierDual Λ (s ≫ aY) i hL

/-- Blueprint `theorem-verdier-biduality`: Verdier biduality on the coefficient class, at the finite
stages `Λ = A_{E,n}`.

For `X` separated of finite type over an algebraically closed field `k` with `dim X ≤ d` and a
finite coefficient ring `Λ` whose exponent is invertible on `k`, the Verdier dual
`𝔻_X = RHom(-, ω_X)` preserves `Dctf(X, Λ)` and the evaluation-defined double-dual map
`δ_K : K ⟶ 𝔻_X 𝔻_X K` is an isomorphism on it, so that `𝔻_X` is an anti-equivalence of `Dctf(X, Λ)`
(`AlgebraicGeometry.Etale.verdierDualEquivalence`); an input Tor interval `[a, b]` gives the
interval `[-b - 2d, -a]` for the dual. -/
theorem verdierDual_finiteStage [IsAlgClosed k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX] (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    (∀ {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
            ((verdierDual Λ aX).obj (op K)) ∧
          IsIso ((verdierDualDoubleDual Λ aX).app K)) ∧
    ∀ (a b : ℤ) {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
      boundedConstructible (ModuleCat.{u + 1} Λ) X K →
        torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K →
          torAmplitudeIn (ModuleCat.{u + 1} Λ) X (-b - 2 * (d : ℤ)) (-a)
            ((verdierDual Λ aX).obj (op K)) :=
  ⟨fun hK ↦ ⟨constructibleFiniteTor_verdierDual Λ aX hK, isIso_verdierDualDoubleDual_app Λ aX hK⟩,
    fun a b _ hK hKt ↦ torAmplitudeIn_verdierDual Λ aX d hd a b hK hKt⟩

end Etale

end AlgebraicGeometry
