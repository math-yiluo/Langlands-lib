/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Point

/-!
# Positive cohomology of a closed exceptional image

Let `k` be a separably closed field, `T = 𝔸¹_k` and `i : Spec k ⟶ T` the inclusion of the
origin, the zero section. For a nonzero finite coefficient ring `Λ` whose exponent is invertible
in `k`, the cohomology sheaf `𝓗²(Ri^! Λ_T)` is nonzero (blueprint `example-closed-support`).
Hence `Ri^!` does not preserve `D^{≤ 0}`, or any `D^{≤ c}` with `c < 2`.

## The argument

The blueprint computes `i_* 𝓗²(Ri^! Λ_T) ≅ R¹j_* Λ_U` from the closed support triangle and the
Galois cohomology of the strictly henselian trait at the origin. Here the nonvanishing is read
off from the rank-one purity `Ri^!(Λ_T(1)[2]) ≅ Λ_k`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLineZero`), together with
the trivialization `Λ_T(1) ≅ Λ_T` of the Tate twist over a separably closed field
(`AlgebraicGeometry.Etale.nonempty_iso_tateObject_constantComplex_of_isSepClosed`): the twist is
pulled back from `Spec k`, where every étale sheaf is constant. This needs a normalized Tate
twist datum (`AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`) as a hypothesis, although it
does not appear in the statement.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_tateObject_constantComplex_of_isSepClosed`
- `AlgebraicGeometry.Etale.not_isZero_homology_two_rightDerivedUpperShriek_affineLineZero`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
  (k : Type u) [Field k] [IsSepClosed k]

/-- On the spectrum of a separably closed field `k` every étale sheaf `L` of `Λ`-modules whose
stalk at the geometric point `𝟙 : Spec k ⟶ Spec k` is `Λ` is the constant sheaf `Λ`: the
counit of the constant sheaf adjunction is an isomorphism, and the global sections of `L` are
its stalk. -/
lemma nonempty_iso_constantSheaf_of_isSepClosed
    (L : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : (pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.obj L ≅ ModuleCat.of Λ Λ) :
    Nonempty (L ≅ (constantSheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let adj := constantSheafAdj (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    isTerminalEtalePoint
  exact ⟨(asIso (adj.counit.app L)).symm ≪≫
    (constantSheaf _ _).mapIso
      ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).app L).symm ≪≫
    (constantSheaf _ _).mapIso (ΓIsoSheafFiberOfIsSepClosed L ≪≫ e)⟩

omit [IsSepClosed k] in
/-- Over a field `k` and for a nonzero ring `Λ`, the zeroth cohomology sheaf of
the constant complex `Λ_k` is nonzero: it is the constant sheaf `Λ`, and the constant sheaf
functor on `Spec k` is fully faithful. -/
theorem not_isZero_homology_zero_constantComplex_spec [Nontrivial Λ] :
    ¬ IsZero ((DerivedCategory.homologyFunctor _ 0).obj (constantComplex Λ (Spec (.of k)))) := by
  intro h
  have h₁ := IsZero.of_full_of_faithful_of_isZero
    (constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) _
    (h.of_iso (homologyZeroConstantComplexIso Λ (Spec (.of k))).symm)
  rw [ModuleCat.isZero_iff_subsingleton] at h₁
  exact not_subsingleton Λ h₁

variable [HasTateTwist Λ] [HasInvertibleExponent Λ (Spec (.of k))]

/-- Over a separably closed field `k`, every Tate twisting object is trivial: for every
`k`-scheme `X`, `Λ_X(m) ≅ Λ_X`. The twisting object is pulled back from `Spec k`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTateObjectIso`), where it is a locally constant
sheaf with stalk `Λ` placed in degree zero
(`AlgebraicGeometry.Etale.exists_isLocallyConstantSheaf_tateObject`), hence the constant sheaf
(`AlgebraicGeometry.Etale.nonempty_iso_constantSheaf_of_isSepClosed`). -/
theorem nonempty_iso_tateObject_constantComplex_of_isSepClosed {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (m : ℤ) :
    Nonempty (tateObject Λ X m ≅ constantComplex Λ X) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  obtain ⟨L, -, hL, ⟨eL⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) (Spec (.of k)) m
  obtain ⟨e₁⟩ := hL k (𝟙 _)
  obtain ⟨e₂⟩ := nonempty_iso_constantSheaf_of_isSepClosed Λ k L e₁
  exact ⟨(leftDerivedUpperStarTateObjectIso aX m).symm ≪≫
    (L((aX)^*[ModuleCat.{u + 1} Λ])).mapIso (eL ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e₂ ≪≫
      (constantComplexIsoSingleFunctor Λ (Spec (.of k))).symm) ≪≫
    leftDerivedUpperStarConstantComplexIso Λ aX⟩

variable [Finite Λ]

/-- For the zero section `s : Spec k ⟶ 𝔸¹_k` over a separably closed field,
`(Rs^! Λ_T)[2] ≅ Λ_k`: rank-one purity
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLineZero`) with the twist
trivialized (`AlgebraicGeometry.Etale.nonempty_iso_tateObject_constantComplex_of_isSepClosed`).
-/
theorem nonempty_iso_shift_rightDerivedUpperShriek_affineLineZero_of_isSepClosed
    [HasTateTwist.IsNormalized Λ] :
    Nonempty (((rightDerivedUpperShriek Λ
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k))))⟦(2 * 1 : ℤ)⟧ ≅
      constantComplex Λ (Spec (.of k))) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_affineLineZero Λ (𝟙 (Spec (.of k)))
  obtain ⟨t⟩ := nonempty_iso_tateObject_constantComplex_of_isSepClosed Λ k
    (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) 1
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))
  exact ⟨(((R(s)^![Λ]).commShiftIso (2 * 1 : ℤ)).app _).symm ≪≫
    (R(s)^![Λ]).mapIso ((shiftFunctor _ (2 * 1 : ℤ)).mapIso
      (t.symm ≪≫ (derivedTensorLeftUnitor _ _ _).symm)) ≪≫ e⟩

/-- Blueprint `example-closed-support`: Positive cohomology of a closed exceptional image.

Let `k` be a separably closed field, `T = 𝔸¹_k` and `i : Spec k ⟶ T` the origin (the zero
section). For a nonzero finite coefficient ring `Λ` with exponent invertible in `k` (for
instance `Λ = A_{E,n}` with `ℓ ≠ char k`), the cohomology sheaf `𝓗²(Ri^! Λ_T)` is nonzero.
Thus no bound `Ri^! D^{[a,b]} ⊆ D^{[a-c,b]}` holds for `c < 2`.

The proof uses rank-one purity `Ri^!(Λ_T(1)[2]) ≅ Λ_k`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLineZero`) and the
trivialization of the Tate twist over `k`
(`AlgebraicGeometry.Etale.nonempty_iso_tateObject_constantComplex_of_isSepClosed`), so
`(Ri^! Λ_T)[2] ≅ Λ_k` and `𝓗²(Ri^! Λ_T) ≅ 𝓗⁰(Λ_k) ≠ 0`; it therefore assumes a normalized
Tate twist datum, unlike the blueprint proof via the closed support triangle and
`R¹j_* Λ_U`. -/
theorem not_isZero_homology_two_rightDerivedUpperShriek_affineLineZero
    [Nontrivial Λ] [HasTateTwist.IsNormalized Λ] :
    ¬ IsZero ((DerivedCategory.homologyFunctor _ 2).obj
      ((rightDerivedUpperShriek Λ
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k))))) := fun h ↦ by
  obtain ⟨e⟩ := nonempty_iso_shift_rightDerivedUpperShriek_affineLineZero_of_isSepClosed Λ k
  exact not_isZero_homology_zero_constantComplex_spec Λ k
    (h.of_iso ((DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
      ((DerivedCategory.homologyFunctor _ 0).shiftIso (2 * 1 : ℤ) 0 2 (by norm_num)).app _))

end Etale

end AlgebraicGeometry
