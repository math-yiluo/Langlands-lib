/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
/-!
# Künneth and the projection formula in ordinary étale cohomology

The Künneth formula and the projection formula in ordinary étale cohomology
(`proposition-ordinary-external-kunneth--1`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kunneth`
- `AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_rightDerivedLowerStar_of_isProper`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
section Kunneth

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [LocallyOfFiniteType aY]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [HasInvertibleExponent Λ Y] in
/-- Blueprint `proposition-ordinary-external-kunneth--1`: Künneth and the projection formula in
ordinary étale cohomology

**Künneth.** Let `k` be separably closed, let the exponent of `Λ` be invertible on `X` and `Y`
and let `X`, `Y` be finite-type `k`-schemes. For the cartesian square

```
  W --p₂--> Y
  |         |
  p₁        a_Y
  |         |
  v         v
  X --a_X-> Spec k
```

exhibiting `W = X ×_k Y`, the exterior-product map

`RΓ(X, E) ⊗^L RΓ(Y, K) ≅ RΓ(X ×_k Y, Lp₁^* E ⊗^L Lp₂^* K)`

is an isomorphism for all `E ∈ D(X_ét, Λ)` and `K ∈ D(Y_ét, Λ)` — unbounded, and with no
properness hypothesis. Without the cartesian hypothesis the statement is false: for `W = ∅`
and `X = Y = Spec k` the right-hand side is `0` and the left-hand side is `Λ`.

The schemes have to be quasi-compact, as in Stacks 0F1P (blueprint
`proposition-ordinary-external-kunneth--1`), which asks for `X` and `Y` of finite type: for `X` the
disjoint union of countably many copies of `Spec k`, `Y = Spec k`, `Λ = 𝔽_ℓ`, `E = Λ` and `K` a
vector space `V` in degree `0`, the left-hand side is `(∏ 𝔽_ℓ) ⊗ V` and the right-hand side is
`∏ V`; for `dim V = ℶ_ω` the second has dimension `ℶ_ω ^ ℵ₀ > ℶ_ω`, the dimension of the first. It
is `AlgebraicGeometry.Etale.nonempty_iso_kunneth_of_isSepClosed` when `X` is nonempty; when `X`
is empty both sides vanish. -/
theorem nonempty_iso_kunneth [QuasiCompact aX] [QuasiCompact aY] {W : Scheme.{u}} (p₁ : W ⟶ X)
    (p₂ : W ⟶ Y) (sq : IsPullback p₁ p₂ aX aY)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) W).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj E)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : IsEmpty W := Function.isEmpty p₁.base
    have hzero : ∀ (Z : Scheme.{u}) [IsEmpty Z]
        (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        IsZero ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj M) := fun Z _ M ↦
      have : (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).Additive := by
        unfold rightDerivedGlobalSections; infer_instance
      Functor.map_isZero _ (DerivedCategory.isZero_of_forall_isZero
        (Scheme.Etale.isZero_sheaf_of_isEmpty ·) M)
    refine ⟨IsZero.iso ?_ (hzero W _)⟩
    rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, (hzero X E).eq_of_src (𝟙 _) 0,
      MonoidalPreadditive.zero_tensor]
  · have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
    exact nonempty_iso_kunneth_of_isSepClosed Λ aX aY p₁ p₂ sq E K

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `proposition-ordinary-external-kunneth--1`: Künneth and the projection formula in
ordinary étale cohomology

**The projection formula for a proper morphism.** For `f : X ⟶ Y` proper between finite-type
`k`-schemes and all `E ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`,

`Rf_* E ⊗^L L ≅ Rf_*(E ⊗^L Lf^* L)`.

The isomorphism is the projection map `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`,
an isomorphism by `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_of_isProper`
(`proposition-proper-direct-image-constructible-complexes--9`); the invertibility of the exponent of
`Λ` is not needed. -/
theorem nonempty_iso_derivedTensor_rightDerivedLowerStar_of_isProper (f : X ⟶ Y) [IsProper f]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E)).obj L ≅
      (R((f)_*[ModuleCat.{u + 1} Λ])).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj E).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L))) :=
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ isAddTorsion_of_finite f
  ⟨asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app L)⟩

end Kunneth

end Etale

end AlgebraicGeometry
