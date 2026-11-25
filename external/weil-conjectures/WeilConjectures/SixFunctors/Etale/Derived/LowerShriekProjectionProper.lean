/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCupProduct
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The projection map of `Rf_!` and the direct-image projection map

Let `c = (X ⟶[i] Z ⟶[g] Y)` be a compactification of `f : X ⟶ Y`. The *forget-supports map*
of `c` is the composite
```
Rf_!(c) = D(i_!) ⋙ Rg_* ⟶ Ri_* ⋙ Rg_* ⟶ Rf_*
```
of `Rg_*` applied to the comparison `D(i_!) ⟶ Ri_*` and of the composition isomorphism
(`AlgebraicGeometry.Etale.compactificationForgetSupports`). It intertwines the projection map
`PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)` of
`AlgebraicGeometry.Etale.projectionMapOfCompactification` with the projection map
`Rf_*K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^*L)` of the direct image
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_comp_compactificationForgetSupports`).
For a proper `f` the forget-supports map is an isomorphism, so the compactly supported
projection formula is the direct-image projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMapOfCompactification_app_app_iff_of_isProper`); for
`f = 𝟙 X` the latter holds for any coefficients
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_id_app_app`).

These are the identity and proper clauses of blueprint
`proposition-composition-base-change-rf-shriek--1`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

section Identity

/-- The projection map `R(𝟙 X)_* M ⊗ᴸ L ⟶ R(𝟙 X)_*(M ⊗ᴸ L(𝟙 X)^* L)` of the identity is an
isomorphism, for any coefficients: the derived pullback `L(𝟙 X)^* ≅ 𝟭` is an equivalence and
its tensor comparison is invertible. -/
theorem isIso_rightDerivedLowerStarProjectionMap_id_app_app (X : Scheme.{u})
    (M L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A (𝟙 X)).app M).app L) := by
  have : L(((𝟙 X))^*[A]).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarId A X).symm
  exact (derivedUpperStarLowerStarAdjunction A (𝟙 X))
    |>.isIso_rightAdjointProjectionMap_app_app_of_isEquivalence
      (leftDerivedUpperStarTensorComparison A (𝟙 X)) M L

end Identity

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The *forget-supports map* `Rf_!(c) ⟶ Rf_*` of a compactification `c = (X ⟶[i] Z ⟶[g] Y)`
of `f`: `Rg_*` applied to the comparison `D(i_!) ⟶ Ri_*`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar`), followed by the
composition isomorphism `Ri_* ⋙ Rg_* ⟶ Rf_*` conjugate to
`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`. -/
noncomputable def compactificationForgetSupports : Rf_!(c)[A] ⟶ R((f)_*[A]) :=
  Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A c.i) R((c.g)_*[A]) ≫
    rightDerivedLowerStarCompHom A c.i c.g f c.comm

/-- For a proper `f`, the forget-supports map of any compactification of `f` is an isomorphism:
the open immersion `i` is then also a closed immersion. -/
instance isIso_compactificationForgetSupports [IsProper f] :
    IsIso (compactificationForgetSupports A c) := by
  have := c.isClosedImmersion_openImmersion ‹_›
  unfold compactificationForgetSupports
  infer_instance

/-- **The projection map of `Rf_!` and the direct-image projection map**: the forget-supports
map `s : Rf_!(c) ⟶ Rf_*` intertwines the projection maps,
```
Rf_!(c)K ⊗ᴸ L ──PF_c──▶ Rf_!(c)(K ⊗ᴸ Lf^*L)
     │ s ⊗ 1                  │ s
     ▼                        ▼
 Rf_*K ⊗ᴸ L  ──PF_*──▶  Rf_*(K ⊗ᴸ Lf^*L).
``` -/
theorem projectionMapOfCompactification_comp_compactificationForgetSupports
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L ≫
        (compactificationForgetSupports A c).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map ((compactificationForgetSupports A c).app K)).app L ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app L := by
  refine (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap_comp _
    (derivedUpperStarLowerStarAdjunction A c.i) (derivedUpperStarLowerStarAdjunction A f)
    (leftDerivedUpperStarTensorComparison A c.i) (leftDerivedUpperStarTensorComparison A f) _ _
    (derivedOpenImmersionLowerShriekProjectionIso_inv_comp_toLowerStar A c.i)
    (fun M L ↦ ?_) K L
  have h := rightDerivedLowerStarProjectionMap_comp' A c.i c.g f c.comm M L
  rw [← Iso.symm_hom, ← leftDerivedUpperStarCompactificationIso_eq] at h
  simp only [derivedTensor_map_app, derivedTensor_obj_map] at h
  exact h

/-- **For a proper morphism the compactly supported projection formula is the direct-image
projection formula**: for any compactification `c` of a proper `f`, the projection map `PF_c`
is invertible at `(K, L)` if and only if the projection map
`Rf_*K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^*L)` is. -/
theorem isIso_projectionMapOfCompactification_app_app_iff_of_isProper [IsProper f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (((projectionMapOfCompactification A c).app K).app L) ↔
      IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app L) := by
  have h := projectionMapOfCompactification_comp_compactificationForgetSupports A c K L
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : IsIso (((projectionMapOfCompactification A c).app K).app L ≫
        (compactificationForgetSupports A c).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L))) := inferInstance
    rw [h] at this
    exact IsIso.of_isIso_comp_left (((-⊗ᴸ-(Y)[A]).map
      ((compactificationForgetSupports A c).app K)).app L) _
  · have : IsIso (((-⊗ᴸ-(Y)[A]).map ((compactificationForgetSupports A c).app K)).app L ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app L) := inferInstance
    rw [← h] at this
    exact IsIso.of_isIso_comp_right _ ((compactificationForgetSupports A c).app
      (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)))

/-- **The projection formula for a compactification of the identity**: for any
compactification `c` of `𝟙 X`, the projection map `PF_c` is an isomorphism, for any
coefficients. -/
theorem isIso_projectionMapOfCompactification_id_app_app (c : Compactification (𝟙 X))
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsIso (((projectionMapOfCompactification A c).app K).app L) := by
  rw [isIso_projectionMapOfCompactification_app_app_iff_of_isProper]
  exact isIso_rightDerivedLowerStarProjectionMap_id_app_app A X K L

end Etale

end AlgebraicGeometry
