/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Cohomological amplitude of the direct image between schemes of finite type over a field

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and
`Λ` a torsion ring. The higher direct images `R^q f_*` of étale sheaves of `Λ`-modules vanish for
`q > 2d` (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le`,
blueprint `lemma-uniform-bounds-pro-etale-affines` and `theorem-results-from-etale-theory--4`), so
the unbounded derived direct image `Rf_*` sends `D^{≤ n}` into `D^{≤ n + 2d}`
(`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj`), and being left t-exact it sends
`D^{≥ n}` into `D^{≥ n}` (`AlgebraicGeometry.Etale.isGE_rightDerivedLowerStar_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Vanishing of the higher direct images above twice the dimension, over an arbitrary
field** (blueprint `theorem-results-from-etale-theory--4` without the separably closed
hypothesis).

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and
`Λ` a torsion ring. Then `R^q f_* F = 0` for every étale sheaf `F` of `Λ`-modules on `X` and every
`q > 2d`, the derived functors being those of the direct image `f_*` of sheaves of `Λ`-modules.
The base changes of `X` to field extensions of `k` have dimension at most `d`
(`AlgebraicGeometry.topologicalKrullDim_pullback_le`), so this is
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_topologicalKrullDim_le`. -/
theorem isZero_rightDerived_lowerStar_of_two_mul_lt (hΛ : IsAddTorsion Λ) {k : Type u}
    [Field k] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 2 * d < q) :
    IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F) := by
  have hn (L : Type u) [Field L] (s : Spec (.of L) ⟶ Spec (.of k)) {P : Scheme.{u}}
      (p₁ : P ⟶ X) (p₂ : P ⟶ Spec (.of L)) (hP : IsPullback p₁ p₂ aX s) :
      topologicalKrullDim P ≤ (d : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hP.isoPullback.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_pullback_le aX s).trans hd
  exact (isZero_higherDirectImage_of_forall_topologicalKrullDim_le Λ hΛ aX aY f hf d hn F q
    (by lia)).of_iso
      ((((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F q).symm ≪≫
        homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F q)

/-- **The derived direct image raises degrees by at most twice the dimension.** Let `k` be a
field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and `Λ` a torsion
ring. If `K ∈ D(X_ét, Λ)` vanishes above `n`, then `Rf_* K` vanishes above `n + 2d`. No
boundedness below is needed: this is `CategoryTheory.Functor.isLE_rightDerivedFunctor_obj` for
the uniform vanishing `AlgebraicGeometry.Etale.isZero_rightDerived_lowerStar_of_two_mul_lt`. -/
theorem isLE_rightDerivedLowerStar_obj (hΛ : IsAddTorsion Λ) {k : Type u}
    [Field k] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsLE n] : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K).IsLE (n + 2 * (d : ℤ)) := by
  have := ((f)_*[ModuleCat.{u + 1} Λ]).isLE_rightDerivedFunctor_obj (2 * d)
    (fun F q hq ↦ isZero_rightDerived_lowerStar_of_two_mul_lt Λ hΛ aX aY f hf d hd F q hq) K n
  simpa using this

/-- The derived direct image is left t-exact: if `K ∈ D(X_ét, Λ)` vanishes below `n`, so does
`Rf_* K`. -/
theorem isGE_rightDerivedLowerStar_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [K.IsGE n] : ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K).IsGE n :=
  ((f)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj K n

end Etale

end AlgebraicGeometry
