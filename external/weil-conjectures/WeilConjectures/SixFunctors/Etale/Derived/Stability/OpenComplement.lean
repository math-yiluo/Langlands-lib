/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# The open-complement condition

For a finite ring `Λ` and a quasi-compact open immersion `j : V ⟶ T`, the pair `(V, T)` satisfies
the *open-complement condition with constant `c`* (`theorem-f-shriek-finite-coefficients--1`) if
`Rᵠj_* M = 0` for `q > c` and every sheaf `M` of `Λ`-modules on `V_ét`, and `Rᵠj_*` carries
constructible sheaves to constructible sheaves in every degree.

This file proves that over a separably closed field `k`, for `T` of finite type over `k` of
dimension at most `d`, the condition holds with `c = 2d`, uniformly in the finite coefficient ring
`Λ` whose exponent is invertible in `k` (`proposition-open-direct-image-preserves-finite`).

## Main definitions

- `AlgebraicGeometry.Etale.OpenComplementBound`: the open-complement condition.

## Main statements

- `AlgebraicGeometry.Etale.openComplementBound_two_mul`
  (`proposition-open-direct-image-preserves-finite`): the condition with constant `2 dim T`.
- `AlgebraicGeometry.Etale.higherDirectImageIsoHomologyRightDerivedLowerStar`: `Rᵠj_* F` is the
  `q`-th homology sheaf of the unbounded `Rj_*(F[0])`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The higher direct image `Rᵠh_* F` (defined with the bounded below derived functor) is the
`q`-th homology sheaf of the unbounded derived direct image of `F` placed in degree `0`. -/
noncomputable def higherDirectImageIsoHomologyRightDerivedLowerStar {X Y : Scheme.{u}}
    (h : Y ⟶ X) (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImage Λ h q F ≅
      (_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((h)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  (_root_.DerivedCategory.homologyFunctor _ q).mapIso
    (((h)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Open-complement cohomological-dimension
condition.

For a finite ring `Λ`, a quasi-compact open immersion `j : V ⟶ T` and `c ≥ 0`, the pair `(V, T)`
satisfies the *open-complement condition with constant `c`* if `Rᵠj_* M = 0` for every `q > c`
and every sheaf `M` of `Λ`-modules on `V_ét`, and if `Rᵠj_*` carries constructible sheaves to
constructible sheaves in every degree. -/
def OpenComplementBound {V T : Scheme.{u}} (j : V ⟶ T) (c : ℕ) : Prop :=
  HasUniformDirectImageVanishingLE Λ j c ∧
    ∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)), IsConstructibleSheaf F →
      ∀ q : ℤ, IsConstructibleSheaf (higherDirectImage Λ j q F)

variable {Λ} in
/-- The open-complement condition is monotone in its constant. -/
lemma OpenComplementBound.mono {V T : Scheme.{u}} {j : V ⟶ T} {c c' : ℕ} (hcc' : c ≤ c')
    (h : OpenComplementBound Λ j c) : OpenComplementBound Λ j c' :=
  ⟨fun M q hq ↦ h.1 M q (by omega), h.2⟩

/-- Blueprint `proposition-open-direct-image-preserves-finite`: The open-complement condition is
unconditional and uniform in the coefficient ring.

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k` (for
instance annihilated by a power of a prime `ℓ ≠ char k`), `T` a finite-type `k`-scheme of
dimension at most `d`, and `j : V ⟶ T` a quasi-compact open immersion. Then `(V, T)` satisfies the
open-complement condition with constant `2d`: `Rᵠj_* M = 0` for every `q > 2d` and every sheaf
`M` of `Λ`-modules on `V_ét`, and `Rᵠj_* F` is constructible for every constructible `F`. The
constant `2d` depends on `T` alone, not on `Λ`.

The vanishing is `AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_two_mul`
(`theorem-results-from-etale-theory--4`), `V` being of finite type over `k` of dimension at most
`d`; the constructibility is the finiteness of `Rj_*`
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion`). -/
theorem openComplementBound_two_mul [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
    [HasInvertibleExponent Λ (Spec (.of k))] {V T : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] (j : V ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) :
    OpenComplementBound Λ j (2 * d) := by
  refine ⟨hasUniformDirectImageVanishingLE_two_mul Λ j (j ≫ aT) aT rfl d
    ((j.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd), fun F hF q ↦ ?_⟩
  have hb := boundedConstructible_rightDerivedLowerStar_of_isOpenImmersion Λ aT j
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (DerivedCategory.boundedConstructible_singleFunctor_obj F 0)
  have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) :=
    hb.2 q
  exact IsConstructibleSheaf.of_iso (higherDirectImageIsoHomologyRightDerivedLowerStar Λ j q F).symm

end Etale

end AlgebraicGeometry
