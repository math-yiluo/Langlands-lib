/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeIntegralRational
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!

# The proper base change theorem for constructible `𝒪_E`-, `E`- and `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`. Its
condensed ring is `E̲ = C(-, E)` (`Profinite.continuousMapRingObj E`, of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`), and the coefficient ring
on `X_proét` is `E_X = p_X^* E̲`. Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper base
change theorem for bounded constructible `E`-sheaves: the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. No hypothesis is imposed on `g`. The same
holds for the condensed ring `ℚ̲̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
(`Profinite.padicAlgClRingObj`), whose sections are continuous maps into finite
subextensions of `ℚ̄_ℓ`.

The same holds for the condensed ring `𝒪̲_E` (`Profinite.padicIntegersRingObj`) of a finite
extension `E` of `ℚ_ℓ` embedded in `ℚ̄_ℓ`.

All three are deduced from the torsion case, as in the proof of blueprint
`theorem-smooth-base-change-all-admissible`.
A bounded constructible `E`-complex is `E ⊗ᴸ_{𝒪_E} K₀` for a bounded constructible
`𝒪_E`-complex `K₀` (`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`), and a bounded
constructible `ℚ̄_ℓ`-complex is `ℚ̄_ℓ ⊗ᴸ_{𝒪_E} K₀` for some `E` and `K₀`
(`ProEtale.exists_padicAlgCl_iso_integralModel`). The scalar comparisons identify the base-change
morphism at these complexes with the extension of scalars of the integral base-change morphism at
`K₀` (`nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational`,
`isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral`). By derived Nakayama, the latter
is invertible once its first derived reduction `- ⊗ᴸ_{𝒪_E} 𝔽_E` is
(`isIso_boundedConstructibleBaseChange_integral_app_of_reduction`). That reduction is the
pro-étale base-change morphism with coefficients `𝔽_E` at a complex of étale origin
(`ProEtale.boundedConstructible_derivedReduction_obj`), an isomorphism by finite-level
pro-étale proper base change (`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`), which is
the étale proper base change theorem `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`
read on the pro-étale site.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes are
separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms of `Over (Spec (.of k))`.

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`: proper
  base change on bounded constructible `𝒪_E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`: proper base
  change on bounded constructible `E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`: proper
  base change on bounded constructible `ℚ̄_ℓ`-sheaves.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The proper base change theorem** (blueprint
`proposition-proper-direct-image-constructible-complexes`) for bounded constructible `𝒪_E`-sheaves,
`E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y')⟦𝒪̲_E⟧`. By derived Nakayama it suffices that the
first derived reduction `BC_sq(K₀) ⊗ᴸ_{𝒪_E} 𝔽_E` is invertible
(`isIso_boundedConstructibleBaseChange_integral_app_of_reduction`); this is the pro-étale
base-change morphism with coefficients `𝔽_E` at a complex of étale origin, invertible by the
étale proper base change theorem (`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`). -/
theorem isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] [IsProper f.left]
    (sq : IsPullback g' f' f g) :
    IsIso (PadicIntegersRingObj.boundedConstructibleBaseChange ℓ E sq.toCommSq) := by
  have hsq : IsPullback g'.left f'.left f.left g.left := sq.map (Over.forget _)
  have := isNoetherian_of_locallyOfFiniteType X.hom
  have := isNoetherian_of_locallyOfFiniteType Y'.hom
  have : Finite (ResidueFieldCoeff.{u} ℓ E) :=
    inferInstanceAs (Finite (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E)))
  rw [NatTrans.isIso_iff_isIso_app]
  intro K₀
  exact isIso_boundedConstructibleBaseChange_integral_app_of_reduction ℓ E sq.toCommSq hsq K₀
    (isIso_derivedBaseChangeMap_app_of_isProper _ hsq _
      (boundedConstructible_derivedReduction_obj X.left ℓ E _ K₀.property).plusEtaleOrigin)

/-- **The proper base change theorem** (blueprint
`proposition-proper-direct-image-constructible-complexes`) for bounded constructible `E`-sheaves,
`E` a finite extension of `ℚ_ℓ`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [IsProper f.left] (sq : IsPullback g' f' f g) :
    IsIso (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq.toCommSq) := by
  have := isNoetherian_of_locallyOfFiniteType X.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨K₀, ⟨e⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X.left ℓ E K
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  obtain ⟨α⟩ := nonempty_arrowIso_boundedConstructibleBaseChange_integralToRational ℓ E
    sq.toCommSq K₀
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E.1 sq
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff α).1 (by
    simp only [MorphismProperty.isomorphisms.iff]
    infer_instance)

/-- **The proper base change theorem** (blueprint
`proposition-proper-direct-image-constructible-complexes`) for bounded constructible `ℚ̄_ℓ`-sheaves:
for a cartesian square of schemes `sq : IsPullback g' f' f g` with `f` proper, the base-change
morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an isomorphism of functors
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`, for the condensed ring
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl [IsProper f.left]
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange ℓ sq.toCommSq) := by
  have hsq : IsPullback g'.left f'.left f.left g.left := sq.map (Over.forget _)
  have := isNoetherian_of_locallyOfFiniteType X.hom
  exact isIso_boundedConstructibleBaseChange_padicAlgCl_of_integral ℓ _ hsq fun E K₀ ↦
    have := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E.1 sq
    inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
