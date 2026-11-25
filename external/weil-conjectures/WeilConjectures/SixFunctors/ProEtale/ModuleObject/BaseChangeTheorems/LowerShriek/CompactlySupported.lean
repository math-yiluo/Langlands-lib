/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper

/-!

# The compactly supported base change theorem for constructible `E`- and `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, with condensed ring `E̲ = C(-, E)`
(`Profinite.continuousMapRingObj E`). Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`. This file deduces from the proper base change theorem
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`) and base change
for extension by zero
(`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`) that,
on the bounded constructible derived categories of `E`-sheaves, and of `ℚ̄_ℓ`-sheaves for the
condensed ring `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`, the compact-support base-change morphisms
of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs`
are isomorphisms:

* `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` for any compactification `c` of `f`;
* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for the lower shriek of the chosen compactifications.

No properness is imposed on `f` itself: the properness enters only through the structure
morphism `p` of a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f`.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes are
separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms of `Over (Spec (.of k))`; in particular the cartesian square `sq` is a
cartesian square of `Over (Spec (.of k))`. The compactification `Z` of `f.left` and its base
change `Z ×_Y Y'` are then objects of `Over (Spec (.of k))`, separated and of finite type over
`k` as well (`Compactification.overObj` of `WeilConjectures.Compactification.Over`).

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
  and its `_padicAlgCl` version: the base change theorem for the compactly supported direct
  image attached to a compactification `c` of `f` and its base change.
- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange` and its
  `_padicAlgCl` version: the base change theorem for the compactly supported direct image
  `Rf_!`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-! ### For a compactification -/

include ℓ k in
/-- **The base change theorem for the compactly supported direct image attached to a
compactification** of bounded constructible `E`-sheaves: for a compactification
`c` of `f`, the compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback
sq}` is an isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`: in the defining pasting, the
direct-image exchange is an isomorphism by proper base change for the proper structure morphism `p`
of `c`, and the extension-by-zero exchange is an isomorphism by base change for extension by zero.
-/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    IsIso (ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
      ℓ E c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper ℓ E (c.overBaseChange_isPullback_g sq)
  rw [ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq]
  -- Build the pasting explicitly to avoid instance search through the entire composite.
  refine IsIso.comp_isIso' ?_
    (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)))
  · exact Iso.isIso_hom _
  · exact Functor.isIso_whiskerLeft _ _
  · exact Iso.isIso_inv _
  · exact Functor.isIso_whiskerRight _ _
  · exact Iso.isIso_hom _

/-- **The base change theorem for the compactly supported direct image attached to a
compactification** of bounded constructible `ℚ̄_ℓ`-sheaves: for a
compactification `c` of `f`, the compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙
Rf'_!^{c.ofIsPullback sq}` is an isomorphism of functors `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`. -/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicAlgCl
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
    (c.overBaseChange_isPullback_g sq)
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq]
  infer_instance

/-! ### For the lower shriek -/

/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `E`-sheaves, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`: for a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the compact-support base-change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek`. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange ℓ E sq) := by
  have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
    (compactificationOverField f) sq
  rw [boundedConstructibleLowerShriekBaseChange_eq]
  infer_instance

include ℓ k in
/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `ℚ̄_ℓ`-sheaves: for a cartesian square of schemes `sq : IsPullback g' f' f g`, the
compact-support base-change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is an isomorphism of
functors `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`, where `Rf_!` and `Rf'_!` are the lower shrieks
`boundedConstructibleLowerShriek`. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq) := by
  have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicAlgCl ℓ
    (compactificationOverField f) sq
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
