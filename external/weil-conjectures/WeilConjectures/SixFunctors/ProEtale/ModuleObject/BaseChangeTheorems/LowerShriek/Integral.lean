/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekUnit

/-!

# The compactly supported base change theorem for constructible `𝒪_E`-sheaves

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, with condensed ring of integers
`𝒪̲_E` (`Profinite.padicIntegersRingObj ℓ E`). This file provides, for the coefficient ring
`𝒪̲_E`, the results that the files `CompactificationIndependence`, `MorphismDefs` and
`CompactlySupported` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek` provide for
`E̲` and `ℚ̲̄_ℓ`:

* the independence of the lower shriek from the compactification, `Rf_!^{c₁} ≅ Rf_!^{c₂}`;
* the compact-support base-change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for a cartesian
  square `sq : IsPullback g' f' f g`;
* the compactly supported base change theorem: `Ex_!` is an isomorphism.

The constructions are the generic ones of those files. The only coefficient-specific input is the
proper base change theorem for bounded constructible `𝒪_E`-sheaves
(`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`,
blueprint `proposition-proper-direct-image-constructible-complexes`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper`).

## Main statements

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers`:
  `Rf_!^{c₁} ≅ Rf_!^{c₂}` for `𝒪_E`-sheaves.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicIntegers`: the
  compact-support base-change morphism `Ex_!` for `𝒪_E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers`: `Ex_!`
  is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### Independence of the compactification -/

section Pushforward

variable {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]
  [IsProper h.left]

/-- For bounded constructible `𝒪_E`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism: the unit of `Lh^* ⊣ Rh_*` is invertible on
extensions by zero (`isIso_unit_app_openImmersionLowerShriek`), by proper base change for
`𝒪_E`-sheaves (`isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers`). -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (PadicIntegersRingObj.boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      ℓ E sq) :=
  by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (Profinite.padicIntegersRingObj ℓ E) ℓ sq
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have := isIso_unit_app_openImmersionLowerShriek _ ℓ
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h)
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E (𝟙 X))
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (overPullbackSnd h (overClosedComplement i₁))) sq
    (by
      rw [← PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
      exact isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E sq.flip)
    (by
      rw [← PadicIntegersRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
      exact isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E
        (isPullback_overPullbackFst_overPullbackSnd h (overClosedComplement i₁))) K
  simp only [PadicIntegersRingObj.boundedConstructibleOpenImmersionLowerShriekRefinementPushforward,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end Pushforward

section Independence

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y}

/-- The *independence of the lower shriek from the compactification* for bounded constructible
`𝒪_E`-sheaves: for two compactifications `c₁` and `c₂` of `f`, the isomorphism
`Rf_!^{c₁} ≅ Rf_!^{c₂}` on `Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧`, through a common refinement as in
`boundedConstructibleLowerShriekOfCompactificationIso`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers
    (c₁ c₂ : Compactification f.left) :
    PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactification
        ℓ E c₁ ≅
      PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactification
        ℓ E c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers ℓ E
    r₁.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers ℓ E
    r₂.isPullback
  PadicIntegersRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E r₁.isPullback
      r₁.hom_overG ≪≫
    (PadicIntegersRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E r₂.isPullback
      r₂.hom_overG).symm

end Independence

/-! ### The compactly supported base change theorem -/

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `𝒪_E`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into
`Rf'_!^{c_f.ofIsPullback sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers` with
`Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange_padicIntegers
    (sq : IsPullback g' f' f g) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g' ⋙
        PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f' :=
  PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

lemma boundedConstructibleLowerShriekBaseChange_padicIntegers_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq =
      PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers
          ℓ E ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicIntegers]

/-- **The base change theorem for the compactly supported direct image attached to a
compactification** of bounded constructible `𝒪_E`-sheaves: for a compactification `c` of `f`,
the compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` is
an isomorphism of functors `Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y')⟦𝒪̲_E⟧`. -/
theorem isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicIntegers
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    IsIso (PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
      ℓ E c sq) := by
  have := isIso_boundedConstructibleBaseChange_of_isProper_padicIntegers ℓ E
    (c.overBaseChange_isPullback_g sq)
  rw [PadicIntegersRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq]
  infer_instance

/-- **The base change theorem for the compactly supported direct image** of bounded
constructible `𝒪_E`-sheaves: for a cartesian square of schemes `sq : IsPullback g' f' f g`, the
compact-support base-change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` is an isomorphism of
functors `Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y')⟦𝒪̲_E⟧`, where `Rf_!` and `Rf'_!` are the lower shrieks
`boundedConstructibleLowerShriek`. -/
theorem isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq) := by
  have := isIso_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_padicIntegers
    ℓ E (compactificationOverField f) sq
  rw [boundedConstructibleLowerShriekBaseChange_padicIntegers_eq]
  infer_instance

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
