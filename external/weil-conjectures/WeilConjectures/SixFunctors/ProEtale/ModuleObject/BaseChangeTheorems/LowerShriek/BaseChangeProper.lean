/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-!

# The compact-support base change for proper morphisms

For a cartesian square `sq : IsPullback g' f' f g` of separated `k`-schemes of finite type with
`f` and `f'` proper, the compact-support base change `Ex_!` on bounded constructible
`ℚ̄_ℓ`-sheaves is the base change `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` through the identifications
`Rf_! ≅ Rf_*` and `Rf'_! ≅ Rf'_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoLowerStar`,
blueprint `def-exchange-projection`: `Ex_!` is represented by `Ex_*` for the compactification
`f = f ∘ 𝟙` of a proper `f`).

The proof computes `Ex_!` through the trivial compactifications `X ⟶[𝟙] X ⟶[f] Y` and
`X' ⟶[𝟙] X' ⟶[f'] Y'` (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange`),
whose compact-support exchange map is `Ex_*` through `(𝟙)_! ≅ 𝟭`
(`CategoryTheory.ExchangeFormalism.shriekBaseChange_id_left_app`), the isomorphism
`(𝟙)_! ≅ 𝟭` of the trivial compactification being the identity isomorphism of the exchange
formalism (`boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The isomorphism `(𝟙 X)_! ≅ 𝟭` of the trivial compactification `X ⟶[𝟙] X ⟶[f] Y` of a proper
`f` is the identity isomorphism of the extension by zero of the exchange formalism. -/
lemma boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId (f : X ⟶ Y)
    [IsProper f.left] :
    boundedConstructibleOpenImmersionLowerShriekOfIsProperIso (Profinite.padicAlgClRingObj ℓ) ℓ f =
      (𝔽).shId (SepFinType.mk X) :=
  Adjunction.iso_ext_of_inv_app_comp_counit ((𝔽).shAdj (𝟙 (SepFinType.mk X)))
    ((𝔽).pbId (SepFinType.mk X)) _ _
    (fun W ↦ boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_inv_app_comp_counit f ℓ W)
    (fun W ↦ (𝔽).shId_inv_app_comp_counit (SepFinType.mk X) W)


section Proper

variable {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsProper f.left] [IsProper f'.left]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The map `g'` between the trivial compactifications of `f'` and `f`. -/
lemma ofIsProper_overObj_hom_eq (sq : IsPullback g' f' f g) :
    g'.left ≫ (Compactification.ofIsProper f.left).overObj.hom =
      (Compactification.ofIsProper f'.left).overObj.hom := by
  change g'.left ≫ f.left ≫ Y.hom = f'.left ≫ Y'.hom
  rw [← Category.assoc, ← Over.comp_left, sq.w, Over.comp_left, Category.assoc, Over.w g]

/-- The map `g'` between the trivial compactifications of `f'` and `f`. -/
noncomputable abbrev ofIsProperBaseChangeHom (sq : IsPullback g' f' f g) :
    (Compactification.ofIsProper f'.left).overObj ⟶
      (Compactification.ofIsProper f.left).overObj :=
  Over.homMk g'.left (ofIsProper_overObj_hom_eq sq)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The square of the open immersions (identities) of the trivial compactifications of `f'` and
`f` is cartesian. -/
lemma isPullback_ofIsProper_overI (sq : IsPullback g' f' f g) :
    IsPullback g' (Compactification.ofIsProper f'.left).overI
      (Compactification.ofIsProper f.left).overI (ofIsProperBaseChangeHom sq) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (by
    simp only [Over.comp_left]
    exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (IsPullback.of_id_snd (f := g'.left))

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The square of the proper maps of the trivial compactifications of `f'` and `f` is cartesian. -/
lemma isPullback_ofIsProper_overG (sq : IsPullback g' f' f g) :
    IsPullback (ofIsProperBaseChangeHom sq) (Compactification.ofIsProper f'.left).overG
      (Compactification.ofIsProper f.left).overG g :=
  IsPullback.of_map (Over.forget _)
    (Over.OverMorphism.ext (by
      simp only [Over.comp_left]
      exact congrArg CommaMorphism.left sq.w)) sq.overLeft

/-- The compact-support exchange map of the trivial compactifications of the proper `f` and `f'`
is the compact-support exchange map of the factorizations `X ⟶[𝟙] X ⟶[f] Y` and
`X' ⟶[𝟙] X' ⟶[f'] Y'` in the exchange formalism. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChange_ofIsProper_eq
    (sq : IsPullback g' f' f g)
    (hw : SepFinType.homMk g' ≫ 𝟙 (SepFinType.mk X) = 𝟙 (SepFinType.mk X') ≫ SepFinType.homMk g')
    [IsIso ((𝔽).baseChange (SepFinType.homMk g') (𝟙 (SepFinType.mk X')) (𝟙 (SepFinType.mk X))
      (SepFinType.homMk g') hw)] :
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ
        (Compactification.ofIsProper f.left) (Compactification.ofIsProper f'.left)
        (ofIsProperBaseChangeHom sq) (isPullback_ofIsProper_overI sq)
        (isPullback_ofIsProper_overG sq) =
      ((𝔽).shriekBaseChange (𝟙 (SepFinType.mk X)) (SepFinType.homMk f) (𝟙 (SepFinType.mk X'))
        (SepFinType.homMk f') (SepFinType.homMk g') (SepFinType.homMk g') (SepFinType.homMk g) hw
        (SepFinType.homMk_comp_homMk sq.w)) := by
  obtain ⟨Xl, ⟨⟨⟩⟩, Xh⟩ := X
  obtain ⟨Xl', ⟨⟨⟩⟩, Xh'⟩ := X'
  obtain ⟨fl, ⟨⟨⟨⟩⟩⟩, fw⟩ := f
  obtain ⟨fl', ⟨⟨⟨⟩⟩⟩, fw'⟩ := f'
  change Xl ⟶ Y.left at fl
  change Xl' ⟶ Y'.left at fl'
  obtain rfl : Xh = fl ≫ Y.hom := by simpa using fw.symm
  obtain rfl : Xh' = fl' ≫ Y'.hom := by simpa using fw'.symm
  rfl

/-- The compact-support exchange map of the trivial compactifications of the proper `f` and `f'`
is the base change `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*`, through `Rf_!^c ≅ Rf_*`. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChange_ofIsProper
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ
        (Compactification.ofIsProper f.left) (Compactification.ofIsProper f'.left)
        (ofIsProperBaseChangeHom sq) (isPullback_ofIsProper_overI sq)
        (isPullback_ofIsProper_overG sq) ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
        (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f').hom =
    Functor.whiskerRight (boundedConstructibleLowerShriekOfCompactificationOfIsProperIso ℓ f).hom
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫
      boundedConstructibleBaseChange ℓ sq.toCommSq := by
  have hw : SepFinType.homMk g' ≫ 𝟙 (SepFinType.mk X) =
      𝟙 (SepFinType.mk X') ≫ SepFinType.homMk g' := by
    rw [Category.comp_id, Category.id_comp]
  have : IsIso ((𝔽).baseChange (SepFinType.homMk g') (𝟙 (SepFinType.mk X'))
      (𝟙 (SepFinType.mk X)) (SepFinType.homMk g')
      hw) :=
    isIso_baseChange_boundedConstructibleExchangeFormalism ℓ
      (IsPullback.of_id_snd (f := g') : IsPullback g' (𝟙 X') (𝟙 X) g')
  have key := (𝔽).shriekBaseChange_id_left (SepFinType.homMk f) (SepFinType.homMk f')
    (SepFinType.homMk g') (SepFinType.homMk g)
    hw (SepFinType.homMk_comp_homMk sq.w)
  have hσ := congrArg Iso.hom
    (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId ℓ f)
  have hσ' := congrArg Iso.hom
    (boundedConstructibleOpenImmersionLowerShriekOfIsProperIso_eq_shId ℓ f')
  simp only [boundedConstructibleLowerShriekOfCompactificationOfIsProperIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom]
  rw [hσ, hσ', boundedConstructibleBaseChange_eq_pfBaseChange]
  clear hσ hσ'
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChange_ofIsProper_eq ℓ sq hw]
  exact key

end Proper
end AlgebraicGeometry.ProEtale.CondensedRing
