/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-!

# The compact-support base change for open immersions

For a cartesian square `sq : IsPullback g' f' f g` of separated `k`-schemes of finite type with
`f` and `f'` open immersions, the compact-support base change `Ex_!` on bounded constructible
`ℚ̄_ℓ`-sheaves is, through `Rf_! ≅ f_!` and `Rf'_! ≅ f'_!`, the inverse of the extension-by-zero
exchange morphism `Lg'^* f'_! ⟶ f_! Lg^*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen`,
blueprint `def-exchange-projection`: `Ex_!` is represented, for the compactification `f = 𝟙 ∘ f`
of an open immersion, by the identification `Lg^* f_! ≅ f'_! Lg'^*`).

The proof computes `Ex_!` through the trivial compactifications `X ⟶[f] Y ⟶[𝟙] Y` and
`X' ⟶[f'] Y' ⟶[𝟙] Y'` (`boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange`): the
base change of the pushforwards of the identity square is the identity through `R(𝟙)_* ≅ 𝟭`
(`CategoryTheory.ExchangeFormalism.pfBaseChange_id_vert_app`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

/-- A computation with 2-squares: if `E : P ⋙ G ⟶ G ⋙ P'` is the identity through `ι : P ≅ 𝟭`
and `ι' : P' ≅ 𝟭`, and `θ` is a left inverse of `β`, then the horizontal composite of `E` and `β`,
followed by `ι'` and `θ`, is `ι`. -/
lemma CategoryTheory.Functor.whiskerLeft_comp_whiskerRight_comp_aux {A B A' B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B'] {jS : A ⥤ B} {P : B ⥤ B}
    {G : B ⥤ B'} {G' : A ⥤ A'} {jS' : A' ⥤ B'} {P' : B' ⥤ B'} (ι : P ≅ 𝟭 B) (ι' : P' ≅ 𝟭 B')
    (E : P ⋙ G ⟶ G ⋙ P')
    (hE : E ≫ Functor.whiskerLeft G ι'.hom ≫ (Functor.rightUnitor G).hom =
      Functor.whiskerRight ι.hom G ≫ (Functor.leftUnitor G).hom)
    (β : jS ⋙ G ≅ G' ⋙ jS') (θ : G' ⋙ jS' ⟶ jS ⋙ G) (hθ : β.hom ≫ θ = 𝟙 _) :
    ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft jS E ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight β.hom P' ≫ (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft G' (Functor.whiskerLeft jS' ι'.hom ≫ (Functor.rightUnitor jS').hom) ≫ θ =
    Functor.whiskerRight (Functor.whiskerLeft jS ι.hom ≫ (Functor.rightUnitor jS).hom) G := by
  ext K
  have hE' := congr_app hE (jS.obj K)
  have hθ' := congr_app hθ K
  have hn := ι'.hom.naturality (β.hom.app K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app, Category.comp_id, Functor.comp_obj,
    Functor.id_obj, Functor.id_map, NatTrans.id_app] at hE' hθ' hn ⊢
  simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc, Functor.comp_obj]
  rw [reassoc_of% hn, hθ', Category.comp_id, hE']

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
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsOpenImmersion f.left] [IsOpenImmersion f'.left]

/-- The map `g` between the trivial compactifications of the open immersions `f'` and `f`. -/
noncomputable abbrev ofIsOpenImmersionBaseChangeHom (g : Y' ⟶ Y) :
    (Compactification.ofIsOpenImmersion f'.left).overObj ⟶
      (Compactification.ofIsOpenImmersion f.left).overObj :=
  Over.homMk g.left (by
    change g.left ≫ 𝟙 Y.left ≫ Y.hom = 𝟙 Y'.left ≫ Y'.hom
    simp [Over.w g])

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The square of the open immersions of the trivial compactifications of `f'` and `f` is
cartesian. -/
lemma isPullback_ofIsOpenImmersion_overI (sq : IsPullback g' f' f g) :
    IsPullback g' (Compactification.ofIsOpenImmersion f'.left).overI
      (Compactification.ofIsOpenImmersion f.left).overI (ofIsOpenImmersionBaseChangeHom g) :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (by
      simp only [Over.comp_left]
      exact congrArg CommaMorphism.left sq.w)) sq.overLeft

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom]
  [QuasiCompact X'.hom] [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The square of the proper maps (identities) of the trivial compactifications of `f'` and `f`
is cartesian. -/
lemma isPullback_ofIsOpenImmersion_overG :
    IsPullback (ofIsOpenImmersionBaseChangeHom (f := f) (f' := f') g)
      (Compactification.ofIsOpenImmersion f'.left).overG
      (Compactification.ofIsOpenImmersion f.left).overG g :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (by
      simp only [Over.comp_left]
      exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (IsPullback.of_id_snd (f := g.left))

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The base change of the pushforwards for the cartesian square of the trivial compactifications
is that of the identity square. -/
lemma boundedConstructibleBaseChange_ofIsOpenImmersion_eq :
    boundedConstructibleBaseChange ℓ
        (isPullback_ofIsOpenImmersion_overG (f := f) (f' := f') (g := g)).toCommSq =
      boundedConstructibleBaseChange ℓ
        (IsPullback.of_id_snd (f := g)).toCommSq := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight]

/-- The extension-by-zero exchange morphism of the open square of the trivial compactifications
is that of the square `sq`. -/
lemma boundedConstructibleOpenImmersionLowerShriekBaseChange_ofIsOpenImmersion_eq
    (sq : IsPullback g' f' f g) :
    boundedConstructibleOpenImmersionLowerShriekBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ
        (isPullback_ofIsOpenImmersion_overI sq).toCommSq =
      boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq := by
  rw [boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft,
    boundedConstructibleOpenImmersionLowerShriekBaseChange'_eq_exchangeLeft]
  rfl

/-- The base change of the pushforwards of the identity square `g ≫ 𝟙 = 𝟙 ≫ g` is the identity,
through `R(𝟙)_* ≅ 𝟭`. -/
lemma boundedConstructibleBaseChange_id_app (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleBaseChange ℓ
        (IsPullback.of_id_snd (f := g)).toCommSq).app M ≫
      (boundedConstructibleLowerStarId ℓ Y').hom.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj M) =
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
      ((boundedConstructibleLowerStarId ℓ Y).hom.app M) := by
  rw [boundedConstructibleBaseChange_eq_pfBaseChange]
  exact (𝔽).pfBaseChange_id_vert_app (SepFinType.homMk g) _ M

/-- The base change of the pushforwards of the identity square `g ≫ 𝟙 = 𝟙 ≫ g` is the identity,
through `R(𝟙)_* ≅ 𝟭`. -/
lemma boundedConstructibleBaseChange_id :
    boundedConstructibleBaseChange ℓ
        (IsPullback.of_id_snd (f := g)).toCommSq ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
        (boundedConstructibleLowerStarId ℓ Y').hom ≫ (Functor.rightUnitor _).hom =
    Functor.whiskerRight (boundedConstructibleLowerStarId ℓ Y).hom
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫
      (Functor.leftUnitor _).hom := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  have h := boundedConstructibleBaseChange_id_app ℓ (g := g) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app]
  simpa using h

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The base change of the pushforwards for the proper square of the trivial compactifications is
the identity, through `R(𝟙)_* ≅ 𝟭`. -/
lemma boundedConstructibleBaseChange_ofIsOpenImmersion :
    boundedConstructibleBaseChange ℓ
        (isPullback_ofIsOpenImmersion_overG (f := f) (f' := f') (g := g)).toCommSq ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (ofIsOpenImmersionBaseChangeHom (f := f) (f' := f') g))
        (boundedConstructibleLowerStarId ℓ Y').hom ≫ (Functor.rightUnitor _).hom =
    Functor.whiskerRight (boundedConstructibleLowerStarId ℓ Y).hom
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) ≫
      (Functor.leftUnitor _).hom := by
  rw [boundedConstructibleBaseChange_ofIsOpenImmersion_eq]
  exact boundedConstructibleBaseChange_id ℓ

/-- **`Ex_!` for open immersions**, on the trivial compactifications: the compact-support exchange
map of `X ⟶[f] Y ⟶[𝟙] Y` and `X' ⟶[f'] Y' ⟶[𝟙] Y'`, followed by `R(𝟙)_* ≅ 𝟭` and the
extension-by-zero exchange morphism, is `R(𝟙)_* ≅ 𝟭`. -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChange_ofIsOpenImmersion
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ
        (Compactification.ofIsOpenImmersion f.left) (Compactification.ofIsOpenImmersion f'.left)
        (ofIsOpenImmersionBaseChangeHom g) (isPullback_ofIsOpenImmersion_overI sq)
        isPullback_ofIsOpenImmersion_overG ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
        (Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ f')
          (boundedConstructibleLowerStarId ℓ Y').hom ≫ (Functor.rightUnitor _).hom) ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq =
    Functor.whiskerRight (Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ f)
        (boundedConstructibleLowerStarId ℓ Y).hom ≫ (Functor.rightUnitor _).hom)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) := by
  have hb : (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
      (Profinite.padicAlgClRingObj ℓ) ℓ (isPullback_ofIsOpenImmersion_overI sq)).hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq = 𝟙 _ := by
    rw [← boundedConstructibleOpenImmersionLowerShriekBaseChange_ofIsOpenImmersion_eq ℓ sq]
    simp [boundedConstructibleOpenImmersionLowerShriekBaseChangeIso]
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChange_eq]
  exact Functor.whiskerLeft_comp_whiskerRight_comp_aux
    (jS := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (Compactification.ofIsOpenImmersion f.left).overI)
    (P := boundedConstructibleLowerStar ℓ
      (Compactification.ofIsOpenImmersion f.left).overG)
    (G := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    (G' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
    (jS' := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (Compactification.ofIsOpenImmersion f'.left).overI)
    (P' := boundedConstructibleLowerStar ℓ
      (Compactification.ofIsOpenImmersion f'.left).overG)
    (boundedConstructibleLowerStarId ℓ Y) (boundedConstructibleLowerStarId ℓ Y') _
    (boundedConstructibleBaseChange_ofIsOpenImmersion ℓ (f := f) (f' := f') (g := g)) _ _ hb

/-- **`Ex_!` for open immersions is the extension-by-zero base change**: through `Rf_! ≅ f_!` and
`Rf'_! ≅ f'_!`, the compact-support base change of a cartesian square with `f` and `f'` open
immersions, followed by the extension-by-zero exchange morphism `Lg'^* f'_! ⟶ f_! Lg^*`, is the
identity of `Lg^* f_!` (blueprint `def-exchange-projection`). -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_comp_isoOpen
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq ≫
        Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f').hom ≫
        boundedConstructibleOpenImmersionLowerShriekBaseChange' (Profinite.padicAlgClRingObj ℓ) ℓ
          sq.toCommSq =
      Functor.whiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl
        ℓ f).hom (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange ℓ sq
      (Compactification.ofIsOpenImmersion f.left) (Compactification.ofIsOpenImmersion f'.left)
      (ofIsOpenImmersionBaseChangeHom g) (isPullback_ofIsOpenImmersion_overI sq)
      isPullback_ofIsOpenImmersion_overG]
  have hc : Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (Compactification.ofIsOpenImmersion f'.left) (compactificationOverField f')).hom ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (compactificationOverField f') (Compactification.ofIsOpenImmersion f'.left)).hom = 𝟙 _ := by
    rw [← Functor.whiskerLeft_comp, ← Iso.trans_hom,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_trans,
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl]
    simp
  have hP := boundedConstructibleLowerShriekOfCompactificationBaseChange_ofIsOpenImmersion ℓ sq
  simp only [boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, Functor.whiskerRight_comp,
    Category.assoc] at hP ⊢
  rw [reassoc_of% hc, hP]

end AlgebraicGeometry.ProEtale.CondensedRing
