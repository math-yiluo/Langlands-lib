/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.RadicialDescent

/-!
# Changing the base of the generic constructibility property

Let `q : B ⟶ S` be of finite type and let `Y` be a `B`-scheme via `fYB : Y ⟶ B`. If over an open
`V ⊆ B` the direct image along `j : X ⟶ Y` is bounded constructible and commutes with base change
(as `B`-schemes), then, over all of `S`, the same holds for the restriction of `j` to the open
`G = fYB⁻¹(V)` of `Y`, viewed as an `S`-scheme
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.restrict_of_base`): for a noetherian
`T ⟶ S`, the base change `G_T = G ×_S T` is also `Y ×_B V_T` with `V_T = V ×_S T` open in
`B ×_S T`, which is noetherian. This is how the first step of the proof of
`theorem-generic-constructibility-base-change-rj` uses the induction hypothesis over `𝔸¹_S` for a
coordinate `Y ⟶ 𝔸¹_S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Horizontal pasting, at an object, the other way**: for two squares pasted horizontally, if
the derived base change map of the pasted square is an isomorphism at `K` and `h^*` of that of the
right square is an isomorphism at `K`, then the derived base change map of the left square is an
isomorphism at `g'^* K`. -/
lemma isIso_derivedBaseChangeMapPlus_app_of_paste_horiz {X'' X' X Y'' Y' Y : Scheme.{u}}
    {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'}
    {g : Y' ⟶ Y} (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g))
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h₁ : IsIso (((h)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₁).app K)))
    (hsq : IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K)) :
    IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq₂).app
      (((g')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K)) := by
  have e := NatTrans.congr_app
    (derivedBaseChangeMapPlus_paste_horiz (ModuleCat.{u + 1} Λ) sq₁ sq₂ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj] at e
  rw [e, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at hsq
  exact hsq

/-- An open subscheme of a noetherian scheme is noetherian. -/
lemma isNoetherian_opens {T : Scheme.{u}} [IsNoetherian T] (W : T.Opens) : IsNoetherian W :=
  { __ := LocallyOfFiniteType.isLocallyNoetherian W.ι
    __ := QuasiCompact.compactSpace_of_compactSpace W.ι }

/-- **Changing the base**: let `q : B ⟶ S` be of finite type, `fYB : Y ⟶ B`, `j : X ⟶ Y` and
`V ⊆ B` open. If the direct image along `j` of `K` is bounded constructible and commutes with base
change over `V`, as `B`-schemes, then the same holds over every `U ⊆ S`, as `S`-schemes, for the
restriction of `j` to the open `fYB⁻¹(V)` of `Y`. -/
theorem HasDirectImageBaseChangeOnPlus.restrict_of_base {S B X Y : Scheme.{u}} (q : B ⟶ S)
    [LocallyOfFiniteType q] [QuasiCompact q] (fYB : Y ⟶ B) (j : X ⟶ Y)
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (V : B.Opens) (h : HasDirectImageBaseChangeOnPlus Λ fYB j K V) (U : Set S) :
    HasDirectImageBaseChangeOnPlus Λ ((fYB ⁻¹ᵁ V).ι ≫ fYB ≫ q) (j ∣_ (fYB ⁻¹ᵁ V))
      ((((j ⁻¹ᵁ (fYB ⁻¹ᵁ V)).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj K) U := by
  intro T _ t _ GT XT gG fGT gX jT hG sq
  -- `T₂ = B ×_S T` and its open `T₃ = V ×_S T`, both noetherian
  let T₂ := pullback t q
  let p₂ : T₂ ⟶ T := pullback.fst t q
  let q₂ : T₂ ⟶ B := pullback.snd t q
  have hT₂ : IsPullback p₂ q₂ t q := IsPullback.of_hasPullback t q
  have : LocallyOfFiniteType p₂ := MorphismProperty.pullback_fst t q inferInstance
  have : QuasiCompact p₂ := MorphismProperty.pullback_fst t q inferInstance
  have : IsNoetherian T₂ :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian p₂
      __ := QuasiCompact.compactSpace_of_compactSpace p₂ }
  let T₃ := q₂ ⁻¹ᵁ V
  have : IsNoetherian T₃ := isNoetherian_opens T₃
  let ψ : T₃.toScheme ⟶ V := q₂ ∣_ V
  have hT₃ : IsPullback ψ (T₃.ι ≫ p₂) (V.ι ≫ q) t :=
    (isPullback_morphismRestrict q₂ V).paste_vert hT₂.flip
  -- the map `G_T ⟶ T₃`
  let φ : GT ⟶ T₂ := pullback.lift fGT (gG ≫ (fYB ⁻¹ᵁ V).ι ≫ fYB) (by
    rw [Category.assoc, Category.assoc, ← hG.w])
  have hφ : Set.range φ ⊆ Set.range T₃.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    change q₂ (φ x) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    exact (gG x).2
  let φ' : GT ⟶ T₃ := IsOpenImmersion.lift T₃.ι φ hφ
  have hφ' : φ' ≫ T₃.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have hleft : IsPullback gG φ' (fYB ∣_ V) ψ := by
    refine IsPullback.of_bot ?_ ?_ hT₃
    · rw [← Category.assoc φ', hφ', pullback.lift_fst, ← Category.assoc, morphismRestrict_ι,
        Category.assoc]
      exact hG
    · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, Category.assoc,
        morphismRestrict_ι, ← Category.assoc φ', hφ', pullback.lift_snd]
  have hY : IsPullback (gG ≫ (fYB ⁻¹ᵁ V).ι) φ' fYB (ψ ≫ V.ι) :=
    hleft.paste_horiz (isPullback_morphismRestrict fYB V).flip
  have hRj : IsPullback (j ⁻¹ᵁ (fYB ⁻¹ᵁ V)).ι (j ∣_ (fYB ⁻¹ᵁ V)) j (fYB ⁻¹ᵁ V).ι :=
    (isPullback_morphismRestrict j (fYB ⁻¹ᵁ V)).flip
  have hX : IsPullback (gX ≫ (j ⁻¹ᵁ (fYB ⁻¹ᵁ V)).ι) jT j (gG ≫ (fYB ⁻¹ᵁ V).ι) :=
    sq.paste_horiz hRj
  have hrange : Set.range (ψ ≫ V.ι) ⊆ (V : Set B) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (ψ x).2
  obtain ⟨c, i⟩ := h T₃ (ψ ≫ V.ι) hrange GT XT (gG ≫ (fYB ⁻¹ᵁ V).ι) φ'
    (gX ≫ (j ⁻¹ᵁ (fYB ⁻¹ᵁ V)).ι) jT hY hX
  refine ⟨ObjectProperty.prop_of_iso _ (_root_.DerivedCategory.Plus.ι.mapIso
    ((jT)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) gX (j ⁻¹ᵁ (fYB ⁻¹ᵁ V)).ι).app
        K))) c, ?_⟩
  have := isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) hRj
  exact isIso_derivedBaseChangeMapPlus_app_of_paste_horiz hRj.toCommSq sq.toCommSq _ K
    inferInstance i

end Etale

end AlgebraicGeometry
