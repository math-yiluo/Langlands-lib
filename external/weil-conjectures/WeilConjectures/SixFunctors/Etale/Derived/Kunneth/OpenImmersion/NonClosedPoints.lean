/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.NonClosedBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Torsion
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLimit
public import WeilConjectures.AlgebraicGeometry.ClosedPointsFiberProduct

/-!
# Base change along open immersions at non-closed points

This file contains the two "stalks over points with positive transcendence degree" steps of the
proof of blueprint `corollary-open-direct-image-over-field--2`: if the statement holds for all data
with smaller `dim X + dim Y`, then the base change map is an isomorphism on the geometric stalk at
every point `z ∈ X ×_K Y` whose image in `X` (resp. in `Y`) is not closed. The proof base changes
the square to the strict henselization `X' = Spec O^{sh}_{X,x}` (resp. `Y' = Spec O^{sh}_{Y,y}`),
a limit of étale `X`-schemes (smooth base change in the limit form, blueprint
`corollary-open-direct-image-over-field--2`), writes it as a limit of affine schemes of finite type
and smaller dimension over a separably closed field `L` (blueprint
`corollary-open-direct-image-over-field--2`), and passes to the limit (blueprint
`corollary-open-direct-image-over-field--2`, with `corollary-open-direct-image-over-field--2` for
the open `U`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Adding a finite dimension is strictly monotone on `WithBot ℕ∞`. -/
lemma WithBot.add_coe_lt_add_coe_of_ne_top {a b : WithBot ℕ∞} {c : ℕ∞} (hab : a < b)
    (hc : c ≠ ⊤) : a + c < b + c := by
  obtain ⟨b', rfl⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_gt hab)
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, ← WithBot.coe_add]
    exact WithBot.bot_lt_coe _
  | coe a' =>
    rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe]
    exact (ENat.add_lt_add_iff_right hc).2 (WithBot.coe_lt_coe.1 hab)

/-- If `dim A < dim X` and `Y` is a nonempty scheme of finite type over a field, then
`dim A + dim Y < dim X + dim Y`. -/
lemma topologicalKrullDim_add_lt_add {K : Type u} [Field K] {A X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY] [QuasiCompact aY] (y : Y)
    (h : topologicalKrullDim A < topologicalKrullDim X) :
    topologicalKrullDim A + topologicalKrullDim Y < topologicalKrullDim X + topologicalKrullDim Y
    := by
  have hY0 : topologicalKrullDim Y ≠ ⊥ := by
    rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    exact ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.1 hY0
  have hct : c ≠ ⊤ := by
    rintro rfl
    exact (topologicalKrullDim_lt_top_of_finiteType aY).ne hc.symm
  rw [← hc]
  exact WithBot.add_coe_lt_add_coe_of_ne_top h hct

/-- If `X` lies over a field in which `n ≠ 0` is invertible, and `n` kills `Λ`, then every
sheaf of `Λ`-modules is torsion of orders invertible on `X`. -/
lemma isTorsionSheafOfInvertibleOrder_of_field {K : Type u} [Field K] {X T : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (n : ℕ) (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder X F := by
  have hn0 : (n : K) ≠ 0 := hn.ne_zero
  refine IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n (by rintro rfl; simp at hn0) hΛ
    ?_ F
  simpa using ((isUnit_natCast_Γ_spec_iff (K := K) n).2 hn0).map a.appTop.hom

/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, stalks at points `z` whose image
`x` in `X` is not closed (so that `trdeg_K κ(x) > 0`): if
`corollary-open-direct-image-over-field--2` holds for all data with smaller `dim X + dim Y`, the
base change map is an isomorphism on the geometric stalk at `z`. -/
theorem Etale.isIso_sheafFiber_baseChangeHomologyMap_of_not_isClosed_fst {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0)
    (IH : Etale.OpenImmersionBaseChangeBelow Λ (topologicalKrullDim X + topologicalKrullDim Y))
    (z : W) (hz : ¬ IsClosed ({q₁.base z} : Set X)) (i : ℤ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let zb := W.algClosurePoint z
  let s := zb ≫ q₁
  have hs : ¬ IsClosed {s (IsLocalRing.closedPoint (AlgebraicClosure (W.residueField z)))} := by
    simpa [s, zb] using hz
  obtain ⟨L, _, _, _, ℓ, I, _, _, D, π, qD, ⟨hπ⟩, hℓK, hDaff, hDmap, hqlft, hπq, hqmap,
    hdimD⟩ := Scheme.exists_isLimit_strictLocalization_of_not_isClosed aX s hs
  let t := strictLocalizationToBase s
  let κ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  -- the base change of the square along `t : X' ⟶ X`
  let uX := pullback.fst q₁ t
  let q₁' := pullback.snd q₁ t
  have hX'W : uX ≫ q₁ = q₁' ≫ t := pullback.condition
  let uT := pullback.fst j t
  let j' := pullback.snd j t
  let uY := pullback.fst h uX
  let h' := pullback.snd h uX
  have c1 : uY ≫ h = h' ≫ uX := pullback.condition
  have hℓK' : ℓ ≫ κ = t ≫ aX := hℓK
  let e' : pullback h uX ⟶ pullback j t := pullback.lift (uY ≫ e) (h' ≫ q₁') (by
    rw [Category.assoc, sq.w, ← Category.assoc, c1, Category.assoc, hX'W, Category.assoc])
  have he : e' ≫ uT = uY ≫ e := pullback.lift_fst _ _ _
  have bT : IsPullback uT j' j t := IsPullback.of_hasPullback j t
  have bX : IsPullback uY h' h uX := IsPullback.of_hasPullback h uX
  have sq' : IsPullback e' h' j' q₁' := by
    have H := bX.paste_horiz sq
    rw [← he, hX'W] at H
    exact IsPullback.of_right H (pullback.lift_snd _ _ _) bT
  -- the side faces satisfy base change (blueprint `corollary-open-direct-image-over-field--2`)
  have hT : IsIso (Etale.baseChangeHomologyMap Λ bT i F) := by
    have := isTorsionSheafOfInvertibleOrder_of_field Λ aX n hn hΛ F
    exact Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization Λ s (𝟙 X) t (𝟙 _)
      IsPullback.of_id_snd j bT i F
  have hX : IsIso (Etale.baseChangeHomologyMap Λ bX i (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
    have := isTorsionSheafOfInvertibleOrder_of_field Λ (q₁ ≫ aX) n hn hΛ
      (((e)^*[ModuleCat.{u + 1} Λ]).obj F)
    have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    have : QuasiSeparated h :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
    exact Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization Λ s q₁ uX q₁'
      (IsPullback.of_hasPullback q₁ t) h bX i _
  -- the base changed square satisfies base change: limit argument
  have hF : IsIso (Etale.baseChangeHomologyMap Λ sq' i (((uT)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
    let aYL := pullback.snd aY κ
    let q₂' : pullback q₁ t ⟶ pullback aY κ := pullback.lift (uX ≫ q₂) (q₁' ≫ ℓ) (by
      rw [Category.assoc, ← hW.w, ← Category.assoc, hX'W, Category.assoc, Category.assoc, hℓK'])
    have hq₂ : q₂' ≫ pullback.fst aY κ = uX ≫ q₂ := pullback.lift_fst _ _ _
    have hWL : IsPullback q₁' q₂' ℓ aYL := by
      have H := (IsPullback.of_hasPullback q₁ t).paste_horiz hW.flip
      rw [← hℓK', ← hq₂] at H
      exact (IsPullback.of_right H (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback aY κ)).flip
    let qN : D ⟶ (Functor.const I).obj (Spec (.of L)) :=
      { app := qD
        naturality a b f := (hqmap f).trans (Category.comp_id _).symm }
    have : ∀ i, LocallyOfFiniteType (qN.app i) := hqlft
    have : ∀ i, IsAffine (D.obj i) := hDaff
    have : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (D.map f) := fun f ↦ hDmap f
    have : CompactSpace (pullback j t : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace j'
    have hn' : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
    refine Etale.isIso_baseChangeHomologyMap_of_isLimit_fst Λ aYL hπ qN ℓ hπq j' hWL sq' n hn'
      hΛ IH (fun k ↦ ?_) i _
    rw [topologicalKrullDim_pullback_eq_of_field aY κ]
    exact topologicalKrullDim_add_lt_add aY (q₂.base z) (hdimD k)
  have key := (Etale.isIso_baseChangeHomologyMap_iff_of_cube Λ sq bT sq' bX hX'W.symm he i F
    hT hX).1 hF
  let zb' : Spec (.of (AlgebraicClosure (W.residueField z))) ⟶ pullback q₁ t :=
    pullback.lift zb (Spec.map (strictHenselizationEval s))
      (spec_map_strictHenselizationEval_comp_strictLocalizationToBase s).symm
  exact Etale.isIso_sheafFiber_map_of_isIso_upperStar Λ uX _ key z zb' (pullback.lift_fst _ _ _)

/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, stalks at points `z` whose image
`y` in `Y` is not closed (so that `trdeg_K κ(y) > 0`): if
`corollary-open-direct-image-over-field--2` holds for all data with smaller `dim X + dim Y`, the
base change map is an isomorphism on the geometric stalk at `z`. This step also uses the base change
along the field extension `K ⊆ L` (blueprint `corollary-open-direct-image-over-field--2`). -/
theorem Etale.isIso_sheafFiber_baseChangeHomologyMap_of_not_isClosed_snd {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0)
    (IH : Etale.OpenImmersionBaseChangeBelow Λ (topologicalKrullDim X + topologicalKrullDim Y))
    (z : W) (hz : ¬ IsClosed ({q₂.base z} : Set Y)) (i : ℤ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  let zb := W.algClosurePoint z
  let s := zb ≫ q₂
  have hs : ¬ IsClosed {s (IsLocalRing.closedPoint (AlgebraicClosure (W.residueField z)))} := by
    simpa [s, zb] using hz
  obtain ⟨L, _, _, _, ℓ, I, _, _, D, π, qD, ⟨hπ⟩, hℓK, hDaff, hDmap, hqlft, hπq, hqmap,
    hdimD⟩ := Scheme.exists_isLimit_strictLocalization_of_not_isClosed aY s hs
  let t := strictLocalizationToBase s
  let κ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  -- `X_L`, `U_L` and `W' = W ×_Y Y'`
  let pX := pullback.fst aX κ
  let aXL := pullback.snd aX κ
  let uT := pullback.fst j pX
  let jL := pullback.snd j pX
  let uX := pullback.fst q₂ t
  let r := pullback.snd q₂ t
  have c2 : uX ≫ q₂ = r ≫ t := pullback.condition
  have hℓK' : ℓ ≫ κ = t ≫ aY := hℓK
  let p' : pullback q₂ t ⟶ pullback aX κ := pullback.lift (uX ≫ q₁) (r ≫ ℓ) (by
    rw [Category.assoc, hW.w, ← Category.assoc, c2, Category.assoc, Category.assoc, hℓK'])
  have hp : p' ≫ pX = uX ≫ q₁ := pullback.lift_fst _ _ _
  let uY := pullback.fst h uX
  let h' := pullback.snd h uX
  have c1 : uY ≫ h = h' ≫ uX := pullback.condition
  let e' : pullback h uX ⟶ pullback j pX := pullback.lift (uY ≫ e) (h' ≫ p') (by
    rw [Category.assoc, sq.w, ← Category.assoc, c1, Category.assoc, ← hp, Category.assoc])
  have he : e' ≫ uT = uY ≫ e := pullback.lift_fst _ _ _
  have bT : IsPullback uT jL j pX := IsPullback.of_hasPullback j pX
  have bX : IsPullback uY h' h uX := IsPullback.of_hasPullback h uX
  have sq' : IsPullback e' h' jL p' := by
    have H := bX.paste_horiz sq
    rw [← he, ← hp] at H
    exact IsPullback.of_right H (pullback.lift_snd _ _ _) bT
  -- base change along the field extension (blueprint `corollary-open-direct-image-over-field--2`)
  have hT : IsIso (Etale.baseChangeHomologyMap Λ bT i F) := by
    have := isTorsionSheafOfInvertibleOrder_of_field Λ (𝟙 (Spec (.of K))) n hn hΛ F
    exact Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ aX j pX aXL
      (IsPullback.of_hasPullback aX κ) bT i F
  -- base change along the strict localization (blueprint
  -- `corollary-open-direct-image-over-field--2`)
  have hX : IsIso (Etale.baseChangeHomologyMap Λ bX i (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
    have := isTorsionSheafOfInvertibleOrder_of_field Λ (q₁ ≫ aX) n hn hΛ
      (((e)^*[ModuleCat.{u + 1} Λ]).obj F)
    have : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
    have : QuasiSeparated h :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated) sq inferInstance
    exact Etale.isIso_baseChangeHomologyMap_of_isPullback_strictLocalization Λ s q₂ uX r
      (IsPullback.of_hasPullback q₂ t) h bX i _
  -- the upper square satisfies base change: limit argument
  have hF : IsIso (Etale.baseChangeHomologyMap Λ sq' i (((uT)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
    have hWL : IsPullback p' r aXL ℓ := by
      have H := (IsPullback.of_hasPullback q₂ t).paste_horiz hW
      rw [← hℓK', ← hp] at H
      exact IsPullback.of_right H (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback aX κ)
    let qN : D ⟶ (Functor.const I).obj (Spec (.of L)) :=
      { app := qD
        naturality a b f := (hqmap f).trans (Category.comp_id _).symm }
    have : ∀ i, LocallyOfFiniteType (qN.app i) := hqlft
    have : ∀ i, IsAffine (D.obj i) := hDaff
    have : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (D.map f) := fun f ↦ hDmap f
    have hn' : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
    refine Etale.isIso_baseChangeHomologyMap_of_isLimit_snd Λ aXL jL hπ qN ℓ hπq hWL sq' n hn'
      hΛ IH (fun k ↦ ?_) i _
    rw [topologicalKrullDim_pullback_eq_of_field aX κ, add_comm,
      add_comm (topologicalKrullDim X)]
    exact topologicalKrullDim_add_lt_add aX (q₁.base z) (hdimD k)
  have key := (Etale.isIso_baseChangeHomologyMap_iff_of_cube Λ sq bT sq' bX hp he i F
    hT hX).1 hF
  let zb' : Spec (.of (AlgebraicClosure (W.residueField z))) ⟶ pullback q₂ t :=
    pullback.lift zb (Spec.map (strictHenselizationEval s))
      (spec_map_strictHenselizationEval_comp_strictLocalizationToBase s).symm
  exact Etale.isIso_sheafFiber_map_of_isIso_upperStar Λ uX _ key z zb' (pullback.lift_fst _ _ _)

variable {Λ} in
/-- Proof of blueprint `corollary-open-direct-image-over-field--2`, stalks at non-closed points: a
point of `X ×_K Y` is closed if and only if both of its images are closed (blueprint
`corollary-open-direct-image-over-field--2`), so the two previous steps give the isomorphism on the
geometric stalks at all non-closed points, as soon as `corollary-open-direct-image-over-field--2`
holds for all data with smaller `dim X + dim Y`. -/
theorem Etale.openImmersionBaseChangeAtNonClosed_of_below {N : WithBot ℕ∞}
    (H : Etale.OpenImmersionBaseChangeBelow Λ N) :
    Etale.OpenImmersionBaseChangeAtNonClosed Λ N := by
  intro K _ X U Y W V aX aY _ _ _ _ j _ q₁ q₂ hW e h sq n hn hΛ hdim z hz i F
  have IH := H.mono hdim
  by_cases h₁ : IsClosed ({q₁.base z} : Set X)
  · by_cases h₂ : IsClosed ({q₂.base z} : Set Y)
    · exfalso
      refine hz ?_
      have e₁ : (pullback.fst aX aY).base (hW.isoPullback.hom.base z) = q₁.base z :=
        congrArg (fun f ↦ f.base z) hW.isoPullback_hom_fst
      have e₂ : (pullback.snd aX aY).base (hW.isoPullback.hom.base z) = q₂.base z :=
        congrArg (fun f ↦ f.base z) hW.isoPullback_hom_snd
      have hc := (Scheme.Pullback.isClosed_singleton_iff aX aY (hW.isoPullback.hom.base z)).2
        ⟨by rw [e₁]; exact h₁, by rw [e₂]; exact h₂⟩
      have hl : Function.LeftInverse hW.isoPullback.inv.base hW.isoPullback.hom.base :=
        fun w ↦ congrArg (fun f ↦ f.base w) hW.isoPullback.hom_inv_id
      have : ({z} : Set W) = hW.isoPullback.hom.base ⁻¹' {hW.isoPullback.hom.base z} := by
        ext w
        exact ⟨fun hw ↦ hw ▸ rfl, fun hw ↦ hl.injective hw⟩
      rw [this]
      exact hc.preimage hW.isoPullback.hom.continuous
    · exact Etale.isIso_sheafFiber_baseChangeHomologyMap_of_not_isClosed_snd Λ aX aY j q₁ q₂ hW
        e h sq n hn hΛ IH z h₂ i F
  · exact Etale.isIso_sheafFiber_baseChangeHomologyMap_of_not_isClosed_fst Λ aX aY j q₁ q₂ hW
      e h sq n hn hΛ IH z h₁ i F

end AlgebraicGeometry
