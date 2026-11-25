/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import WeilConjectures.WeilSheaf.ArtinSchreierPullback
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.WeilSheaf.UpperStarExact
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# The Artin–Schreier sheaf of the inverse character

The reflection `x ↦ -x` of the affine line commutes with the Artin–Schreier map, so it acts on
`AS_* ℚ̄_ℓ`, conjugating the translation `σ_c` into `σ_{-c}`; it therefore carries the
`ψ`-isotypic component `ℒ_ψ` to the `ψ⁻¹`-isotypic component `ℒ_{ψ⁻¹}` (blueprint
`lemma-artin-schreier-character-sheaf`).

## Main declarations

- `AlgebraicGeometry.ProEtale.adicLowerStarExchange`: the exchange morphism
  `b_* g_* ℚ̄_ℓ ⟶ g_* ℚ̄_ℓ` attached to `g ≫ b = a⁻¹ ≫ g`, with its compatibilities with deck
  actions and with other exchange morphisms (computed on sections).
- `AlgebraicGeometry.WeilSheaf.artinSchreierNegHom`: the action
  `[-1]_* AS_* ℚ̄_ℓ ⟶ AS_* ℚ̄_ℓ` of the reflection, a morphism of Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.nonempty_iso_image_artinSchreierIdempotent_inv`:
  `ℒ_{ψ⁻¹} ≅ [-1]^* ℒ_ψ`.
- `AlgebraicGeometry.nonempty_artinSchreier_inv_iso`: `ℒ_{ψ⁻¹(a x)} ≅ ℒ_{ψ(-a x)}`.

## Implementation notes

To keep kernel checks cheap, morphisms of `ℓ`-adic sheaves are compared with their underlying
sheaf morphisms only by rewriting (never by `rfl` between differently presented composites), and
the objects at which natural transformations are evaluated are rewritten to a common form first
(e.g. `AlgebraicGeometry.ProEtale.lowerStarComp_hom_app_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The exchange morphism `b_* g_* ℚ̄_ℓ ≅ (g ≫ b)_* ℚ̄_ℓ = (a⁻¹ ≫ g)_* ℚ̄_ℓ ≅ g_* (a⁻¹)_* ℚ̄_ℓ
≅ g_* ℚ̄_ℓ` attached to an automorphism `a` of `X` and a morphism `b` with
`g ≫ b = a⁻¹ ≫ g`. -/
noncomputable def lowerStarExchangeStr {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ⟶ Y)
    (hg : g ≫ b = a.inv ≫ g) :
    (b)_*[WeilCoefficients.{u} l].obj ((g)_*[WeilCoefficients.{u} l].obj
      (adicConstantSheaf l X)) ⟶ (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) :=
  ((lowerStarComp _ g b ≪≫ lowerStarCongr _ hg ≪≫
      (lowerStarComp _ a.inv g).symm).app (adicConstantSheaf l X) ≪≫
    (g)_*[WeilCoefficients.{u} l].mapIso (adicConstantSheafLowerStarIso l a.symm)).hom

/-- The composition isomorphism of pushforwards at `ℚ̄_ℓ`, seen as the unit `ℓ`-adic sheaf. -/
lemma lowerStarComp_hom_app_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStarComp (WeilCoefficients.{u} l) f g).hom.app (AdicSheaf.unit l X).X =
      (lowerStarComp _ f g).hom.app (adicConstantSheaf l X) :=
  rfl

/-- The inverse composition isomorphism of pushforwards at `ℚ̄_ℓ`, seen as the unit `ℓ`-adic
sheaf. -/
lemma lowerStarComp_inv_app_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (lowerStarComp (WeilCoefficients.{u} l) f g).inv.app (AdicSheaf.unit l X).X =
      (lowerStarComp _ f g).inv.app (adicConstantSheaf l X) :=
  rfl

/-- The congruence isomorphism of pushforwards at `ℚ̄_ℓ`, seen as the unit `ℓ`-adic sheaf. -/
lemma lowerStarCongr_hom_app_unit {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (lowerStarCongr (WeilCoefficients.{u} l) h).hom.app (AdicSheaf.unit l X).X =
      (lowerStarCongr _ h).hom.app (adicConstantSheaf l X) :=
  rfl

/-- `AlgebraicGeometry.ProEtale.lowerStarExchangeStr` as a composite. -/
lemma lowerStarExchangeStr_eq {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ⟶ Y)
    (hg : g ≫ b = a.inv ≫ g) :
    lowerStarExchangeStr (l := l) g a b hg =
      (lowerStarComp _ g b).hom.app (adicConstantSheaf l X) ≫
        (lowerStarCongr _ hg).hom.app (adicConstantSheaf l X) ≫
        (lowerStarComp _ a.inv g).inv.app (adicConstantSheaf l X) ≫
        (g)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l a.symm).hom := by
  simp only [lowerStarExchangeStr, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    NatTrans.comp_app, Category.assoc]

/-- The action of an automorphism `σ` of `X` over `Y` on `g_* ℚ̄_ℓ,X`, pulling back sections
along `σ`. -/
noncomputable def lowerStarDeckAction {X Y : Scheme.{u}} (g : X ⟶ Y) (σ : X ≅ X)
    (hσ : σ.hom ≫ g = g) :
    (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) ⟶
      (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) :=
  (g)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l σ).inv ≫
    (lowerStarComp _ σ.hom g).hom.app (adicConstantSheaf l X) ≫
    (lowerStarCongr _ hσ).hom.app (adicConstantSheaf l X)

/-- A variant of `AlgebraicGeometry.ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange`:
if `a ≫ σ = σ' ≫ a`, the exchange morphism of `(a, b)` intertwines the actions of `σ` and `σ'`.
-/
lemma lowerStar_map_lowerStarDeckAction_comp_lowerStarExchangeStr {X Y : Scheme.{u}}
    (g : X ⟶ Y) (a : X ≅ X) (b : Y ⟶ Y) (σ σ' : X ≅ X) (hg : g ≫ b = a.inv ≫ g)
    (hσ : σ.hom ≫ g = g) (hσ' : σ'.hom ≫ g = g) (hσa : a.hom ≫ σ.hom = σ'.hom ≫ a.hom) :
    (b)_*[WeilCoefficients.{u} l].map (lowerStarDeckAction (l := l) g σ hσ) ≫
        lowerStarExchangeStr g a b hg =
      lowerStarExchangeStr g a b hg ≫ lowerStarDeckAction g σ' hσ' := by
  ext V : 3
  simp only [lowerStarExchangeStr, lowerStarDeckAction, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app',
    Quiver.Hom.unop_op, unop_op, lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, adicConstantSheafLowerStarIso_inv_hom_app,
    adicConstantSheafLowerStarIso_hom_hom_app, adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
        Iso.symm_inv, MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
        Category.comp_id, NatIso.ofComponents_inv_app, MorphismProperty.Over.isoMk_inv_left,
        pullback.congrHom_inv, MorphismProperty.Over.pullbackComp_hom_app_left,
        Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, limit.lift_π,
        PullbackCone.mk_π_app, pullbackLeftPullbackSndIso_hom_fst, limit.lift_π_assoc,
        cospan_left]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp only [pullback.lift_fst]
      exact Category.id_comp _
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, ← reassoc_of% hσa, hσ]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, hσa]


/-- `AlgebraicGeometry.ProEtale.pullbackLeftPullbackSndIso_inv_fst` with the base change of an
object of the pro-étale site written as such. -/
@[reassoc]
lemma pullbackLeftPullbackSndIso_inv_fst_fst_over {X Y Z : Scheme.{u}} (b : Z ⟶ Y) (V : Y.ProEt)
    (g : X ⟶ Z) :
    (pullbackLeftPullbackSndIso V.hom b g).inv ≫
        pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V).hom g ≫
          pullback.fst V.hom b = pullback.fst _ _ :=
  pullbackLeftPullbackSndIso_inv_fst _ _ _

/-- `pullbackLeftPullbackSndIso_hom_fst` with the base change of an object of the pro-étale site
written as such. -/
@[reassoc]
lemma pullbackLeftPullbackSndIso_hom_fst_over {Y Z W : Scheme.{u}} (b : Z ⟶ Y) (V : Y.ProEt)
    (c : W ⟶ Z) :
    (pullbackLeftPullbackSndIso V.hom b c).hom ≫ pullback.fst V.hom (c ≫ b) =
      pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V).hom c ≫
        pullback.fst V.hom b :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- A variant of `AlgebraicGeometry.ProEtale.pullbackLeftPullbackSndIso_inv_fst_fst_over` with an
identity morphism. -/
lemma pullbackLeftPullbackSndIso_inv_id_fst_fst_over {X Y Z : Scheme.{u}} (b : Z ⟶ Y)
    (V : Y.ProEt) (g : X ⟶ Z) :
    (pullbackLeftPullbackSndIso V.hom b g).inv ≫
      𝟙 ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V)).left ≫
        pullback.fst ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ b).obj V).hom g ≫
          pullback.fst V.hom b = pullback.fst _ _ := by
  erw [Category.id_comp]
  exact pullbackLeftPullbackSndIso_inv_fst _ _ _

/-- Exchange morphisms of commuting pairs of automorphisms commute. -/
lemma lowerStarExchangeStr_comm {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ⟶ Y)
    (a' : X ≅ X) (b' : Y ⟶ Y)
    (hg : g ≫ b = a.inv ≫ g) (hg' : g ≫ b' = a'.inv ≫ g)
    (haa' : a.inv ≫ a'.inv = a'.inv ≫ a.inv) (hbb' : b ≫ b' = b' ≫ b) :
    (b')_*[WeilCoefficients.{u} l].map (lowerStarExchangeStr (l := l) g a b hg) ≫
        lowerStarExchangeStr g a' b' hg' =
      ((lowerStarComp _ b b' ≪≫ lowerStarCongr _ hbb' ≪≫
          (lowerStarComp _ b' b).symm).app _).hom ≫
        (b)_*[WeilCoefficients.{u} l].map (lowerStarExchangeStr g a' b' hg') ≫
        lowerStarExchangeStr g a b hg := by
  ext V : 3
  have e₁ := @lowerStar_map_hom_app' (WeilCoefficients.{u} l) _
  have e₂ := @lowerStar_obj_obj_map' (WeilCoefficients.{u} l) _
  simp only [lowerStarExchangeStr, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, e₁,
    Quiver.Hom.unop_op, unop_op, lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, adicConstantSheafLowerStarIso_hom_hom_app,
    adicConstantSheaf_obj_map, e₂]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  have h₁ : a'.hom ≫ a.hom = a.hom ≫ a'.hom := by
    rw [← cancel_epi a'.inv, ← cancel_epi a.inv]
    simp [reassoc_of% haa']
  have h₂ : a'.hom ≫ a.inv = a.inv ≫ a'.hom := by
    calc a'.hom ≫ a.inv = a.inv ≫ (a.hom ≫ a'.hom) ≫ a.inv := by simp
      _ = a.inv ≫ (a'.hom ≫ a.hom) ≫ a.inv := by rw [h₁]
      _ = a.inv ≫ a'.hom := by simp
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [MorphismProperty.Over.pullbackCongr]
        simp [-pullbackLeftPullbackSndIso_hom_fst, -pullbackLeftPullbackSndIso_hom_fst_assoc,
          pullbackLeftPullbackSndIso_inv_fst_fst_over_assoc,
          pullbackLeftPullbackSndIso_inv_fst_fst_over,
          pullbackLeftPullbackSndIso_hom_fst_over_assoc, pullbackLeftPullbackSndIso_hom_fst_over]
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, hg, reassoc_of% h₂]
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, reassoc_of% h₁]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, h₁]

/-- The underlying inverse of `AlgebraicGeometry.ProEtale.adicLowerStarUnitIso`. -/
lemma adicLowerStarUnitIso_inv_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (adicLowerStarUnitIso l e).inv.hom = (adicConstantSheafLowerStarIso l e).inv :=
  rfl

/-- The exchange morphism `b_* g_* ℚ̄_ℓ ⟶ g_* ℚ̄_ℓ` of
`AlgebraicGeometry.ProEtale.lowerStarExchangeStr`, as a morphism of `ℓ`-adic sheaves. -/
noncomputable def adicLowerStarExchange {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X) (b : Y ⟶ Y)
    (hg : g ≫ b = a.inv ≫ g) :
    (b)_*ᵃ[l].obj ((g)_*ᵃ[l].obj (AdicSheaf.unit l X)) ⟶ (g)_*ᵃ[l].obj (AdicSheaf.unit l X) :=
  (adicLowerStarComp l g b).hom.app _ ≫ (adicLowerStarCongr l hg).hom.app _ ≫
    (adicLowerStarComp l a.inv g).inv.app _ ≫ (g)_*ᵃ[l].map (adicLowerStarUnitIso l a.symm).hom

/-- The action of an automorphism `σ` of `X` over `Y` on `g_* ℚ̄_ℓ`, as a morphism of `ℓ`-adic
sheaves. -/
noncomputable def adicLowerStarDeckAction {X Y : Scheme.{u}} (g : X ⟶ Y) (σ : X ≅ X)
    (hσ : σ.hom ≫ g = g) :
    (g)_*ᵃ[l].obj (AdicSheaf.unit l X) ⟶ (g)_*ᵃ[l].obj (AdicSheaf.unit l X) :=
  (g)_*ᵃ[l].map (adicLowerStarUnitIso l σ).inv ≫ (adicLowerStarComp l σ.hom g).hom.app _ ≫
    (adicLowerStarCongr l hσ).hom.app _

/-- The exchange morphism intertwines the deck actions of `σ` and `σ'` if `a ≫ σ = σ' ≫ a`, as
morphisms of `ℓ`-adic sheaves. -/
lemma adicLowerStar_map_deckAction_comp_exchange {X Y : Scheme.{u}}
    (g : X ⟶ Y) (a : X ≅ X) (b : Y ⟶ Y) (σ σ' : X ≅ X) (hg : g ≫ b = a.inv ≫ g)
    (hσ : σ.hom ≫ g = g) (hσ' : σ'.hom ≫ g = g) (hσa : a.hom ≫ σ.hom = σ'.hom ≫ a.hom) :
    (b)_*ᵃ[l].map (adicLowerStarDeckAction g σ hσ) ≫ adicLowerStarExchange g a b hg =
      adicLowerStarExchange g a b hg ≫ adicLowerStarDeckAction g σ' hσ' := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarDeckAction,
    adicLowerStarDeckAction, adicLowerStarExchange]
  repeat rw [Mod.comp_hom']
  repeat rw [adicLowerStarComp_hom_app_hom]
  repeat rw [adicLowerStarCongr_hom_app_hom]
  repeat rw [adicLowerStarComp_inv_app_hom]
  repeat rw [adicLowerStar_map_hom]
  rw [adicLowerStarUnitIso_hom_hom, adicLowerStarUnitIso_inv_hom, adicLowerStarUnitIso_inv_hom]
  repeat rw [lowerStarComp_hom_app_unit]
  repeat rw [lowerStarComp_inv_app_unit]
  repeat rw [lowerStarCongr_hom_app_unit]
  have := lowerStar_map_lowerStarDeckAction_comp_lowerStarExchangeStr (l := l) g a b σ σ' hg hσ
    hσ' hσa
  rw [lowerStarExchangeStr_eq, lowerStarDeckAction, lowerStarDeckAction] at this
  exact this

/-- The composition isomorphism of pushforwards at `g_* ℚ̄_ℓ`, seen as an `ℓ`-adic sheaf. -/
lemma lowerStarComp_hom_app_lowerStar_unit {X Y Z T : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (h : Z ⟶ T) :
    (lowerStarComp (WeilCoefficients.{u} l) f h).hom.app ((g)_*ᵃ[l].obj (AdicSheaf.unit l X)).X =
      (lowerStarComp _ f h).hom.app
        ((g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X)) :=
  rfl

/-- The inverse composition isomorphism of pushforwards at `g_* ℚ̄_ℓ`, seen as an `ℓ`-adic
sheaf. -/
lemma lowerStarComp_inv_app_lowerStar_unit {X Y Z T : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (h : Z ⟶ T) :
    (lowerStarComp (WeilCoefficients.{u} l) f h).inv.app ((g)_*ᵃ[l].obj (AdicSheaf.unit l X)).X =
      (lowerStarComp _ f h).inv.app
        ((g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X)) :=
  rfl

/-- The congruence isomorphism of pushforwards at `g_* ℚ̄_ℓ`, seen as an `ℓ`-adic sheaf. -/
lemma lowerStarCongr_hom_app_lowerStar_unit {X Y Z : Scheme.{u}} (g : X ⟶ Y) {f h : Y ⟶ Z}
    (e : f = h) :
    (lowerStarCongr (WeilCoefficients.{u} l) e).hom.app ((g)_*ᵃ[l].obj (AdicSheaf.unit l X)).X =
      (lowerStarCongr _ e).hom.app
        ((g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X)) :=
  rfl

/-- The exchange morphisms of commuting pairs of automorphisms commute, as morphisms of `ℓ`-adic
sheaves (from `AlgebraicGeometry.ProEtale.lowerStarExchangeStr_comm`). -/
lemma adicLowerStar_map_exchange_comp_exchange {X Y : Scheme.{u}} (g : X ⟶ Y) (a : X ≅ X)
    (b : Y ⟶ Y) (a' : X ≅ X) (b' : Y ⟶ Y)
    (hg : g ≫ b = a.inv ≫ g) (hg' : g ≫ b' = a'.inv ≫ g)
    (haa' : a.inv ≫ a'.inv = a'.inv ≫ a.inv) (hbb' : b ≫ b' = b' ≫ b) :
    (b')_*ᵃ[l].map (adicLowerStarExchange g a b hg) ≫ adicLowerStarExchange g a' b' hg' =
      (adicLowerStarComp l b b').hom.app _ ≫ (adicLowerStarCongr l hbb').hom.app _ ≫
        (adicLowerStarComp l b' b).inv.app _ ≫ (b)_*ᵃ[l].map (adicLowerStarExchange g a' b' hg') ≫
        adicLowerStarExchange g a b hg := by
  refine Mod.hom_ext _ _ ?_
  rw [adicLowerStarExchange, adicLowerStarExchange]
  repeat rw [Mod.comp_hom']
  repeat rw [adicLowerStar_map_hom]
  repeat rw [Mod.comp_hom']
  repeat rw [adicLowerStarComp_hom_app_hom]
  repeat rw [adicLowerStarCongr_hom_app_hom]
  repeat rw [adicLowerStarComp_inv_app_hom]
  repeat rw [adicLowerStar_map_hom]
  repeat rw [adicLowerStarUnitIso_hom_hom]
  repeat rw [lowerStarComp_hom_app_unit]
  repeat rw [lowerStarComp_inv_app_unit]
  repeat rw [lowerStarCongr_hom_app_unit]
  rw [lowerStarComp_hom_app_lowerStar_unit, lowerStarComp_inv_app_lowerStar_unit,
    lowerStarCongr_hom_app_lowerStar_unit]
  have := lowerStarExchangeStr_comm (l := l) g a b a' b' hg hg' haa' hbb'
  simp only [lowerStarExchangeStr_eq, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc] at this
  exact this

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open scoped ProEtale

section AffineLine

variable (k₀ : Type u) [Field k₀]

/-- The scaling by `-1` is an involution. -/
@[reassoc]
lemma affineLine.smul_neg_one_comp_smul_neg_one :
    affineLine.smul k₀ (-1) ≫ affineLine.smul k₀ (-1) = 𝟙 _ := by
  rw [← affineLine.smul_mul, neg_one_mul, neg_neg, affineLine.smul_one]

/-- The scaling `[c]` conjugates translations: `σ_a ≫ [c] = [c] ≫ σ_{c a}`. -/
lemma affineLine.translation_comp_smul (a c : k₀) :
    affineLine.translation k₀ a ≫ affineLine.smul k₀ c =
      affineLine.smul k₀ c ≫ affineLine.translation k₀ (c * a) := by
  refine AffineSpace.hom_ext (by simp [affineLine.translation, affineLine.smul]) fun _ ↦ ?_
  simp only [affineLine.translation, affineLine.smul, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.smul_appTop_coord, AffineSpace.translation_appTop_coord,
    map_mul, map_add]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.translation_over,
    AffineSpace.smul_over]
  ring

variable [Finite k₀]

/-- The scaling `[c]` commutes with the Artin–Schreier map, as `c ^ q = c`. -/
@[reassoc]
lemma affineLine.smul_comp_artinSchreierMap (c : k₀) :
    affineLine.smul k₀ c ≫ affineLine.artinSchreierMap k₀ =
      affineLine.artinSchreierMap k₀ ≫ affineLine.smul k₀ c := by
  let := Fintype.ofFinite k₀
  refine AffineSpace.hom_ext (by simp [affineLine.smul, affineLine.artinSchreierMap]) fun _ ↦ ?_
  simp only [affineLine.smul, affineLine.artinSchreierMap, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, AffineSpace.smul_appTop_coord,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow, map_mul]
  simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    AffineSpace.artinSchreierMap_over]
  rw [mul_pow, ← map_pow, ← map_pow, FiniteField.pow_card]
  ring

omit [Finite k₀] in
/-- The reflection `x ↦ -x` of the geometric affine line, an involution. -/
noncomputable def affineLine.geometricNegIso :
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber where
  hom := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _)
  inv := Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _)
  hom_inv_id := by
    rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_id]
    congr 1
    exact affineLine.smul_neg_one_comp_smul_neg_one k₀
  inv_hom_id := by
    rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_id]
    congr 1
    exact affineLine.smul_neg_one_comp_smul_neg_one k₀

omit [Finite k₀] in
lemma affineLine.geometricNegIso_inv :
    (affineLine.geometricNegIso k₀).inv = (affineLine.geometricNegIso k₀).hom :=
  rfl

/-- The base change of `AS ≫ [-1] = [-1] ≫ AS`. -/
lemma affineLine.geometricArtinSchreierMap_comp_geometricNegIso :
    affineLine.geometricArtinSchreierMap k₀ ≫ (affineLine.geometricNegIso k₀).inv =
      (affineLine.geometricNegIso k₀).inv ≫ affineLine.geometricArtinSchreierMap k₀ := by
  simp only [affineLine.geometricNegIso, affineLine.geometricArtinSchreierMap]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  congr 1
  exact (affineLine.smul_comp_artinSchreierMap k₀ (-1)).symm

/-- `AlgebraicGeometry.affineLine.geometricArtinSchreierMap_comp_geometricNegIso` with the
reflection on the left written as a base change. -/
lemma affineLine.geometricArtinSchreierMap_comp_geometricFiberMap_smul_neg_one :
    affineLine.geometricArtinSchreierMap k₀ ≫
        Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _) =
      (affineLine.geometricNegIso k₀).inv ≫ affineLine.geometricArtinSchreierMap k₀ :=
  affineLine.geometricArtinSchreierMap_comp_geometricNegIso k₀

omit [Finite k₀] in
/-- The base change of `[-1] ≫ σ_c = σ_{-c} ≫ [-1]`. -/
lemma affineLine.geometricNegIso_comp_geometricTranslationIso (c : k₀) :
    (affineLine.geometricNegIso k₀).hom ≫ (affineLine.geometricTranslationIso k₀ c).hom =
      (affineLine.geometricTranslationIso k₀ (-c)).hom ≫ (affineLine.geometricNegIso k₀).hom := by
  simp only [affineLine.geometricNegIso, affineLine.geometricTranslationIso]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  congr 1
  rw [affineLine.translation_comp_smul, neg_one_mul, neg_neg]

/-- The reflection of the geometric affine line commutes with the geometric Frobenius. -/
lemma affineLine.geometricNegIso_inv_comp_frobenius_inv :
    (affineLine.geometricNegIso k₀).inv ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≫
        (affineLine.geometricNegIso k₀).inv :=
  Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ (comp_over _ _)

end AffineLine

end AlgebraicGeometry

namespace AlgebraicGeometry

open scoped ProEtale

section NegWeil

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

instance : IsIso (affineLine.smul k₀ (-1)) :=
  ⟨⟨_, affineLine.smul_neg_one_comp_smul_neg_one k₀,
    affineLine.smul_neg_one_comp_smul_neg_one k₀⟩⟩

section Carrier

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The composition isomorphism of pushforwards at the underlying sheaf of `ℚ̄_ℓ`, as the unit
`ℓ`-adic sheaf (stated to rewrite with, see the implementation notes). -/
lemma WeilSheaf.adicConstant_carrier_comp_hom {Z T : Scheme.{u}}
    (f : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶ Z) (h : Z ⟶ T) :
    (ProEtale.adicLowerStarComp l f h).hom.app (WeilSheaf.adicConstant k₀ l X).obj.carrier =
      (ProEtale.adicLowerStarComp l f h).hom.app (ProEtale.AdicSheaf.unit l _) :=
  rfl

/-- The inverse composition isomorphism of pushforwards at the underlying sheaf of `ℚ̄_ℓ`. -/
lemma WeilSheaf.adicConstant_carrier_comp_inv {Z T : Scheme.{u}}
    (f : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶ Z) (h : Z ⟶ T) :
    (ProEtale.adicLowerStarComp l f h).inv.app (WeilSheaf.adicConstant k₀ l X).obj.carrier =
      (ProEtale.adicLowerStarComp l f h).inv.app (ProEtale.AdicSheaf.unit l _) :=
  rfl

/-- The congruence isomorphism of pushforwards at the underlying sheaf of `ℚ̄_ℓ`. -/
lemma WeilSheaf.adicConstant_carrier_congr_hom {Z : Scheme.{u}}
    {f h : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ⟶ Z} (e : f = h) :
    (ProEtale.adicLowerStarCongr l e).hom.app (WeilSheaf.adicConstant k₀ l X).obj.carrier =
      (ProEtale.adicLowerStarCongr l e).hom.app (ProEtale.AdicSheaf.unit l _) :=
  rfl

/-- The Weil structure of `ℚ̄_ℓ`, as a morphism of `ℓ`-adic sheaves. -/
lemma WeilSheaf.adicConstant_str_hom :
    (Endofunctor.IsoAlgebra.str (WeilSheaf.adicConstant k₀ l X).obj).hom =
      (ProEtale.adicLowerStarUnitIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom :=
  rfl

end Carrier

section Generic

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
  [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The Weil structure of the pushforward `φ_* ℚ̄_ℓ` is the exchange morphism of the base change
`φ̄` with the geometric Frobenii. -/
lemma WeilSheaf.lowerStar_adicConstant_obj_obj_str :
    ((WeilSheaf.lowerStar φ).obj (WeilSheaf.adicConstant k₀ l X)).obj.obj.str =
      ProEtale.adicLowerStarExchange (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) := by
  rw [← Endofunctor.IsoAlgebra.str_hom, WeilSheaf.lowerStar_obj_obj_str, Iso.trans_hom,
    Iso.app_hom, ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom,
    Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom]
  rw [WeilSheaf.adicConstant_carrier_comp_hom, WeilSheaf.adicConstant_carrier_comp_inv,
    WeilSheaf.adicConstant_carrier_congr_hom, WeilSheaf.adicConstant_str_hom,
    ProEtale.adicLowerStarExchange]
  rw [Category.assoc, Category.assoc]

end Generic

/-- The Weil structure of `AS_* ℚ̄_ℓ` is the exchange morphism of `ĀS` with the geometric
Frobenius. -/
lemma WeilSheaf.artinSchreierPushforward_obj_obj_str :
    (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str =
      ProEtale.adicLowerStarExchange ĀS
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) :=
  WeilSheaf.lowerStar_adicConstant_obj_obj_str (affineLine.artinSchreierMap k₀)

/-- The composition isomorphism of pushforwards at the underlying sheaf of `AS_* ℚ̄_ℓ`. -/
lemma WeilSheaf.artinSchreierPushforward_carrier_comp_hom {Z T : Scheme.{u}}
    (f : Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ⟶ Z)
    (h : Z ⟶ T) :
    (ProEtale.adicLowerStarComp l f h).hom.app
        (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier =
      (ProEtale.adicLowerStarComp l f h).hom.app
        ((ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l _)) :=
  rfl

/-- The inverse composition isomorphism of pushforwards at the underlying sheaf of
`AS_* ℚ̄_ℓ`. -/
lemma WeilSheaf.artinSchreierPushforward_carrier_comp_inv {Z T : Scheme.{u}}
    (f : Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ⟶ Z)
    (h : Z ⟶ T) :
    (ProEtale.adicLowerStarComp l f h).inv.app
        (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier =
      (ProEtale.adicLowerStarComp l f h).inv.app
        ((ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l _)) :=
  rfl

/-- The congruence isomorphism of pushforwards at the underlying sheaf of `AS_* ℚ̄_ℓ`. -/
lemma WeilSheaf.artinSchreierPushforward_carrier_congr_hom {Z : Scheme.{u}}
    {f h : Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ⟶ Z}
    (e : f = h) :
    (ProEtale.adicLowerStarCongr l e).hom.app
        (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier =
      (ProEtale.adicLowerStarCongr l e).hom.app
        ((ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l _)) :=
  rfl

variable (k₀ l) in
/-- The action of the reflection `x ↦ -x` on `AS_* ℚ̄_ℓ`, as a morphism of `ℓ`-adic sheaves
`[-1]_* ĀS_* ℚ̄_ℓ ≅ (ĀS ≫ [-1])_* ℚ̄_ℓ = ([-1] ≫ ĀS)_* ℚ̄_ℓ ≅ ĀS_* [-1]_* ℚ̄_ℓ ≅ ĀS_* ℚ̄_ℓ`. -/
noncomputable def affineLine.artinSchreierNegModHom :
    (Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _))_*ᵃ[l].obj
        ((ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l _)) ⟶
      (ĀS)_*ᵃ[l].obj (ProEtale.AdicSheaf.unit l _) :=
  ProEtale.adicLowerStarExchange ĀS (affineLine.geometricNegIso k₀)
    (Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _))
    (affineLine.geometricArtinSchreierMap_comp_geometricFiberMap_smul_neg_one k₀)

/-- The action of the reflection on `AS_* ℚ̄_ℓ` commutes with the Weil structures: the
reflection and the Artin–Schreier map are defined over `k₀`. -/
lemma affineLine.artinSchreierNegModHom_comm :
    (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀)).map
        (affineLine.artinSchreierNegModHom k₀ l) ≫
      (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str =
    ((WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).obj
      (WeilSheaf.artinSchreierPushforward k₀ l)).obj.obj.str ≫
      affineLine.artinSchreierNegModHom k₀ l := by
  rw [WeilSheaf.artinSchreierPushforward_obj_obj_str, ← Endofunctor.IsoAlgebra.str_hom,
    WeilSheaf.lowerStar_obj_obj_str, Iso.trans_hom,
    Iso.app_hom, ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.trans_hom,
    Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom,
    Endofunctor.IsoAlgebra.str_hom, WeilSheaf.artinSchreierPushforward_obj_obj_str]
  rw [WeilSheaf.artinSchreierPushforward_carrier_comp_hom,
    WeilSheaf.artinSchreierPushforward_carrier_comp_inv,
    WeilSheaf.artinSchreierPushforward_carrier_congr_hom, affineLine.artinSchreierNegModHom]
  simp only [Category.assoc]
  exact ProEtale.adicLowerStar_map_exchange_comp_exchange _ _ _ _ _ _ _
    (affineLine.geometricNegIso_inv_comp_frobenius_inv k₀)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)

variable (k₀ l) in
/-- The action of the reflection `x ↦ -x` on `AS_* ℚ̄_ℓ`, as a morphism of Weil sheaves
`[-1]_* AS_* ℚ̄_ℓ ⟶ AS_* ℚ̄_ℓ`. -/
noncomputable def WeilSheaf.artinSchreierNegHom :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).obj
        (WeilSheaf.artinSchreierPushforward k₀ l) ⟶ WeilSheaf.artinSchreierPushforward k₀ l :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ⟨affineLine.artinSchreierNegModHom k₀ l, affineLine.artinSchreierNegModHom_comm⟩)

/-- Morphisms of Weil sheaves agree if their underlying morphisms of `ℓ`-adic sheaves do. -/
lemma WeilSheaf.hom_ext_of_hom_hom_f {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    {F G : WeilSheaf k₀ l X} {f g : F ⟶ G} (h : f.hom.hom.f = g.hom.hom.f) : f = g :=
  ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext h))

omit [Fact (ringChar k₀ ≠ l)] in
/-- The action of `σ_c` on `ĀS_* ℚ̄_ℓ` is the deck action of the translation. -/
lemma artinSchreierTranslationSheafHom_eq (c : k₀) :
    artinSchreierTranslationSheafHom l c = ProEtale.adicLowerStarDeckAction ĀS
      (affineLine.geometricTranslationIso k₀ c)
      (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c) :=
  rfl

/-- The reflection conjugates the translation `σ_c` into `σ_{-c}`. -/
lemma WeilSheaf.lowerStar_map_artinSchreierTranslationAction_comp_artinSchreierNegHom (c : k₀) :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).map
        (WeilSheaf.artinSchreierTranslationAction l c) ≫ WeilSheaf.artinSchreierNegHom k₀ l =
      WeilSheaf.artinSchreierNegHom k₀ l ≫ WeilSheaf.artinSchreierTranslationAction l (-c) := by
  refine WeilSheaf.hom_ext_of_hom_hom_f ?_
  have := ProEtale.adicLowerStar_map_deckAction_comp_exchange (l := l) ĀS
    (affineLine.geometricNegIso k₀)
    (Scheme.Hom.geometricFiberMap (affineLine.smul k₀ (-1)) (comp_over _ _))
    (affineLine.geometricTranslationIso k₀ c) (affineLine.geometricTranslationIso k₀ (-c))
    (affineLine.geometricArtinSchreierMap_comp_geometricFiberMap_smul_neg_one k₀)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀ (-c))
    (affineLine.geometricNegIso_comp_geometricTranslationIso k₀ c)
  rw [← artinSchreierTranslationSheafHom_eq, ← artinSchreierTranslationSheafHom_eq] at this
  exact this

/-- The reflection commutes with the multiplication by scalars. -/
lemma WeilSheaf.lowerStar_map_smulEnd_comp_artinSchreierNegHom (b : PadicAlgCl l) :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).map
        (WeilSheaf.smulEnd b (WeilSheaf.artinSchreierPushforward k₀ l)) ≫
        WeilSheaf.artinSchreierNegHom k₀ l =
      WeilSheaf.artinSchreierNegHom k₀ l ≫
        WeilSheaf.smulEnd b (WeilSheaf.artinSchreierPushforward k₀ l) := by
  refine WeilSheaf.hom_ext_of_hom_hom_f ?_
  exact (congrArg (· ≫ affineLine.artinSchreierNegModHom k₀ l)
    (ProEtale.AdicSheaf.adicLowerStar_map_smul _ _ _)).trans (ProEtale.AdicSheaf.smul_comp _ _)

/-- The reflection carries the projector `e_ψ` to `e_{ψ⁻¹}`. -/
lemma WeilSheaf.lowerStar_map_artinSchreierIdempotent_comp_artinSchreierNegHom
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    (WeilSheaf.lowerStar (affineLine.smul k₀ (-1))).map (WeilSheaf.artinSchreierIdempotent ψ) ≫
        WeilSheaf.artinSchreierNegHom k₀ l =
      WeilSheaf.artinSchreierNegHom k₀ l ≫ WeilSheaf.artinSchreierIdempotent ψ⁻¹ := by
  let := Fintype.ofFinite k₀
  simp only [WeilSheaf.artinSchreierIdempotent, Functor.map_sum, Functor.map_comp,
    Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
    WeilSheaf.lowerStar_map_artinSchreierTranslationAction_comp_artinSchreierNegHom,
    reassoc_of% WeilSheaf.lowerStar_map_smulEnd_comp_artinSchreierNegHom]
  refine Fintype.sum_equiv (Equiv.neg k₀) _ _ fun c ↦ ?_
  rw [Equiv.neg_apply, neg_neg, AddChar.inv_apply]

instance : IsIso (affineLine.artinSchreierNegModHom k₀ l) := by
  unfold affineLine.artinSchreierNegModHom ProEtale.adicLowerStarExchange
  infer_instance

instance : IsIso (WeilSheaf.artinSchreierNegHom k₀ l) := by
  have : IsIso (WeilSheaf.artinSchreierNegHom k₀ l).hom.hom.f :=
    inferInstanceAs (IsIso (affineLine.artinSchreierNegModHom k₀ l))
  exact WeilSheaf.isIso_of_isIso_hom_hom_f _

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

variable (k₀ l) in
/-- The pullback along the reflection `x ↦ -x` is an involution. -/
noncomputable def WeilSheaf.upperStarNegUnitIso :
    𝟭 (WeilSheaf k₀ l (affineLine k₀)) ≅
      WeilSheaf.upperStar (affineLine.smul k₀ (-1)) ⋙
        WeilSheaf.upperStar (affineLine.smul k₀ (-1)) :=
  (WeilSheaf.upperStarIdIso _).symm ≪≫
    WeilSheaf.upperStarCongr (affineLine.smul_neg_one_comp_smul_neg_one k₀).symm ≪≫
    WeilSheaf.upperStarCompIso _ _

variable (k₀ l) in
/-- The pullback along the reflection `x ↦ -x` is the pushforward along it: both are right
adjoint to the pullback, which is a self-inverse equivalence. -/
noncomputable def WeilSheaf.upperStarNegIsoLowerStarNeg :
    WeilSheaf.upperStar (k₀ := k₀) (l := l) (affineLine.smul k₀ (-1)) ≅
      WeilSheaf.lowerStar (affineLine.smul k₀ (-1)) :=
  (CategoryTheory.Equivalence.mk _ _ (WeilSheaf.upperStarNegUnitIso k₀ l)
    (WeilSheaf.upperStarNegUnitIso k₀ l).symm).toAdjunction.rightAdjointUniq
    (WeilSheaf.upperStarLowerStarAdjunction (affineLine.smul k₀ (-1)))

/-- `φ^* F ≅ g'^* G` for `F ≅ g^* G` and `φ ≫ g = g'`. -/
theorem WeilSheaf.nonempty_iso_upperStar_obj_of_iso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X)
    (g : X ⟶ X) (g' : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [g.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
    (h : φ ≫ g = g') {F G : WeilSheaf k₀ l X} (e : F ≅ (WeilSheaf.upperStar g).obj G) :
    Nonempty ((WeilSheaf.upperStar φ).obj F ≅ (WeilSheaf.upperStar g').obj G) := by
  obtain ⟨e'⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj φ g g' h G
  exact ⟨(WeilSheaf.upperStar φ).mapIso e ≪≫ e'⟩

/-- Blueprint `lemma-artin-schreier-character-sheaf`: `ℒ_{ψ⁻¹} ≅ [-1]^* ℒ_ψ`, the reflection
carrying the projector `e_ψ` of `AS_* ℚ̄_ℓ` to `e_{ψ⁻¹}`. -/
theorem WeilSheaf.nonempty_iso_image_artinSchreierIdempotent_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (image (WeilSheaf.artinSchreierIdempotent ψ⁻¹) ≅
      (WeilSheaf.upperStar (affineLine.smul k₀ (-1))).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ))) := by
  obtain ⟨i₁⟩ := nonempty_iso_image_of_comp_eq
    ((WeilSheaf.upperStarNegIsoLowerStarNeg k₀ l).app _)
    ((WeilSheaf.upperStar (affineLine.smul k₀ (-1))).map (WeilSheaf.artinSchreierIdempotent ψ))
    _ ((WeilSheaf.upperStarNegIsoLowerStarNeg k₀ l).hom.naturality _)
  obtain ⟨i₂⟩ := nonempty_iso_image_of_comp_eq (asIso (WeilSheaf.artinSchreierNegHom k₀ l)) _ _
    (WeilSheaf.lowerStar_map_artinSchreierIdempotent_comp_artinSchreierNegHom ψ)
  obtain ⟨i₃⟩ := nonempty_iso_obj_image (WeilSheaf.upperStar (k₀ := k₀) (l := l)
    (affineLine.smul k₀ (-1))) (WeilSheaf.artinSchreierIdempotent ψ)
  exact ⟨i₂.symm ≪≫ i₁.symm ≪≫ i₃.symm⟩

/-- `[a]^* ℒ_{ψ⁻¹} ≅ [-a]^* ℒ_ψ`. -/
theorem WeilSheaf.nonempty_iso_upperStar_smul_image_inv (ψ : AddChar k₀ (PadicAlgCl l))
    (a : k₀) :
    Nonempty ((WeilSheaf.upperStar (affineLine.smul k₀ a)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ⁻¹)) ≅
      (WeilSheaf.upperStar (affineLine.smul k₀ (-a))).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ))) := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_iso_image_artinSchreierIdempotent_inv (l := l) ψ
  exact WeilSheaf.nonempty_iso_upperStar_obj_of_iso (affineLine.smul k₀ a)
    (affineLine.smul k₀ (-1)) (affineLine.smul k₀ (-a))
    (by rw [← affineLine.smul_mul, mul_neg_one]) e

/-- Blueprint `lemma-artin-schreier-character-sheaf` (the clause `ℒ_{ψ⁻¹,f} ≅ ℒ_{ψ,-f}` for
`f = a x`): `ℒ_{ψ⁻¹(a x)} ≅ ℒ_{ψ(-a x)}`. -/
theorem nonempty_artinSchreier_inv_iso (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty (artinSchreier ψ⁻¹ a ≅ artinSchreier ψ (-a)) := by
  rw [artinSchreier, artinSchreier, WeilSheaf.image_artinSchreierIdempotent_eq ψ⁻¹,
    WeilSheaf.image_artinSchreierIdempotent_eq ψ]
  exact WeilSheaf.nonempty_iso_upperStar_smul_image_inv ψ a

end NegWeil

end AlgebraicGeometry
