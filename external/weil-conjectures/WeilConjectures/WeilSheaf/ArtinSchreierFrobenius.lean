/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# The counit of the Artin–Schreier pushforward and the Frobenius

Let `ĀS : 𝔸¹_{k̄} ⟶ 𝔸¹_{k̄}` be the geometric Artin–Schreier map. The counit
`ε : ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `ĀS^* ⊣ ĀS_*`, which evaluates a function on the fibres of `ĀS`
at the given point of the fibre, is compatible with the Weil structures of `AS_* ℚ̄_ℓ` and of
`ℚ̄_ℓ` (`AlgebraicGeometry.affineLine.artinSchreierCounit_frobenius`), and its pullback along a
translation `σ̄_c` is the evaluation along `x ↦ (x, σ̄_c x)`
(`AlgebraicGeometry.affineLine.artinSchreierCounit_translation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀
local notation "𝐅𝐫" =>
  Aut.asIso (Scheme.Hom.geometricGaloisFrobenius (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
local notation "Frₕ" =>
  Iso.hom (Aut.asIso
    (Scheme.Hom.geometricGaloisFrobenius (affineLine k₀ ↘ Spec (CommRingCat.of k₀))))

variable (k₀ l) in
/-- The counit `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `ĀS^* ⊣ ĀS_*` at the constant sheaf. -/
noncomputable abbrev affineLine.artinSchreierCounit :
    (ĀS)^*[WeilCoefficients.{u} l].obj ((ĀS)_*[WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ⟶
      ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).counit.app _

variable (k₀ l) in
/-- The Weil structure `Fr^* ĀS_* ℚ̄_ℓ ⟶ ĀS_* ℚ̄_ℓ` of `AS_* ℚ̄_ℓ`, through `Fr^* ≅ (Fr⁻¹)_*`, the
exchange of `ĀS_*` with `(Fr⁻¹)_*` and the Weil structure of `ℚ̄_ℓ`. -/
noncomputable def affineLine.artinSchreierPushforwardStr :
    (Frₕ)^*[WeilCoefficients.{u} l].obj ((ĀS)_*[WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ⟶
      (ĀS)_*[WeilCoefficients.{u} l].obj
        (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (ProEtale.upperStarIsoLowerStarInv _ (𝐅𝐫)).hom.app _ ≫
    ((ProEtale.lowerStarComp _ (affineLine.geometricArtinSchreierMap k₀) (𝐅𝐫).inv ≪≫
        ProEtale.lowerStarCongr _
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
        (ProEtale.lowerStarComp _ (𝐅𝐫).inv (affineLine.geometricArtinSchreierMap k₀)).symm).app
        (ProEtale.adicConstantSheaf l
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫
      (affineLine.geometricArtinSchreierMap k₀)_*[WeilCoefficients.{u} l].mapIso
        (ProEtale.adicConstantSheafLowerStarIso l (𝐅𝐫).symm)).hom

/-- The Weil structure of `AS_* ℚ̄_ℓ`, on underlying sheaves. -/
lemma affineLine.frobeniusStr_artinSchreierPushforward :
    (WeilSheaf.artinSchreierPushforward k₀ l).frobeniusStr =
      affineLine.artinSchreierPushforwardStr k₀ l := by
  exact congrArg ((ProEtale.upperStarIsoLowerStarInv _ _).hom.app _ ≫ ·)
    artinSchreierPushforward_str_hom_hom

set_option linter.flexible false in
omit [Fact (ringChar k₀ ≠ l)] in
/-- The pushforward-level identity behind
`AlgebraicGeometry.affineLine.artinSchreierCounit_frobenius`. -/
lemma affineLine.lowerStar_map_adicConstantSheafToLowerStar_frobenius :
    (ĀS)_*[WeilCoefficients.{u} l].map (ProEtale.adicConstantSheafToLowerStar l Frₕ) ≫
        (ProEtale.lowerStarFactor _ (rfl : Frₕ ≫ ĀS = Frₕ ≫ ĀS)).hom.app
          (ProEtale.adicConstantSheaf l _) =
      (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) Frₕ).unit.app _ ≫
        (Frₕ)_*[WeilCoefficients.{u} l].map (affineLine.artinSchreierPushforwardStr k₀ l) ≫
        (ProEtale.lowerStarFactor _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          (affineLine.artinSchreierMap k₀) (comp_over _ _))).hom.app
          (ProEtale.adicConstantSheaf l _) := by
  have hu := ProEtale.upperStarLowerStarAdjunction_unit_app_comp_map_upperStarIsoLowerStarInv
    (WeilCoefficients.{u} l) (𝐅𝐫)
    ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _))
  rw [affineLine.artinSchreierPushforwardStr, Functor.map_comp, Category.assoc, reassoc_of% hu]
  ext V : 3
  ext x
  refine ProEtale.adicConstantSheaf_ext fun y ↦ ?_
  simp only [ProEtale.lowerStarUnit, Iso.trans_inv, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    ProEtale.lowerStarFactor_inv_app_hom_app, ProEtale.lowerStarFactor_hom_app_hom_app,
    ProEtale.lowerStarId_inv_app_hom_app, ProEtale.lowerStar_map_hom_app',
    ProEtale.lowerStarComp_hom_app_hom_app, ProEtale.lowerStarComp_inv_app_hom_app,
    ProEtale.lowerStarCongr_hom_app_hom_app, ProEtale.adicConstantSheafLowerStarIso_hom_hom_app,
    ProEtale.adicConstantSheaf_obj_map, ProEtale.lowerStar_obj_obj_map',
    ProEtale.adicConstantSheafToLowerStar_hom_app, ← Functor.map_comp, ← op_comp]
  refine congrArg (fun φ : _ ⟶ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ ĀS).obj
    V.unop).left ↦ x.down.1 (φ.base y)) ?_
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp,
      MorphismProperty.Over.pullbackId]

omit [Fact (ringChar k₀ ≠ l)] in
/-- The counit `ε : ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is compatible with the Weil structures of `AS_* ℚ̄_ℓ`
and of `ℚ̄_ℓ`, the latter being the canonical morphism `Fr^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. -/
lemma affineLine.artinSchreierCounit_frobenius :
    (ProEtale.upperStarComp _ Frₕ ĀS).hom.app ((ĀS)_*[WeilCoefficients.{u} l].obj
        (ProEtale.adicConstantSheaf l _)) ≫
        (Frₕ)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierCounit k₀ l) ≫
        ProEtale.upperStarAdicConstantSheafHom l Frₕ =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          (affineLine.artinSchreierMap k₀) (comp_over _ _)).symm).hom.app
          ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _)) ≫
        (ProEtale.upperStarComp _ ĀS Frₕ).hom.app
          ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _)) ≫
        (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierPushforwardStr k₀ l) ≫
        affineLine.artinSchreierCounit k₀ l := by
  apply ((ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
    (Frₕ ≫ ĀS)).homEquiv _ _).injective
  have h₁ : ProEtale.upperStarAdicConstantSheafHom l Frₕ =
      (Frₕ)^*[WeilCoefficients.{u} l].map (ProEtale.adicConstantSheafToLowerStar l Frₕ) ≫
        (ProEtale.upperStarLowerStarAdjunction _ Frₕ).counit.app _ :=
    Adjunction.homEquiv_counit _ _ _ _
  have e₁ := ProEtale.homEquiv_upperStarFactor_hom_app_comp_counit
    (rfl : Frₕ ≫ ĀS = Frₕ ≫ ĀS) ((ĀS)_*[WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l _)) (ProEtale.adicConstantSheaf l _)
    (affineLine.artinSchreierCounit k₀ l ≫ ProEtale.adicConstantSheafToLowerStar l Frₕ)
  have e₂ := ProEtale.homEquiv_upperStarFactor_hom_app_comp_counit
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius (affineLine.artinSchreierMap k₀)
      (comp_over _ _) : ĀS ≫ Frₕ = Frₕ ≫ ĀS)
    ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _))
    (ProEtale.adicConstantSheaf l _) (affineLine.artinSchreierPushforwardStr k₀ l)
  rw [ProEtale.upperStarFactor_rfl, Functor.map_comp, Category.assoc, ← h₁] at e₁
  simp only [Functor.id_obj] at e₁ e₂
  rw [ProEtale.upperStarFactor_hom_app, Category.assoc] at e₂
  rw [e₁, e₂]
  have tri : (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).unit.app _ ≫
      (ĀS)_*[WeilCoefficients.{u} l].map (affineLine.artinSchreierCounit k₀ l) = 𝟙 _ :=
    (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).right_triangle_components _
  rw [Functor.map_comp, Category.assoc, reassoc_of% tri]
  exact affineLine.lowerStar_map_adicConstantSheafToLowerStar_frobenius

variable (l) in
/-- The action of the translation `σ_c` on `ĀS_* ℚ̄_ℓ`, pulling back sections along `σ̄_c`. -/
noncomputable def affineLine.artinSchreierTranslation (c : k₀) :
    (ĀS)_*[WeilCoefficients.{u} l].obj
        (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⟶
      (ĀS)_*[WeilCoefficients.{u} l].obj
        (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  (ĀS)_*[WeilCoefficients.{u} l].map
      (ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom) ≫
    (ProEtale.lowerStarComp (WeilCoefficients.{u} l) (affineLine.geometricTranslationIso k₀ c).hom
      ĀS).hom.app (ProEtale.adicConstantSheaf l _) ≫
    (ProEtale.lowerStarCongr (WeilCoefficients.{u} l)
      (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
      (ProEtale.adicConstantSheaf l _)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The evaluation along `x ↦ (x, σ̄_c x)` is the pullback of the translation action followed by
the counit. -/
lemma affineLine.artinSchreierEvalHom_hom (c : k₀) :
    (affineLine.artinSchreierEvalHom l c).hom =
      (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierTranslation l c) ≫
        affineLine.artinSchreierCounit k₀ l := by
  rw [affineLine.artinSchreierEvalHom, Mod.comp_hom', ProEtale.adicUpperStar_map_hom]
  erw [Adjunction.modAdjunction_counit_app_hom]
  rw [artinSchreierTranslationSheafHom_hom, ProEtale.adicConstantSheafLowerStarIso_inv]
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
/-- The pullback of the counit `ε : ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` along the translation `σ̄_c` is the
evaluation along `x ↦ (x, σ̄_c x)`. -/
lemma affineLine.artinSchreierCounit_translation (c : k₀) :
    (ProEtale.upperStarComp _ (affineLine.geometricTranslationIso k₀ c).hom ĀS).hom.app
        ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _)) ≫
        ((affineLine.geometricTranslationIso k₀ c).hom)^*[WeilCoefficients.{u} l].map
          (affineLine.artinSchreierCounit k₀ l) ≫
        ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ c).hom =
      (ProEtale.upperStarCongr _
          (affineLine.geometricTranslation_comp_artinSchreierMap k₀ c)).hom.app
          ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _)) ≫
        (ĀS)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierTranslation l c) ≫
        affineLine.artinSchreierCounit k₀ l := by
  apply ((ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
    ((affineLine.geometricTranslationIso k₀ c).hom ≫ ĀS)).homEquiv _ _).injective
  have h₁ : ProEtale.upperStarAdicConstantSheafHom l (affineLine.geometricTranslationIso k₀ c).hom =
      ((affineLine.geometricTranslationIso k₀ c).hom)^*[WeilCoefficients.{u} l].map
        (ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom) ≫
        (ProEtale.upperStarLowerStarAdjunction _
          (affineLine.geometricTranslationIso k₀ c).hom).counit.app _ :=
    Adjunction.homEquiv_counit _ _ _ _
  have e₁ := ProEtale.homEquiv_upperStarFactor_hom_app_comp_counit
    (rfl : (affineLine.geometricTranslationIso k₀ c).hom ≫ ĀS = _)
    ((ĀS)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l _))
    (ProEtale.adicConstantSheaf l _)
    (affineLine.artinSchreierCounit k₀ l ≫
      ProEtale.adicConstantSheafToLowerStar l (affineLine.geometricTranslationIso k₀ c).hom)
  rw [ProEtale.upperStarFactor_rfl, Functor.map_comp, Category.assoc, ← h₁] at e₁
  simp only [Functor.id_obj] at e₁
  rw [e₁, ProEtale.homEquiv_upperStarCongr_hom_app_comp, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_unit]
  have tri : (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).unit.app _ ≫
      (ĀS)_*[WeilCoefficients.{u} l].map (affineLine.artinSchreierCounit k₀ l) = 𝟙 _ :=
    (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).right_triangle_components _
  rw [Functor.map_comp, Category.assoc, reassoc_of% tri, tri]
  simp only [Functor.id_obj, Category.comp_id, affineLine.artinSchreierTranslation,
    Category.assoc, ProEtale.lowerStarCongr, eqToIso.hom, eqToHom_app, eqToHom_trans,
    eqToHom_refl]
  rw [← ProEtale.lowerStarComp_trans_lowerStarCongr, ProEtale.lowerStarCongr_rfl, Iso.trans_refl]


omit [Finite k₀] in
/-- The translation by `0` of the geometric affine line is the identity. -/
lemma affineLine.geometricTranslationIso_zero_hom :
    (affineLine.geometricTranslationIso k₀ 0).hom = 𝟙 _ := by
  have key : ∀ (φ : affineLine k₀ ⟶ affineLine k₀)
      (h : φ ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = _), φ = 𝟙 _ →
        Scheme.Hom.geometricFiberMap φ h = 𝟙 _ := by
    rintro _ _ rfl
    exact Scheme.Hom.geometricFiberMap_id
  exact key _ (comp_over (affineLine.translation k₀ 0) (Spec (CommRingCat.of k₀)))
    (affineLine.translation_zero k₀)

omit [Fact (ringChar k₀ ≠ l)] in
/-- The translation action on `ĀS_* ℚ̄_ℓ`, on underlying sheaves. -/
lemma affineLine.artinSchreierTranslation_eq (c : k₀) :
    affineLine.artinSchreierTranslation l c = (artinSchreierTranslationSheafHom l c).hom := by
  rw [artinSchreierTranslationSheafHom_hom, ProEtale.adicConstantSheafLowerStarIso_inv]
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
/-- The translation by `0` acts trivially on `ĀS_* ℚ̄_ℓ`. -/
lemma affineLine.artinSchreierTranslation_zero :
    affineLine.artinSchreierTranslation (k₀ := k₀) l 0 = 𝟙 _ := by
  rw [affineLine.artinSchreierTranslation_eq]
  ext ⟨U⟩ : 3
  rw [artinSchreierTranslationSheafHom_hom_app, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app]
  have h : (pullback.map U.hom ĀS U.hom ĀS (𝟙 _) (affineLine.geometricTranslationIso k₀ 0).hom
      (𝟙 _) (by simp) (by simp [affineLine.geometricTranslation_comp_artinSchreierMap]) :
        pullback U.hom ĀS ⟶ pullback U.hom ĀS) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [affineLine.geometricTranslationIso_zero_hom]
  rw [h, op_id, CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry
