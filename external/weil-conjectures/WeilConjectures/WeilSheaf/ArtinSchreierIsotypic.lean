/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierPullback
public import WeilConjectures.WeilSheaf.IsotypicPullback

/-!
# The Artin–Schreier sheaf as an isotypic component

The Artin–Schreier map `AS : 𝔸¹ ⟶ 𝔸¹` is a `k₀`-torsor under the translations
(`AlgebraicGeometry.affineLine.isTorsorSplit_artinSchreierMap`), and the inclusion `ℒ_ψ ⟶ AS_* ℚ̄_ℓ`
of pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.artinSchreierImageι`)
is `ψ`-equivariant with invertible adjoint `AS^* ℒ_ψ ⟶ ℚ̄_ℓ` (blueprint
`lemma-artin-schreier-character-sheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open ProEtale
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

variable (k₀) in
/-- The translation `x ↦ x + c` of the affine line, as an automorphism. -/
noncomputable def affineLine.translationIso (c : k₀) : affineLine k₀ ≅ affineLine k₀ where
  hom := affineLine.translation k₀ c
  inv := affineLine.translation k₀ (-c)
  hom_inv_id := affineLine.translation_comp_translation_neg k₀ c
  inv_hom_id := affineLine.translation_neg_comp_translation k₀ c

/-- The translations of the affine line are defined over `k₀`. -/
instance (c : k₀) : (affineLine.translationIso k₀ c).hom.IsOver (Spec (CommRingCat.of k₀)) :=
  inferInstanceAs ((affineLine.translation k₀ c).IsOver (Spec (CommRingCat.of k₀)))

/-- The translations of the affine line lie over the Artin–Schreier map
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma affineLine.translationIso_comp_artinSchreierMap (c : k₀) :
    (affineLine.translationIso k₀ c).hom ≫ affineLine.artinSchreierMap k₀ =
      affineLine.artinSchreierMap k₀ :=
  affineLine.translation_comp_artinSchreierMap k₀ c

omit [Finite k₀] in
/-- Translation by `c + d` is translation by `c` followed by translation by `d`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma affineLine.translationIso_add (c d : k₀) :
    (affineLine.translationIso k₀ (c + d)).hom =
      (affineLine.translationIso k₀ c).hom ≫ (affineLine.translationIso k₀ d).hom :=
  affineLine.translation_add k₀ c d

/-- The Artin–Schreier map is a split `k₀`-torsor under the translations
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma affineLine.isTorsorSplit_artinSchreierMap :
    IsTorsorSplit (affineLine.artinSchreierMap k₀) (affineLine.translationIso k₀)
      (affineLine.translationIso_comp_artinSchreierMap) :=
  affineLine.isIso_sigmaDesc_lift_translation k₀

omit [Finite k₀] in
/-- The base change of the translations of the affine line are the geometric translations
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma affineLine.geometricTorsorAut_translationIso :
    (geometricTorsorAut k₀ (affineLine.translationIso k₀)) =
      affineLine.geometricTranslationIso k₀ :=
  funext fun _ ↦ Iso.ext rfl

/-- The translation of a torsor pushforward only depends on the automorphisms
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtale.torsorTranslation_congr {Z W : Scheme.{u}} (π : W ⟶ Z) {G : Type u}
    {τ τ' : G → (W ≅ W)} (e : τ = τ') (hτ : ∀ g, (τ g).hom ≫ π = π)
    (hτ' : ∀ g, (τ' g).hom ≫ π = π) (g : G) :
    torsorTranslation l π τ hτ g = torsorTranslation l π τ' hτ' g := by
  subst e
  rfl

variable [Fact (ringChar k₀ ≠ l)] (ψ : AddChar k₀ (PadicAlgCl l))

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

/-- The inclusion `ℒ_ψ ⟶ AS_* ℚ̄_ℓ` of pro-étale Weil sheaves. -/
noncomputable def ProEtaleWeilSheaf.artinSchreierImageι :
    (image (WeilSheaf.artinSchreierIdempotent ψ)).obj ⟶
      ProEtaleWeilSheaf.torsorPushforward k₀ l (affineLine.artinSchreierMap k₀) :=
  ObjectProperty.homMk ⟨(image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f, by
    have h := (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.h
    have hstr : (WeilSheaf.artinSchreierPushforward k₀ l).obj.obj.str =
        (ProEtaleWeilSheaf.torsorPushforward k₀ l (affineLine.artinSchreierMap k₀)).obj.str := by
      change ((WeilSheaf.lowerStar (affineLine.artinSchreierMap k₀)).obj
        (WeilSheaf.adicConstant k₀ l _)).obj.obj.str = _
      rw [← Endofunctor.IsoAlgebra.str_hom, ← Endofunctor.IsoAlgebra.str_hom,
        WeilSheaf.lowerStar_obj_obj_str, ProEtaleWeilSheaf.lowerStar_obj_str]
      rfl
    rw [hstr] at h
    exact h⟩

/-- The underlying morphism of `AlgebraicGeometry.ProEtaleWeilSheaf.artinSchreierImageι`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.artinSchreierImageι_hom_f :
    (ProEtaleWeilSheaf.artinSchreierImageι ψ).hom.f =
      (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f :=
  rfl


omit [Fact (ringChar k₀ ≠ l)] in
/-- The translations of `ĀS_* ℚ̄_ℓ` are the torsor translations
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma artinSchreierTranslationSheafHom_eq_torsorTranslation (c : k₀) :
    artinSchreierTranslationSheafHom l c = torsorTranslation l ĀS
      (geometricTorsorAut k₀ (affineLine.translationIso k₀))
      (geometricTorsorAut_comp k₀ (affineLine.artinSchreierMap k₀) (affineLine.translationIso k₀)
        affineLine.translationIso_comp_artinSchreierMap) c := by
  exact (ProEtale.torsorTranslation_congr ĀS affineLine.geometricTorsorAut_translationIso _
    (affineLine.geometricTranslation_comp_artinSchreierMap k₀) c).symm


/-- The translations act on the adjoint `ĀS^* ℒ_ψ ⟶ ℚ̄_ℓ` of the inclusion through `ψ`. -/
lemma affineLine.homEquiv_symm_artinSchreierImageι_comp (c : k₀) :
    (ĀS)^*ᵃ[l].map ((image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f ≫
        artinSchreierTranslationSheafHom l c) ≫
      (adicUpperStarLowerStarAdjunction l ĀS).counit.app
        (ProEtaleWeilSheaf.adicConstant k₀ l (affineLine k₀)).carrier =
    (ĀS)^*ᵃ[l].map (AdicSheaf.smul (ULift.up (ψ c)) _ ≫
        (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f) ≫
      (adicUpperStarLowerStarAdjunction l ĀS).counit.app
        (ProEtaleWeilSheaf.adicConstant k₀ l (affineLine k₀)).carrier := by
  obtain ⟨E, hE⟩ := affineLine.exists_iso_artinSchreierImage (l := l) ψ
  rw [CategoryTheory.Functor.map_comp (ĀS)^*ᵃ[l] (AdicSheaf.smul _ _),
    AdicSheaf.adicUpperStar_map_smul, Category.assoc]
  refine Mod.hom_ext _ _ ?_
  have h₀ := hE 0
  have hc := hE c
  rw [affineLine.artinSchreierTranslation_zero, CategoryTheory.Functor.map_id, Category.id_comp,
    AddChar.map_zero_eq_one] at h₀
  have h1 : (ULift.up 1 : ULift.{u + 1} (PadicAlgCl l)) = 1 := rfl
  rw [h1, one_smul, Category.comp_id] at h₀
  rw [affineLine.artinSchreierTranslation_eq] at hc
  simp only [Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarLowerStarAdjunction_counit_app_hom_eq, AdicSheaf.smul_hom,
    CategoryTheory.Functor.map_comp, Category.assoc, Linear.smul_comp, Category.id_comp]
  change _ ≫ _ ≫ affineLine.artinSchreierCounit k₀ l =
    _ • (_ ≫ affineLine.artinSchreierCounit k₀ l)
  erw [hc, h₀]
  rw [Linear.comp_smul, Category.comp_id]

/-- The translations act on the inclusion `ℒ_ψ ⟶ AS_* ℚ̄_ℓ` through `ψ`. -/
lemma ProEtaleWeilSheaf.artinSchreierImageι_comp_torsorTranslation (c : k₀) :
    ProEtaleWeilSheaf.artinSchreierImageι ψ ≫ ProEtaleWeilSheaf.torsorTranslation
        (affineLine.artinSchreierMap k₀) (affineLine.translationIso k₀)
        affineLine.translationIso_comp_artinSchreierMap c =
      ProEtaleWeilSheaf.smulEnd (ψ c) _ ≫ ProEtaleWeilSheaf.artinSchreierImageι ψ := by
  apply ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l
    (affineLine.artinSchreierMap k₀)).homEquiv _ _).symm.injective
  apply Endofunctor.IsoAlgebra.hom_ext
  rw [ProEtaleWeilSheaf.homEquiv_symm_hom_f, ProEtaleWeilSheaf.homEquiv_symm_hom_f,
    Endofunctor.IsoAlgebra.comp_hom_f, Endofunctor.IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.torsorTranslation_hom_f, ProEtaleWeilSheaf.smulEnd_hom_f,
    ProEtaleWeilSheaf.artinSchreierImageι_hom_f,
    ← artinSchreierTranslationSheafHom_eq_torsorTranslation]
  exact affineLine.homEquiv_symm_artinSchreierImageι_comp ψ c

/-- The adjoint `AS^* ℒ_ψ ⟶ ℚ̄_ℓ` of the inclusion `ℒ_ψ ⟶ AS_* ℚ̄_ℓ` is invertible
(blueprint `lemma-artin-schreier-character-sheaf`). -/
instance ProEtaleWeilSheaf.isIso_homEquiv_symm_artinSchreierImageι :
    IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l
      (affineLine.artinSchreierMap k₀)).homEquiv _ _).symm
        (ProEtaleWeilSheaf.artinSchreierImageι ψ)) := by
  have : IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l
      (affineLine.artinSchreierMap k₀)).homEquiv _ _).symm
        (ProEtaleWeilSheaf.artinSchreierImageι ψ)).hom.f := by
    rw [ProEtaleWeilSheaf.homEquiv_symm_hom_f, ProEtaleWeilSheaf.artinSchreierImageι_hom_f]
    obtain ⟨E, hE⟩ := affineLine.exists_iso_artinSchreierImage (l := l) ψ
    have h₀ := hE 0
    rw [affineLine.artinSchreierTranslation_zero, CategoryTheory.Functor.map_id,
      Category.id_comp, AddChar.map_zero_eq_one,
      show (ULift.up 1 : ULift.{u + 1} (PadicAlgCl l)) = 1 from rfl, one_smul,
      Category.comp_id] at h₀
    have : IsIso ((ĀS)^*ᵃ[l].map (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f ≫
        (adicUpperStarLowerStarAdjunction l ĀS).counit.app
          (ProEtaleWeilSheaf.adicConstant k₀ l (affineLine k₀)).carrier).hom := by
      rw [Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarLowerStarAdjunction_counit_app_hom_eq]
      erw [h₀]
      infer_instance
    have : IsIso ((Mod.forget _).map ((ĀS)^*ᵃ[l].map
        (image.ι (WeilSheaf.artinSchreierIdempotent ψ)).hom.hom.f ≫
        (adicUpperStarLowerStarAdjunction l ĀS).counit.app
          (ProEtaleWeilSheaf.adicConstant k₀ l (affineLine k₀)).carrier)) := this
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact Endofunctor.IsoAlgebra.isIso_of_isIso_hom_f' _

end AlgebraicGeometry
