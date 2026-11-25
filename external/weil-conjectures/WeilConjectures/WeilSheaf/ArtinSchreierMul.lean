/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierFunctions
public import WeilConjectures.WeilSheaf.ArtinSchreierIsotypic
public import WeilConjectures.WeilSheaf.ArtinSchreierPlane
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# Multiplicativity of the Artin–Schreier sheaves

For two global functions `f₁, f₂` on a `k₀`-scheme `X`, all the Artin–Schreier sheaves
`ℒ_{ψ, c₁ f₁ + c₂ f₂}` (`c ∈ k₀²`) are isotypic components of the pushforward `π_* ℚ̄_ℓ` along the
Artin–Schreier covering `π : X' ⟶ X` of `(f₁, f₂)`, a `k₀²`-torsor
(`AlgebraicGeometry.artinSchreierPlaneCover`): the group `k₀²` acts on `ℒ_{ψ, c₁ f₁ + c₂ f₂}`
through the character `a ↦ ψ(c₁ a₁ + c₂ a₂)`. The criterion
`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_iso_ihom_of_isotypic` then identifies internal
homs between them (`AlgebraicGeometry.nonempty_iso_ihom_artinSchreierPlane`). This gives
(blueprint `lemma-artin-schreier-character-sheaf`):

* `ℒ_{ψ,a} ⊗ ℒ_{ψ,b} ≅ ℒ_{ψ,a+b}` (`AlgebraicGeometry.nonempty_iso_tensorObj_artinSchreierOf`),
  where `ℒ_{ψ,a} ⊗ ℒ_{ψ,b} = 𝓗om(ℒ_{ψ,a}^∨, ℒ_{ψ,b})`, from `ℒ_{ψ,-a} ≅ ℒ_{ψ,a}^∨` and
  `ℒ_{ψ,a+b} ≅ 𝓗om(ℒ_{ψ,-a}, ℒ_{ψ,b})`;
* `ℒ_{ψ(a x)}^∨ ≅ ℒ_{ψ⁻¹(a x)}` on the affine line, in `WeilSheaf/ArtinSchreierDual.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Plane

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (f : planeIndex → Γ(X, ⊤))

variable (k₀) in
/-- The coordinate `∑ᵢ cᵢ tᵢ : X' ⟶ 𝔸¹` of the Artin–Schreier covering `X'` of `(f₁, f₂)`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
noncomputable abbrev artinSchreierPlaneCover.linearCoord (c : planeIndex → k₀) :
    artinSchreierPlaneCover k₀ f ⟶ affineLine k₀ :=
  artinSchreierPlaneCover.coord f ≫ affineLine.linearForm k₀ c

variable (k₀) in
/-- The function `∑ᵢ cᵢ fᵢ : X ⟶ 𝔸¹` (blueprint `lemma-artin-schreier-character-sheaf`). -/
noncomputable abbrev planeLinearFunction (c : planeIndex → k₀) : X ⟶ affineLine k₀ :=
  planeSection k₀ f ≫ affineLine.linearForm k₀ c

omit [Fact (ringChar k₀ ≠ l)] in
/-- The coordinate `∑ᵢ cᵢ tᵢ` of the covering lifts `∑ᵢ cᵢ fᵢ` through the Artin–Schreier map
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma artinSchreierPlaneCover.linearCoord_comp_artinSchreierMap (c : planeIndex → k₀) :
    artinSchreierPlaneCover.linearCoord k₀ f c ≫ affineLine.artinSchreierMap k₀ =
      artinSchreierPlaneCover.π f ≫ planeLinearFunction k₀ f c := by
  rw [Category.assoc, affineLine.linearForm_comp_artinSchreierMap,
    artinSchreierPlaneCover.condition_assoc]

omit [Fact (ringChar k₀ ≠ l)] in
/-- Translating the covering by `a ∈ k₀²` translates the coordinate `∑ᵢ cᵢ tᵢ` by `∑ᵢ cᵢ aᵢ`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma artinSchreierPlaneCover.translation_comp_linearCoord (c a : planeIndex → k₀) :
    (artinSchreierPlaneCover.translation f a).hom ≫ artinSchreierPlaneCover.linearCoord k₀ f c =
      artinSchreierPlaneCover.linearCoord k₀ f c ≫
        (affineLine.translationIso k₀ (∑ i, c i * a i)).hom := by
  rw [artinSchreierPlaneCover.translation_comp_coord_assoc, Category.assoc,
    planeTranslation_comp_linearForm, ← Category.assoc]
  rfl

omit [Finite k₀] in
/-- The linear form `a ↦ ∑ᵢ cᵢ aᵢ` on `k₀²` (blueprint `lemma-artin-schreier-character-sheaf`). -/
def planeLinearMap (c : planeIndex → k₀) : (planeIndex → k₀) →+ k₀ where
  toFun a := ∑ i, c i * a i
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The character `a ↦ ψ(∑ᵢ cᵢ aᵢ)` of `k₀²` (blueprint `lemma-artin-schreier-character-sheaf`). -/
noncomputable def planeCharacter (ψ : AddChar k₀ (PadicAlgCl l)) (c : planeIndex → k₀) :
    AddChar (planeIndex → k₀) (PadicAlgCl l) :=
  ψ.compAddMonoidHom (planeLinearMap c)

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- Evaluation of `AlgebraicGeometry.planeCharacter` (blueprint
`lemma-artin-schreier-character-sheaf`). -/
lemma planeCharacter_apply (ψ : AddChar k₀ (PadicAlgCl l)) (c a : planeIndex → k₀) :
    planeCharacter ψ c a = ψ (∑ i, c i * a i) :=
  rfl

/-- The inclusion `(∑ᵢ cᵢ fᵢ)^* ℒ_ψ ⟶ π_* ℚ̄_ℓ`, pulled back from `ℒ_ψ ⟶ AS_* ℚ̄_ℓ`. -/
local notation "Φ[" ψ ", " c "]" => ProEtaleWeilSheaf.isotypicPullback
  (artinSchreierPlaneCover.linearCoord_comp_artinSchreierMap f c)
  (ProEtaleWeilSheaf.artinSchreierImageι ψ)

omit [Fact (ringChar k₀ ≠ l)] in
/-- If the adjoint `π^* M ⟶ ℚ̄_ℓ` of `φ : M ⟶ π_* ℚ̄_ℓ` is invertible, so is its underlying
morphism on the geometric fibre (blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint {Z W : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))] (π : W ⟶ Z)
    [π.IsOver (Spec (CommRingCat.of k₀))] {M : ProEtaleWeilSheaf k₀ l Z}
    (φ : M ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (hφ : IsIso (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l π).homEquiv _ _).symm φ)) :
    IsIso ((Scheme.Hom.geometricFiberMap π (comp_over _ _))^*ᵃ[l].map φ.hom.f ≫
      (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap π
        (comp_over _ _))).counit.app _) := by
  have h := (Endofunctor.IsoAlgebra.forget _).map_isIso
    (((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l π).homEquiv _ _).symm φ)
  rw [Endofunctor.IsoAlgebra.forget_map, ProEtaleWeilSheaf.homEquiv_symm_hom_f] at h
  exact h

/-- The translation by `a ∈ k₀²` acts on `(∑ᵢ cᵢ fᵢ)^* ℒ_ψ ⟶ π_* ℚ̄_ℓ` through `ψ(∑ᵢ cᵢ aᵢ)`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma artinSchreierPlaneCover.isotypicPullback_comp_torsorTranslation
    (ψ : AddChar k₀ (PadicAlgCl l)) (c a : planeIndex → k₀) :
    Φ[ψ, c] ≫ ProEtaleWeilSheaf.torsorTranslation
        (artinSchreierPlaneCover.π f) (artinSchreierPlaneCover.translation f)
        (artinSchreierPlaneCover.translation_comp_π f) a =
      ProEtaleWeilSheaf.smulEnd (planeCharacter ψ c a) _ ≫ Φ[ψ, c] :=
  ProEtaleWeilSheaf.isotypicPullback_comp_torsorTranslation
    (artinSchreierPlaneCover.translation f) (artinSchreierPlaneCover.translation_comp_π f)
    (affineLine.translationIso k₀) affineLine.translationIso_comp_artinSchreierMap _ _ ψ
    (ProEtaleWeilSheaf.artinSchreierImageι_comp_torsorTranslation ψ) (planeLinearMap c)
    (fun a ↦ artinSchreierPlaneCover.translation_comp_linearCoord f c a) a

omit [Fact (ringChar k₀ ≠ l)] in
/-- The order of `k₀²` is invertible in `ℚ̄_ℓ` (blueprint
`lemma-artin-schreier-character-sheaf`). -/
lemma natCard_planeIndex_ne_zero :
    (Nat.card (planeIndex → k₀) : PadicAlgCl l) ≠ 0 :=
  Nat.cast_ne_zero.2 Nat.card_pos.ne'

/-- **Internal homs of Artin–Schreier sheaves of linear combinations.** If the characters
`χᵢ(a) = ψᵢ(∑ⱼ cᵢⱼ aⱼ)` of `k₀²` satisfy `χ₁ χ₂ = χ₃`, then
`(∑ⱼ c₁ⱼ fⱼ)^* ℒ_{ψ₁} ≅ 𝓗om((∑ⱼ c₂ⱼ fⱼ)^* ℒ_{ψ₂}, (∑ⱼ c₃ⱼ fⱼ)^* ℒ_{ψ₃})` as pro-étale Weil
sheaves (blueprint `lemma-artin-schreier-character-sheaf`). -/
theorem nonempty_iso_ihom_artinSchreierPlane (ψ₁ ψ₂ ψ₃ : AddChar k₀ (PadicAlgCl l))
    (c₁ c₂ c₃ : planeIndex → k₀) (h : ∀ g : planeIndex → k₀,
      ψ₁ (∑ i, c₁ i * g i) * ψ₂ (∑ i, c₂ i * g i) = ψ₃ (∑ i, c₃ i * g i)) :
    Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l (planeLinearFunction k₀ f c₁)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ₁)).obj ≅
      ProEtaleWeilSheaf.ihom k₀ l X
        ((ProEtaleWeilSheaf.upperStar k₀ l (planeLinearFunction k₀ f c₂)).obj
          (image (WeilSheaf.artinSchreierIdempotent ψ₂)).obj)
        ((ProEtaleWeilSheaf.upperStar k₀ l (planeLinearFunction k₀ f c₃)).obj
          (image (WeilSheaf.artinSchreierIdempotent ψ₃)).obj)) := by
  refine ProEtaleWeilSheaf.nonempty_iso_ihom_of_isotypic
    (π := artinSchreierPlaneCover.π (k₀ := k₀) f)
    (τ := artinSchreierPlaneCover.translation (k₀ := k₀) f)
    (hτ := artinSchreierPlaneCover.translation_comp_π (k₀ := k₀) f)
    (artinSchreierPlaneCover.translation_add (k₀ := k₀) f)
    (isTorsorSplit_artinSchreierPlaneCover k₀ f)
    (planeCharacter ψ₁ c₁) (planeCharacter ψ₂ c₂) natCard_planeIndex_ne_zero
    Φ[ψ₁, c₁] Φ[ψ₂, c₂] Φ[ψ₃, c₃]
    (artinSchreierPlaneCover.isotypicPullback_comp_torsorTranslation f ψ₁ c₁)
    (artinSchreierPlaneCover.isotypicPullback_comp_torsorTranslation f ψ₂ c₂) (fun g ↦ ?_)
    (ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint _ _
      (ProEtaleWeilSheaf.isIso_homEquiv_symm_isotypicPullback _ _))
    (ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint _ _
      (ProEtaleWeilSheaf.isIso_homEquiv_symm_isotypicPullback _ _))
    (ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint _ _
      (ProEtaleWeilSheaf.isIso_homEquiv_symm_isotypicPullback _ _))
  have e : (planeCharacter ψ₁ c₁ * planeCharacter ψ₂ c₂) g = planeCharacter ψ₃ c₃ g := by
    rw [AddChar.mul_apply]
    exact h g
  rw [e]
  exact artinSchreierPlaneCover.isotypicPullback_comp_torsorTranslation f ψ₃ c₃ g

/-- **Duals of Artin–Schreier sheaves of linear combinations.** If the characters
`χᵢ(a) = ψᵢ(∑ⱼ cᵢⱼ aⱼ)` of `k₀²` satisfy `χ₁ χ₂ = 1`, then
`(∑ⱼ c₁ⱼ fⱼ)^* ℒ_{ψ₁} ≅ 𝓗om((∑ⱼ c₂ⱼ fⱼ)^* ℒ_{ψ₂}, ℚ̄_ℓ)` as pro-étale Weil sheaves
(blueprint `lemma-artin-schreier-character-sheaf`). -/
theorem nonempty_iso_ihom_adicConstant_artinSchreierPlane (ψ₁ ψ₂ : AddChar k₀ (PadicAlgCl l))
    (c₁ c₂ : planeIndex → k₀)
    (h : ∀ g : planeIndex → k₀, ψ₁ (∑ i, c₁ i * g i) * ψ₂ (∑ i, c₂ i * g i) = 1) :
    Nonempty ((ProEtaleWeilSheaf.upperStar k₀ l (planeLinearFunction k₀ f c₁)).obj
        (image (WeilSheaf.artinSchreierIdempotent ψ₁)).obj ≅
      ProEtaleWeilSheaf.ihom k₀ l X
        ((ProEtaleWeilSheaf.upperStar k₀ l (planeLinearFunction k₀ f c₂)).obj
          (image (WeilSheaf.artinSchreierIdempotent ψ₂)).obj)
        (ProEtaleWeilSheaf.adicConstant k₀ l X)) := by
  refine ProEtaleWeilSheaf.nonempty_iso_ihom_of_isotypic
    (π := artinSchreierPlaneCover.π (k₀ := k₀) f)
    (τ := artinSchreierPlaneCover.translation (k₀ := k₀) f)
    (hτ := artinSchreierPlaneCover.translation_comp_π (k₀ := k₀) f)
    (artinSchreierPlaneCover.translation_add (k₀ := k₀) f)
    (isTorsorSplit_artinSchreierPlaneCover k₀ f)
    (planeCharacter ψ₁ c₁) (planeCharacter ψ₂ c₂) natCard_planeIndex_ne_zero
    Φ[ψ₁, c₁] Φ[ψ₂, c₂] (ProEtaleWeilSheaf.unitToLowerStar k₀ l _)
    (artinSchreierPlaneCover.isotypicPullback_comp_torsorTranslation f ψ₁ c₁)
    (artinSchreierPlaneCover.isotypicPullback_comp_torsorTranslation f ψ₂ c₂) (fun g ↦ ?_)
    (ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint _ _
      (ProEtaleWeilSheaf.isIso_homEquiv_symm_isotypicPullback _ _))
    (ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint _ _
      (ProEtaleWeilSheaf.isIso_homEquiv_symm_isotypicPullback _ _))
    (ProEtaleWeilSheaf.isIso_geometricFiberMap_adjoint _ _ inferInstance)
  have e : (planeCharacter ψ₁ c₁ * planeCharacter ψ₂ c₂) g = 1 := by
    rw [AddChar.mul_apply]
    exact h g
  rw [e, ProEtaleWeilSheaf.smulEnd_one, Category.id_comp]
  exact ProEtaleWeilSheaf.unitToLowerStar_comp_torsorTranslation (g := g) ..

end Plane

section Assembly

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- A sum over the two coordinates of the plane (blueprint
`lemma-artin-schreier-character-sheaf`). -/
lemma sum_planeIndex {M : Type*} [AddCommMonoid M] (F : planeIndex → M) :
    ∑ i, F i = F ⟨0⟩ + F ⟨1⟩ := by
  rw [← (Equiv.ulift (α := Fin 2)).symm.sum_comp, Fin.sum_univ_two]
  rfl

/-- The underlying pro-étale Weil sheaf of a pullback, along a morphism equal to the given one
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma WeilSheaf.nonempty_iso_upperStar_obj_obj {Y Y' : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ Y') [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y')
    {g : Y ⟶ Y'} [g.IsOver (Spec (CommRingCat.of k₀))] (hg : φ = g) :
    Nonempty (((WeilSheaf.upperStar φ).obj F).obj ≅
      (ProEtaleWeilSheaf.upperStar k₀ l g).obj F.obj) := by
  rw [WeilSheaf.upperStar_obj_obj]
  exact ⟨(ProEtaleWeilSheaf.upperStarCongrIso k₀ l hg).app F.obj⟩

/-- The underlying pro-étale Weil sheaf of an iterated pullback is the pullback along the
composite (blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj_obj {Y Y' Y'' : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    [Y''.Over (Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ Y') [φ.IsOver (Spec (CommRingCat.of k₀))] (φ' : Y' ⟶ Y'')
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y'')
    {g : Y ⟶ Y''} [g.IsOver (Spec (CommRingCat.of k₀))] (hg : φ ≫ φ' = g) :
    Nonempty (((WeilSheaf.upperStar φ).obj ((WeilSheaf.upperStar φ').obj F)).obj ≅
      (ProEtaleWeilSheaf.upperStar k₀ l g).obj F.obj) := by
  rw [WeilSheaf.upperStar_obj_obj, WeilSheaf.upperStar_obj_obj]
  exact ⟨((ProEtaleWeilSheaf.upperStarCompIso k₀ l φ φ').app F.obj).symm ≪≫
    (ProEtaleWeilSheaf.upperStarCongrIso k₀ l hg).app F.obj⟩

attribute [local instance high] WeilSheaf.hasImage_artinSchreierIdempotent

/-- Unfolding `AlgebraicGeometry.artinSchreier`, with the named instance
`AlgebraicGeometry.WeilSheaf.hasImage_artinSchreierIdempotent` for the image
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma artinSchreier_eq_upperStar_image (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    artinSchreier ψ a = (WeilSheaf.upperStar (affineLine.smul k₀ a)).obj
      (image (WeilSheaf.artinSchreierIdempotent ψ)) :=
  congrArg (WeilSheaf.upperStar (affineLine.smul k₀ a)).obj
    (WeilSheaf.image_artinSchreierIdempotent_eq ψ)

/-- The underlying pro-étale Weil sheaf of `ℒ_{ψ(a x)}` is the pullback of `ℒ_ψ` along any
morphism equal to `x ↦ a x` (blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma nonempty_iso_artinSchreier_obj (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀)
    {g : affineLine k₀ ⟶ affineLine k₀} [g.IsOver (Spec (CommRingCat.of k₀))]
    (hg : affineLine.smul k₀ a = g) :
    Nonempty ((artinSchreier ψ a).obj ≅ (ProEtaleWeilSheaf.upperStar k₀ l g).obj
      (image (WeilSheaf.artinSchreierIdempotent ψ)).obj) := by
  rw [artinSchreier_eq_upperStar_image]
  exact WeilSheaf.nonempty_iso_upperStar_obj_obj _ _ hg

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The underlying pro-étale Weil sheaf of `ℒ_{ψ,x}` is the pullback of `ℒ_ψ` along any
morphism equal to the function `x` (blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma nonempty_iso_artinSchreierOf_obj (ψ : AddChar k₀ (PadicAlgCl l)) (x : Γ(X, ⊤))
    {g : X ⟶ affineLine k₀} [g.IsOver (Spec (CommRingCat.of k₀))]
    (hg : affineLine.homOfSection k₀ x ≫ affineLine.smul k₀ 1 = g) :
    Nonempty ((artinSchreierOf ψ x).obj ≅ (ProEtaleWeilSheaf.upperStar k₀ l g).obj
      (image (WeilSheaf.artinSchreierIdempotent ψ)).obj) := by
  rw [artinSchreierOf_eq, artinSchreier_eq_upperStar_image]
  exact WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj_obj _ _ _ hg

/-- The underlying pro-étale Weil sheaf of a tensor product `F ⊗ G = 𝓗om(F^∨, G)`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma WeilSheaf.tensorObj_obj (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    (F.tensorObj G hF).obj = ProEtaleWeilSheaf.ihom k₀ l X (F.dual hF).obj G.obj :=
  rfl

/-- The underlying pro-étale Weil sheaf of a dual `F^∨ = 𝓗om(F, ℚ̄_ℓ)`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma WeilSheaf.dual_obj_eq_ihom (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    (F.dual hF).obj =
      ProEtaleWeilSheaf.ihom k₀ l X F.obj (ProEtaleWeilSheaf.adicConstant k₀ l X) :=
  rfl

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- For `f = (a, b)` and `c = (x, y)`, the function `∑ᵢ cᵢ fᵢ` is `x a + y b`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma planeLinearFunction_pair (a b : Γ(X, ⊤)) (x y : k₀) :
    planeLinearFunction k₀ (fun i : planeIndex ↦ ![a, b] i.down) (fun i ↦ ![x, y] i.down) =
      affineLine.homOfSection k₀
        ((X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom x) * a +
          (X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom y) * b) := by
  rw [planeLinearFunction, planeSection_comp_linearForm, sum_planeIndex]
  rfl

/-- **Multiplicativity of the Artin–Schreier sheaves**: `ℒ_{ψ,a} ⊗ ℒ_{ψ,b} ≅ ℒ_{ψ,a+b}` for
global functions `a, b` on `X`. On the Artin–Schreier covering of `(a, b)`, a `k₀²`-torsor, the
three sheaves and `ℒ_{ψ,-a}` are isotypic components of `π_* ℚ̄_ℓ`, which gives
`ℒ_{ψ,-a} ≅ 𝓗om(ℒ_{ψ,a}, ℚ̄_ℓ) = ℒ_{ψ,a}^∨` and `ℒ_{ψ,a+b} ≅ 𝓗om(ℒ_{ψ,-a}, ℒ_{ψ,b})`.
(blueprint: `lemma-artin-schreier-character-sheaf`) -/
theorem nonempty_iso_tensorObj_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l))
    (a b : Γ(X, ⊤)) :
    Nonempty ((artinSchreierOf ψ a).tensorObj (artinSchreierOf ψ b)
      (isLisse_artinSchreierOf ψ a) ≅ artinSchreierOf ψ (a + b)) := by
  set f : planeIndex → Γ(X, ⊤) := fun i ↦ ![a, b] i.down with hf
  have hv (x y : k₀) (z : Γ(X, ⊤))
      (hz : z = (X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom x) * a +
        (X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom y) * b) :
      affineLine.homOfSection k₀ z ≫ affineLine.smul k₀ 1 =
        planeLinearFunction k₀ f (fun i ↦ ![x, y] i.down) := by
    rw [hf, planeLinearFunction_pair, affineLine.homOfSection_comp_smul, hz]
    simp
  obtain ⟨ea⟩ := nonempty_iso_artinSchreierOf_obj ψ a (hv 1 0 a (by simp))
  obtain ⟨eb⟩ := nonempty_iso_artinSchreierOf_obj ψ b (hv 0 1 b (by simp))
  obtain ⟨eab⟩ := nonempty_iso_artinSchreierOf_obj ψ (a + b) (hv 1 1 (a + b) (by simp))
  have hA (g : planeIndex → k₀) : ψ (∑ i, ![-1, 0] i.down * g i) *
      ψ (∑ i, ![1, 0] i.down * g i) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_zero_eq_one ψ, sum_planeIndex, sum_planeIndex]
    congr 1
    simp
  have hB (g : planeIndex → k₀) : ψ (∑ i, ![1, 1] i.down * g i) *
      ψ (∑ i, ![-1, 0] i.down * g i) = ψ (∑ i, ![0, 1] i.down * g i) := by
    rw [← AddChar.map_add_eq_mul, sum_planeIndex, sum_planeIndex, sum_planeIndex]
    congr 1
    simp
  obtain ⟨eA⟩ := nonempty_iso_ihom_adicConstant_artinSchreierPlane f ψ ψ
    (fun i ↦ ![-1, 0] i.down) (fun i ↦ ![1, 0] i.down) hA
  obtain ⟨eB⟩ := nonempty_iso_ihom_artinSchreierPlane f ψ ψ ψ
    (fun i ↦ ![1, 1] i.down) (fun i ↦ ![-1, 0] i.down) (fun i ↦ ![0, 1] i.down) hB
  refine ⟨ObjectProperty.isoMk _ ?_⟩
  rw [WeilSheaf.tensorObj_obj, WeilSheaf.dual_obj_eq_ihom]
  exact ProEtaleWeilSheaf.ihomMapIsoLeft
      (ProEtaleWeilSheaf.ihomMapIsoLeft ea (ProEtaleWeilSheaf.adicConstant k₀ l X)) _ ≪≫
    ProEtaleWeilSheaf.ihomMapIsoLeft eA _ ≪≫ ProEtaleWeilSheaf.ihomMapIsoRight _ eb ≪≫
    eB.symm ≪≫ eab.symm

end Assembly

end AlgebraicGeometry
