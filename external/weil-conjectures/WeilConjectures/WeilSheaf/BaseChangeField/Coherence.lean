/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-!
# Exchange isomorphisms of pushforwards and their coherence

For a commutative square `p ≫ b = a ≫ p'`-type relation `p ≫ b = a ≫ p` of schemes, the
*exchange isomorphism* `p_* ⋙ b_* ≅ a_* ⋙ p_*` of pushforwards of pro-étale sheaves is
`p_* ⋙ b_* ≅ (p ≫ b)_* = (a ≫ p)_* ≅ a_* ⋙ p_*`
(`AlgebraicGeometry.ProEtale.adicLowerStarExchange` for sheaves of `ℚ̄_ℓ,X`-modules). This file
proves the compatibilities of exchange isomorphisms needed to compare Weil structures under a
finite extension of the base field:

- `AlgebraicGeometry.ProEtale.adicLowerStarExchange_comp`: exchange isomorphisms are compatible
  with composition of the horizontal morphisms `a`, `b`;
- `AlgebraicGeometry.ProEtale.adicLowerStarExchange_id`: the exchange isomorphism of identities
  is the identity;
- `AlgebraicGeometry.ProEtale.adicLowerStarExchange_cube`: two exchange isomorphisms pasted along
  a commutative cube agree.

All of them are checked on sections, after writing every composition and congruence isomorphism
as a factorisation isomorphism `AlgebraicGeometry.ProEtale.lowerStarFactor`; on sections, these
are restriction maps along canonical isomorphisms of iterated fibre products.

## Implementation notes

The components of pushforwards of morphisms and of restriction maps of pushforwards are given by
`rfl`-lemmas (`AlgebraicGeometry.ProEtale.lowerStar_map_hom_app'`,
`AlgebraicGeometry.ProEtale.lowerStar_obj_obj_map'`). Used as `simp` lemmas they leave the kernel
with expensive definitional unfoldings, so this file restates them with a proof term
(`AlgebraicGeometry.ProEtale.lowerStar_map_hom_app_eq`,
`AlgebraicGeometry.ProEtale.lowerStar_obj_obj_map_eq`). For the same reason the congruence
isomorphisms are eliminated in favour of factorisation isomorphisms before passing to sections.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Sheaf

variable (A : Type u') [Category.{u + 1} A]

/-- `AlgebraicGeometry.ProEtale.lowerStar_map_hom_app'`, with a proof term. -/
lemma lowerStar_map_hom_app_eq {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {G G' : Sheaf (Scheme.ProEt.topology Z) A} (φ : G ⟶ G') (V : Y.ProEtᵒᵖ) :
    ((g)_*[A].map φ).hom.app V =
      φ.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj V.unop)) :=
  lowerStar_map_hom_app' A g φ V

/-- `AlgebraicGeometry.ProEtale.lowerStar_obj_obj_map'`, with a proof term. -/
lemma lowerStar_obj_obj_map_eq {Z W : Scheme.{u}} (g : Z ⟶ W)
    (G : Sheaf (Scheme.ProEt.topology Z) A) {V V' : W.ProEtᵒᵖ} (φ : V ⟶ V') :
    ((g)_*[A].obj G).obj.map φ =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map φ.unop).op :=
  lowerStar_obj_obj_map' A g G φ

/-- Exchange isomorphisms, written with factorisation isomorphisms, are compatible with
composition of the horizontal morphisms. -/
lemma lowerStarFactor_exchange_comp {Z P : Scheme.{u}} (p : Z ⟶ P) (a₁ a₂ a₃ : Z ⟶ Z)
    (b₁ b₂ b₃ : P ⟶ P) (c₁ c₂ c₃ : Z ⟶ P) (ha : a₂ ≫ a₁ = a₃) (hb : b₂ ≫ b₁ = b₃)
    (h₁ : p ≫ b₁ = c₁) (h₁' : a₁ ≫ p = c₁) (h₂ : p ≫ b₂ = c₂) (h₂' : a₂ ≫ p = c₂)
    (h₃ : p ≫ b₃ = c₃) (h₃' : a₃ ≫ p = c₃) (G : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarFactor A hb).inv.app ((p)_*[A].obj G) ≫
        (b₁)_*[A].map ((lowerStarFactor A h₂).hom.app G ≫ (lowerStarFactor A h₂').inv.app G) ≫
        (lowerStarFactor A h₁).hom.app ((a₂)_*[A].obj G) ≫
        (lowerStarFactor A h₁').inv.app ((a₂)_*[A].obj G) =
      (lowerStarFactor A h₃).hom.app G ≫ (lowerStarFactor A h₃').inv.app G ≫
        (p)_*[A].map ((lowerStarFactor A ha).inv.app G) := by
  ext V : 3
  simp only [NatTrans.comp_app, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app_eq,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app, lowerStar_obj_obj_map_eq]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback,
    MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]

set_option linter.flexible false in
/-- The exchange isomorphism of identities, written with factorisation isomorphisms, is the
identity. -/
lemma lowerStarFactor_exchange_id {Z P : Scheme.{u}} (p : Z ⟶ P) (c : Z ⟶ P)
    (h : p ≫ 𝟙 P = c) (h' : 𝟙 Z ≫ p = c) (G : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarFactor A h).hom.app G ≫ (lowerStarFactor A h').inv.app G ≫
        (p)_*[A].map ((lowerStarId A Z).hom.app G) =
      (lowerStarId A P).hom.app ((p)_*[A].obj G) := by
  ext V : 3
  simp only [NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app_eq,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app, lowerStar_obj_obj_map_eq,
    lowerStarId_hom_app_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals try simp [MorphismProperty.Over.pullback, MorphismProperty.Over.pullbackId,
    MorphismProperty.Over.mk, MorphismProperty.Over.pullbackComp]
  all_goals exact pullback.condition.symm

/-- Two exchange isomorphisms, written with factorisation isomorphisms, pasted along a
commutative cube agree. The vertical morphisms are `θ : Z ⟶ Z'`, `ψ : P ⟶ P'`, the
horizontal ones `ā : Z ⟶ P`, `ā' : Z' ⟶ P'`, and the endomorphisms `F`, `F'`, `G`, `G'` of
`Z`, `Z'`, `P`, `P'`. -/
lemma lowerStarFactor_exchange_cube {Z Z' P P' : Scheme.{u}} (θ : Z ⟶ Z') (ψ : P ⟶ P')
    (a : Z ⟶ P) (a' : Z' ⟶ P') (F : Z ⟶ Z) (F' : Z' ⟶ Z') (G : P ⟶ P) (G' : P' ⟶ P')
    (d : Z ⟶ P') (e : θ ≫ a' = d) (e' : a ≫ ψ = d)
    (cθ : Z ⟶ Z') (hθ : θ ≫ F' = cθ) (hθ' : F ≫ θ = cθ)
    (cψ : P ⟶ P') (hψ : ψ ≫ G' = cψ) (hψ' : G ≫ ψ = cψ)
    (ca : Z ⟶ P) (hA : a ≫ G = ca) (hA' : F ≫ a = ca)
    (cb : Z' ⟶ P') (hB : a' ≫ G' = cb) (hB' : F' ≫ a' = cb)
    (K : Sheaf (Scheme.ProEt.topology Z) A) :
    (G')_*[A].map ((lowerStarFactor A e).hom.app K ≫ (lowerStarFactor A e').inv.app K) ≫
        (lowerStarFactor A hψ).hom.app ((a)_*[A].obj K) ≫
        (lowerStarFactor A hψ').inv.app ((a)_*[A].obj K) ≫
        (ψ)_*[A].map ((lowerStarFactor A hA).hom.app K ≫ (lowerStarFactor A hA').inv.app K) =
      (lowerStarFactor A hB).hom.app ((θ)_*[A].obj K) ≫
        (lowerStarFactor A hB').inv.app ((θ)_*[A].obj K) ≫
        (a')_*[A].map ((lowerStarFactor A hθ).hom.app K ≫ (lowerStarFactor A hθ').inv.app K) ≫
        (lowerStarFactor A e).hom.app ((F)_*[A].obj K) ≫
        (lowerStarFactor A e').inv.app ((F)_*[A].obj K) := by
  ext V : 3
  simp only [NatTrans.comp_app, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app_eq,
    lowerStarFactor_hom_app_hom_app, lowerStarFactor_inv_app_hom_app, lowerStar_obj_obj_map_eq]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackComp, e, e']

/-- A congruence followed by the inverse of a composition isomorphism is the inverse of a
factorisation isomorphism. -/
lemma lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_eq {X Y Z : Scheme.{u}} {x : Z ⟶ X}
    {b : Z ⟶ Y} {c : Y ⟶ X} (h : x = b ≫ c) (G : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarCongr A h).hom.app G ≫ (lowerStarComp A b c).inv.app G =
      (lowerStarFactor A h.symm).inv.app G := by
  subst h
  rw [lowerStarFactor_rfl, lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

end Sheaf

section Adic

variable {l : ℕ} [Fact l.Prime]

variable (l) in
/-- The isomorphism `p_* ⋙ q_* ≅ (p ≫ q)_* = (p' ≫ q')_* ≅ p'_* ⋙ q'_*` of pushforwards of
sheaves of `ℚ̄_ℓ,X`-modules along a commutative square `p ≫ q = p' ≫ q'`. For `q = b`,
`p' = a` and `q' = p` it is the exchange isomorphism of `p_*` with the pushforwards along
endomorphisms `a`, `b` with `p ≫ b = a ≫ p`. -/
noncomputable def adicLowerStarSquareIso {Z Y Y' X : Scheme.{u}} {p : Z ⟶ Y} {q : Y ⟶ X}
    {p' : Z ⟶ Y'} {q' : Y' ⟶ X} (h : p ≫ q = p' ≫ q') :
    (p)_*ᵃ[l] ⋙ (q)_*ᵃ[l] ≅ (p')_*ᵃ[l] ⋙ (q')_*ᵃ[l] :=
  adicLowerStarComp l p q ≪≫ adicLowerStarCongr l h ≪≫ (adicLowerStarComp l p' q').symm

lemma adicLowerStarSquareIso_hom_app_hom {Z Y Y' X : Scheme.{u}} {p : Z ⟶ Y} {q : Y ⟶ X}
    {p' : Z ⟶ Y'} {q' : Y' ⟶ X} (h : p ≫ q = p' ≫ q') (M : AdicSheaf l Z) :
    ((adicLowerStarSquareIso l h).hom.app M).hom =
      (lowerStarFactor _ h).hom.app M.X ≫
        (lowerStarFactor _ (rfl : p' ≫ q' = p' ≫ q')).inv.app M.X := by
  simp only [adicLowerStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Mod.comp_hom', adicLowerStarComp_hom_app_hom, adicLowerStarCongr_hom_app_hom,
    adicLowerStarComp_inv_app_hom, lowerStarFactor_rfl, ← lowerStarComp_trans_lowerStarCongr,
    Category.assoc]

lemma adicLowerStarCongr_hom_app_comp_adicLowerStarComp_inv_app_hom {X Y Z : Scheme.{u}}
    {x : Z ⟶ X} {b : Z ⟶ Y} {c : Y ⟶ X} (h : x = b ≫ c) (M : AdicSheaf l Z) :
    ((adicLowerStarCongr l h).hom.app M ≫ (adicLowerStarComp l b c).inv.app M).hom =
      (lowerStarFactor _ h.symm).inv.app M.X := by
  rw [Mod.comp_hom', adicLowerStarCongr_hom_app_hom, adicLowerStarComp_inv_app_hom,
    lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_eq]

/-- Exchange isomorphisms are compatible with composition of the horizontal morphisms. -/
lemma adicLowerStarSquareIso_comp {Z P : Scheme.{u}} (p : Z ⟶ P) (a₁ a₂ a₃ : Z ⟶ Z)
    (b₁ b₂ b₃ : P ⟶ P) (ha : a₃ = a₂ ≫ a₁) (hb : b₃ = b₂ ≫ b₁)
    (h₁ : p ≫ b₁ = a₁ ≫ p) (h₂ : p ≫ b₂ = a₂ ≫ p) (h₃ : p ≫ b₃ = a₃ ≫ p)
    (M : AdicSheaf l Z) :
    (adicLowerStarCongr l hb).hom.app ((p)_*ᵃ[l].obj M) ≫
        (adicLowerStarComp l b₂ b₁).inv.app ((p)_*ᵃ[l].obj M) ≫
        (b₁)_*ᵃ[l].map ((adicLowerStarSquareIso l h₂).hom.app M) ≫
        (adicLowerStarSquareIso l h₁).hom.app ((a₂)_*ᵃ[l].obj M) =
      (adicLowerStarSquareIso l h₃).hom.app M ≫
        (p)_*ᵃ[l].map ((adicLowerStarCongr l ha).hom.app M ≫
          (adicLowerStarComp l a₂ a₁).inv.app M) := by
  apply Mod.hom_ext
  have := lowerStarFactor_exchange_comp (WeilCoefficients.{u} l) p a₁ a₂ a₃ b₁ b₂ b₃ _ _ _
    ha.symm hb.symm h₁ rfl h₂ rfl h₃ rfl M.X
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarCongr_hom_app_hom,
    adicLowerStarComp_inv_app_hom, adicLowerStarSquareIso_hom_app_hom,
    Category.assoc, reassoc_of% lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_eq,
    lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_eq]
  simp only [Functor.map_comp, Category.assoc] at this ⊢
  exact this

/-- The exchange isomorphism of identities is the identity. -/
lemma adicLowerStarSquareIso_id {Z P : Scheme.{u}} (p : Z ⟶ P) (a : Z ⟶ Z) (b : P ⟶ P)
    (ha : a = 𝟙 Z) (hb : b = 𝟙 P) (h : p ≫ b = a ≫ p) (M : AdicSheaf l Z) :
    (adicLowerStarSquareIso l h).hom.app M ≫
        (p)_*ᵃ[l].map ((adicLowerStarCongr l ha).hom.app M ≫ (adicLowerStarId l Z).hom.app M) =
      (adicLowerStarCongr l hb).hom.app ((p)_*ᵃ[l].obj M) ≫
        (adicLowerStarId l P).hom.app ((p)_*ᵃ[l].obj M) := by
  subst ha hb
  apply Mod.hom_ext
  have := lowerStarFactor_exchange_id (WeilCoefficients.{u} l) p _ h rfl M.X
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarSquareIso_hom_app_hom,
    adicLowerStarCongr_hom_app_hom, adicLowerStarId_hom_app_hom, lowerStarCongr_rfl,
    Iso.refl_hom, NatTrans.id_app, Category.assoc] at this ⊢
  exact this

/-- Two exchange isomorphisms pasted along a commutative cube agree: for vertical morphisms
`θ : Z ⟶ Z'`, `ψ : P ⟶ P'`, horizontal ones `a : Z ⟶ P`, `a' : Z' ⟶ P'` with
`θ ≫ a' = a ≫ ψ`, and endomorphisms `F`, `F'`, `G`, `G'` of `Z`, `Z'`, `P`, `P'` commuting
with them. -/
lemma adicLowerStarSquareIso_cube {Z Z' P P' : Scheme.{u}} (θ : Z ⟶ Z') (ψ : P ⟶ P')
    (a : Z ⟶ P) (a' : Z' ⟶ P') (F : Z ⟶ Z) (F' : Z' ⟶ Z') (G : P ⟶ P) (G' : P' ⟶ P')
    (e : θ ≫ a' = a ≫ ψ) (hθ : θ ≫ F' = F ≫ θ) (hψ : ψ ≫ G' = G ≫ ψ) (hA : a ≫ G = F ≫ a)
    (hB : a' ≫ G' = F' ≫ a') (M : AdicSheaf l Z) :
    (G')_*ᵃ[l].map ((adicLowerStarSquareIso l e).hom.app M) ≫
        (adicLowerStarSquareIso l hψ).hom.app ((a)_*ᵃ[l].obj M) ≫
        (ψ)_*ᵃ[l].map ((adicLowerStarSquareIso l hA).hom.app M) =
      (adicLowerStarSquareIso l hB).hom.app ((θ)_*ᵃ[l].obj M) ≫
        (a')_*ᵃ[l].map ((adicLowerStarSquareIso l hθ).hom.app M) ≫
        (adicLowerStarSquareIso l e).hom.app ((F)_*ᵃ[l].obj M) := by
  apply Mod.hom_ext
  have := lowerStarFactor_exchange_cube (WeilCoefficients.{u} l) θ ψ a a' F F' G G' _ e rfl
    _ hθ rfl _ hψ rfl _ hA rfl _ hB rfl M.X
  simp only [Mod.comp_hom', adicLowerStar_map_hom, adicLowerStarSquareIso_hom_app_hom,
    Category.assoc] at this ⊢
  simp only [Functor.map_comp, Category.assoc] at this ⊢
  exact this

end Adic

end AlgebraicGeometry.ProEtale
