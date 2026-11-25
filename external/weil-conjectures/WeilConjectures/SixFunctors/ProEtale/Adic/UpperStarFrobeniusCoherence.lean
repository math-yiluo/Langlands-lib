/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition

/-!
# Coherences of ℓ-adic pullbacks along squares

Coherences of the composition isomorphisms of ℓ-adic pullbacks for endomorphisms `g` with `g ≫
p = p` and squares `τ ≫ s = s ≫ g`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

open AdicSheaf in
/-- Changing the endomorphism `g` with `g ≫ p = p` along an equality in the identification
`g^* p^* ≅ (g ≫ p)^* = p^*`. -/
lemma adicUpperStarCongr_hom_app_comp_adicUpperStarComp_inv_app_comp_congr {Y Z : Scheme.{u}}
    {g g₁ : Y ⟶ Y} (p : Y ⟶ Z) (e : g₁ = g) (h : g ≫ p = p) (h₁ : g₁ ≫ p = p)
    (M : AdicSheaf l Z) :
    (adicUpperStarCongr l e).hom.app ((p)^*ᵃ[l].obj M) ≫ (adicUpperStarComp l g p).inv.app M ≫
        (adicUpperStarCongr l h).hom.app M =
      (adicUpperStarComp l g₁ p).inv.app M ≫ (adicUpperStarCongr l h₁).hom.app M := by
  have c := adicUpperStarComp_hom_app_comp_congr (l := l) p e (by rw [e]) M
  rw [← cancel_epi ((adicUpperStarComp l g₁ p).hom.app M), Iso.hom_inv_id_app_assoc,
    reassoc_of% c, Iso.hom_inv_id_app_assoc, adicUpperStarCongr_hom_app_trans]

open AdicSheaf in
/-- The identifications `g^* p^* ≅ (g ≫ p)^* = p^*` for `g ≫ p = p` compose. -/
lemma adicUpperStarCongr_hom_app_comp_adicUpperStarComp_hom_app_comp_map {Y Z : Scheme.{u}}
    {g g' g'' : Y ⟶ Y} (p : Y ⟶ Z) (e : g ≫ g' = g'') (h : g ≫ p = p) (h' : g' ≫ p = p)
    (h'' : g'' ≫ p = p) (M : AdicSheaf l Z) :
    (adicUpperStarCongr l e.symm).hom.app ((p)^*ᵃ[l].obj M) ≫
        (adicUpperStarComp l g g').hom.app ((p)^*ᵃ[l].obj M) ≫
        (g)^*ᵃ[l].map ((adicUpperStarComp l g' p).inv.app M ≫
          (adicUpperStarCongr l h').hom.app M) ≫
        (adicUpperStarComp l g p).inv.app M ≫ (adicUpperStarCongr l h).hom.app M =
      (adicUpperStarComp l g'' p).inv.app M ≫ (adicUpperStarCongr l h'').hom.app M := by
  subst e
  have a := adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app (l := l) g g' p M
  have a' : (adicUpperStarComp l g g').hom.app ((p)^*ᵃ[l].obj M) ≫
      (g)^*ᵃ[l].map ((adicUpperStarComp l g' p).inv.app M) =
      (adicUpperStarComp l (g ≫ g') p).inv.app M ≫
        (adicUpperStarCongr l (Category.assoc g g' p)).hom.app M ≫
        (adicUpperStarComp l g (g' ≫ p)).hom.app M := by
    rw [← cancel_epi ((adicUpperStarComp l (g ≫ g') p).hom.app M), reassoc_of% a,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have c := adicUpperStarComp_inv_app_comp_congr_comp_hom_app (l := l) g h'
    (by rw [h']) M
  have c' : (adicUpperStarComp l g (g' ≫ p)).hom.app M ≫
      (g)^*ᵃ[l].map ((adicUpperStarCongr l h').hom.app M) =
      (adicUpperStarCongr l (by rw [h'] : g ≫ g' ≫ p = g ≫ p)).hom.app M ≫
        (adicUpperStarComp l g p).hom.app M := by
    rw [← c, Iso.hom_inv_id_app_assoc]
  rw [adicUpperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.map_comp, Category.assoc, reassoc_of% a', reassoc_of% c', Iso.hom_inv_id_app_assoc,
    AdicSheaf.adicUpperStarCongr_hom_app_trans_assoc _ _ (by rw [Category.assoc, h']),
    AdicSheaf.adicUpperStarCongr_hom_app_trans]


/-- The congruence isomorphisms of `ℓ`-adic pullbacks are `eqToHom`s. -/
lemma adicUpperStarCongr_hom_app_eq_eqToHom {X Z : Scheme.{u}} {x y : X ⟶ Z} (p : x = y)
    (M : AdicSheaf l Z) :
    (adicUpperStarCongr l p).hom.app M = eqToHom (by rw [p]) := by
  subst p
  rfl

/-- The associativity law for the composition isomorphisms of `ℓ`-adic pullbacks, in the form
`(f ≫ g)^* ⟶ g^* f^*` composed with the inverse of `g^* (h^* ≅ ...)`. -/
lemma adicUpperStarComp_hom_app_comp_map_adicUpperStarComp_inv_app {Q P W Y : Scheme.{u}}
    (f : Q ⟶ P) (g : P ⟶ W) (h : W ⟶ Y) (M : AdicSheaf l Y) :
    (adicUpperStarComp l f g).hom.app ((h)^*ᵃ[l].obj M) ≫
        (f)^*ᵃ[l].map ((adicUpperStarComp l g h).inv.app M) =
      (adicUpperStarComp l (f ≫ g) h).inv.app M ≫
        (adicUpperStarCongr l (Category.assoc f g h)).hom.app M ≫
        (adicUpperStarComp l f (g ≫ h)).hom.app M := by
  have a := adicUpperStarComp_hom_app_comp_adicUpperStarComp_hom_app (l := l) f g h M
  rw [← cancel_epi ((adicUpperStarComp l (f ≫ g) h).hom.app M), reassoc_of% a,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The associativity law for the inverses of the composition isomorphisms. -/
lemma map_adicUpperStarComp_inv_app_comp_adicUpperStarComp_inv_app {Q P W Y : Scheme.{u}}
    (f : Q ⟶ P) (g : P ⟶ W) (h : W ⟶ Y) (M : AdicSheaf l Y) :
    (f)^*ᵃ[l].map ((adicUpperStarComp l g h).inv.app M) ≫
        (adicUpperStarComp l f (g ≫ h)).inv.app M =
      (adicUpperStarComp l f g).inv.app ((h)^*ᵃ[l].obj M) ≫
        (adicUpperStarComp l (f ≫ g) h).inv.app M ≫
        (adicUpperStarCongr l (Category.assoc f g h)).hom.app M := by
  rw [← cancel_epi ((adicUpperStarComp l f g).hom.app ((h)^*ᵃ[l].obj M)),
    reassoc_of% (adicUpperStarComp_hom_app_comp_map_adicUpperStarComp_inv_app f g h M),
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The pullback of a congruence isomorphism followed by a composition isomorphism. -/
lemma adicUpperStarComp_hom_app_comp_map_adicUpperStarCongr_hom_app {Q X Z : Scheme.{u}}
    (c : Q ⟶ X) {x y : X ⟶ Z} (p : x = y) (p' : c ≫ x = c ≫ y) (M : AdicSheaf l Z) :
    (adicUpperStarComp l c x).hom.app M ≫ (c)^*ᵃ[l].map ((adicUpperStarCongr l p).hom.app M) =
      (adicUpperStarCongr l p').hom.app M ≫ (adicUpperStarComp l c y).hom.app M := by
  rw [← AdicSheaf.adicUpperStarComp_inv_app_comp_congr_comp_hom_app c p p' M,
    Iso.hom_inv_id_app_assoc]

/-- The pullback of a congruence isomorphism followed by the inverse of a composition
isomorphism. -/
lemma map_adicUpperStarCongr_hom_app_comp_adicUpperStarComp_inv_app {Q X Z : Scheme.{u}}
    (c : Q ⟶ X) {x y : X ⟶ Z} (p : x = y) (p' : c ≫ x = c ≫ y) (M : AdicSheaf l Z) :
    (c)^*ᵃ[l].map ((adicUpperStarCongr l p).hom.app M) ≫ (adicUpperStarComp l c y).inv.app M =
      (adicUpperStarComp l c x).inv.app M ≫ (adicUpperStarCongr l p').hom.app M := by
  rw [← AdicSheaf.adicUpperStarComp_inv_app_comp_congr_comp_hom_app c p p' M,
    Category.assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- A congruence isomorphism of the first morphism followed by the inverse of a composition
isomorphism. -/
lemma adicUpperStarCongr_hom_app_comp_adicUpperStarComp_inv_app {X Z Z' : Scheme.{u}}
    {x y : X ⟶ Z'} (z : Z' ⟶ Z) (p : x = y) (p' : x ≫ z = y ≫ z) (M : AdicSheaf l Z) :
    (adicUpperStarCongr l p).hom.app ((z)^*ᵃ[l].obj M) ≫ (adicUpperStarComp l y z).inv.app M =
      (adicUpperStarComp l x z).inv.app M ≫ (adicUpperStarCongr l p').hom.app M := by
  rw [← cancel_epi ((adicUpperStarComp l x z).hom.app M), Iso.hom_inv_id_app_assoc,
    reassoc_of% (AdicSheaf.adicUpperStarComp_hom_app_comp_congr z p p' M),
    Iso.hom_inv_id_app, Category.comp_id]

/-- **The transport of sections of a pullback along a square** `τ ≫ s = s ≫ g` with
`g ≫ p = p`, through the identifications `g^* p^* ≅ p^*` and `s^* p^* ≅ x^*`, is the pullback
along `τ` for `τ ≫ x = x`. -/
lemma adicUpperStarComp_coherence_of_square {P Y Z : Scheme.{u}} (τ : P ⟶ P) (s : P ⟶ Y)
    (g : Y ⟶ Y) (p : Y ⟶ Z) {x : P ⟶ Z} (hτ : τ ≫ s = s ≫ g) (hg : g ≫
        p = p) (hx : s ≫ p = x)
    (hτx : τ ≫ x = x) (M : AdicSheaf l Z) :
    (adicUpperStarComp l τ s).inv.app ((p)^*ᵃ[l].obj M) ≫
        (adicUpperStarCongr l hτ).hom.app ((p)^*ᵃ[l].obj M) ≫
        (adicUpperStarComp l s g).hom.app ((p)^*ᵃ[l].obj M) ≫
        (s)^*ᵃ[l].map ((adicUpperStarComp l g p).inv.app M ≫
            (adicUpperStarCongr l hg).hom.app M) ≫
        (adicUpperStarComp l s p).inv.app M ≫ (adicUpperStarCongr l hx).hom.app M =
      (τ)^*ᵃ[l].map ((adicUpperStarComp l s p).inv.app M ≫
          (adicUpperStarCongr l hx).hom.app M) ≫
        (adicUpperStarComp l τ x).inv.app M ≫ (adicUpperStarCongr l hτx).hom.app M := by
  simp only [Functor.map_comp, Category.assoc]
  rw [
    reassoc_of% (adicUpperStarComp_hom_app_comp_map_adicUpperStarComp_inv_app s g p M),
    reassoc_of% adicUpperStarComp_hom_app_comp_map_adicUpperStarCongr_hom_app s hg
      (by rw [hg]), Iso.hom_inv_id_app_assoc,
    reassoc_of% adicUpperStarCongr_hom_app_comp_adicUpperStarComp_inv_app p hτ (by rw [hτ]),
    reassoc_of% map_adicUpperStarCongr_hom_app_comp_adicUpperStarComp_inv_app τ hx (by rw [hx]),
    reassoc_of% (map_adicUpperStarComp_inv_app_comp_adicUpperStarComp_inv_app τ s p M)]
  simp only [adicUpperStarCongr_hom_app_eq_eqToHom, eqToHom_trans]

end AlgebraicGeometry.ProEtale
