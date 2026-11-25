/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleSquareCoherence
public import WeilConjectures.TraceFormula.ShriekTrace

/-!

# Coherence of composition isomorphisms around a pushforward square

For morphisms `g : C ⟶ D`, `b : D ⟶ W`, `c : C ⟶ V`, `q : V ⟶ W`, `p : W ⟶ Y`, `p' : V ⟶ X` and
`f : X ⟶ Y` with `g ≫ b = c ≫ q` and `q ≫ p = p' ≫ f`, the two identifications of
`Rg_! ⋙ Rb_! ⋙ Rp_!` with `Rc_! ⋙ Rp'_! ⋙ Rf_!` built from the composition isomorphisms agree
(`ProEtale.CondensedRing.lowerShriekComp_pushforwardSquare`), and similarly for the derived
pullbacks (`ProEtale.CondensedRing.upperStarComp_pushforwardSquare`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

@[reassoc]
lemma MonoidalCategory.rightUnitor_inv_comp_whiskerRight_comp_hom {C : Type*} [Category C]
    [MonoidalCategory C] {X Y : C} (f : X ⟶ Y) : (ρ_ X).inv ≫ f ▷ 𝟙_ C ≫ (ρ_ Y).hom = f := by
  simp

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {C D V W X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType D.hom] [QuasiCompact D.hom] [IsSeparated D.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

@[reassoc]
lemma lowerShriek_map_eqToHom_comp_lowerShriekComp_inv_app' {u u' : C ⟶ D} (h : u = u')
    (z : D ⟶ W) (M : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek ℓ z).map (eqToHom (by rw [h])) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u' z).inv.app M =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ u z).inv.app M ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The composition isomorphisms of the compactly supported direct images around a pushforward
square agree. -/
@[reassoc]
lemma lowerShriekComp_pushforwardSquare (g : C ⟶ D) (b : D ⟶ W) (c : C ⟶ V) (q : V ⟶ W)
    (p : W ⟶ Y) (p' : V ⟶ X) (f : X ⟶ Y) (hgq : g ≫ b = c ≫ q) (hq : q ≫ p = p' ≫ f)
    (w : g ≫ b ≫ p = (c ≫ p') ≫ f) (M : Dᵇc(C.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b p).inv.app
        ((boundedConstructibleLowerShriek ℓ g).obj M) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (b ≫ p)).inv.app M ≫
      eqToHom (by rw [w]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (c ≫ p') f).hom.app M =
    (boundedConstructibleLowerShriek ℓ p).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app M) ≫
      (boundedConstructibleLowerShriek ℓ p).map (eqToHom (by rw [hgq])) ≫
      (boundedConstructibleLowerShriek ℓ p).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c q).hom.app M) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ hq).hom.app
        ((boundedConstructibleLowerShriek ℓ c).obj M) ≫
      (boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ c p').inv.app M) := by
  have h₁ := lowerShriek_map_lowerShriekComp_inv_app_comp_inv_app ℓ g b p M
  have h₁' : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ b p).inv.app
        ((boundedConstructibleLowerShriek ℓ g).obj M) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (b ≫ p)).inv.app M =
      (boundedConstructibleLowerShriek ℓ p).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g b).inv.app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ b) p).inv.app M ≫
        eqToHom (by rw [Category.assoc]) := by
    rw [reassoc_of% h₁]
    simp
  rw [reassoc_of% h₁']
  refine whisker_eq _ ?_
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_obj,
    Category.assoc]
  rw [lowerShriek_map_lowerShriekComp_hom_app_comp_inv_app_assoc ℓ c q p M,
    lowerShriek_map_eqToHom_comp_lowerShriekComp_inv_app'_assoc ℓ hgq p M]
  refine whisker_eq _ ?_
  rw [lowerShriekComp_hom_app_comp_eqToHom_assoc ℓ hq c M,
    lowerShriekComp_hom_app_comp_hom_app_assoc]
  simp

section Pullback

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The composition isomorphisms with a common first map are compatible with the casts along
`r = r'`. -/
@[reassoc]
lemma boundedConstructibleUpperStarComp_hom_app_map_eqToHom {r r' : V ⟶ W} (h : r = r')
    (a : C ⟶ V) (A : Dᵇc(W.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarComp Λ ℓ a r).hom.app A ≫
      (boundedConstructibleUpperStar Λ ℓ a).map
        (eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar Λ ℓ r).obj A) h)) =
    eqToHom (by rw [h]) ≫ (boundedConstructibleUpperStarComp Λ ℓ a r').hom.app A := by
  subst h
  simp

/-- The composition isomorphisms of the derived pullbacks around a pushforward square agree. -/
lemma boundedConstructibleUpperStarComp_pushforwardSquare (g : C ⟶ D) (b : D ⟶ W) (c : C ⟶ V)
    (q : V ⟶ W) (p : W ⟶ Y) (p' : V ⟶ X) (f : X ⟶ Y) (hgq : g ≫ b = c ≫ q)
    (hq : q ≫ p = p' ≫ f) (w : g ≫ b ≫ p = (c ≫ p') ≫ f) (N : Dᵇc(Y.left)⟦Λ⟧) :
    (boundedConstructibleUpperStar Λ ℓ g).map
        ((boundedConstructibleUpperStarComp Λ ℓ b p).inv.app N) ≫
      (boundedConstructibleUpperStarComp Λ ℓ g (b ≫ p)).inv.app N ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj N) w) ≫
      (boundedConstructibleUpperStarComp Λ ℓ (c ≫ p') f).hom.app N =
    (boundedConstructibleUpperStarComp Λ ℓ g b).inv.app
        ((boundedConstructibleUpperStar Λ ℓ p).obj N) ≫
      eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj
        ((boundedConstructibleUpperStar Λ ℓ p).obj N)) hgq) ≫
      (boundedConstructibleUpperStarComp Λ ℓ c q).hom.app
          ((boundedConstructibleUpperStar Λ ℓ p).obj N) ≫
      (boundedConstructibleUpperStar Λ ℓ c).map
        ((boundedConstructibleUpperStarComp Λ ℓ q p).inv.app N ≫
          eqToHom (congrArg (fun u ↦ (boundedConstructibleUpperStar Λ ℓ u).obj N) hq) ≫
          (boundedConstructibleUpperStarComp Λ ℓ p' f).hom.app N) ≫
      (boundedConstructibleUpperStarComp Λ ℓ c p').inv.app
          ((boundedConstructibleUpperStar Λ ℓ f).obj N) := by
  have e₁ := boundedConstructibleUpperStarComp_hom_app_map_inv_app Λ ℓ c q p N
  have e₂ := boundedConstructibleUpperStar_map_hom_app_comp_inv_app Λ ℓ c p' f N
  have e₃ := boundedConstructibleUpperStarComp_hom_app_map_eqToHom ℓ Λ hq c N
  have e₅ := eqToHom_comp_boundedConstructibleUpperStarComp_inv_app Λ ℓ hgq p N
  have e₆ := boundedConstructibleUpperStarComp_inv_app_comp_inv_app' Λ ℓ g b p N
  simp only [Functor.map_comp, Category.assoc]
  rewrite [reassoc_of% e₁, reassoc_of% e₅, reassoc_of% e₆, reassoc_of% e₃]
  simp only [e₂, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc]

end Pullback

end AlgebraicGeometry.ProEtale.CondensedRing
