/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.TraceFormula.ProperKunneth

/-!

# Composition isomorphisms and base change along a factored square

Two coherences of the six-functor package on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` for a commutative square whose top side
factors as `q = g ≫ h`, used for the exceptional Künneth part of identity (a) of the trace-class
source exchange (blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 3):

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekSquareIso_padicAlgCl_hom_app_comp`: the
  composition isomorphism of the square is pasted from those of its pieces;
- `ProEtale.CondensedRing.unit_comp_lowerShriek_map_prodUpperStarCounit`: the adjoint of the
  transported counit of the outer square is the adjoint of the compact-support base change of a
  cartesian piece.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Generic

variable {P Q R X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
  [LocallyOfFiniteType R.hom] [QuasiCompact R.hom] [IsSeparated R.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The components of the composition isomorphism of a commutative square
`g' ≫ f = f' ≫ g`. -/
theorem boundedConstructibleLowerShriekSquareIso_padicAlgCl_hom_app {g' : P ⟶ Q} {f : Q ⟶ Y}
    {f' : P ⟶ X} {g : X ⟶ Y} (w : g' ≫ f = f' ≫ g)
    (S : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app S =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g' f).inv.app S ≫ eqToHom (by rw [w]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f' g).hom.app S := by
  dsimp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom]
  rw [eqToHom_app]

/-- The composition isomorphisms `R(g ≫ u)_! ≅ Rg_! ⋙ Ru_!` and `R(g ≫ u')_! ≅ Rg_! ⋙ Ru'_!` of
equal morphisms `u = u'` differ by the evident `eqToHom`. -/
theorem boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_comp_eqToHom_comp_inv_app
    (g : P ⟶ Q) {u u' : Q ⟶ Y} (e : u = u') (S : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g u).hom.app S ≫ eqToHom (by rw [e]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g u').inv.app S =
      eqToHom (by rw [e]) := by
  subst e
  simp

-- the `Mono` instance of `Functor.map` of an isomorphism needs a longer instance search
/-- The composition isomorphism of a commutative square `q ≫ p' = p ≫ f` whose top side factors
as `q = g ≫ h` and whose left side factors as `p = g ≫ p_X` is the composite of the composition
isomorphisms of `g` and `h`, of the square `h ≫ p' = p_X ≫ f` and of `g` and `p_X`. -/
theorem boundedConstructibleLowerShriekSquareIso_padicAlgCl_hom_app_comp {g : P ⟶ Q} {h : Q ⟶ R}
    {q : P ⟶ R} (hq : g ≫ h = q) {pX : Q ⟶ X} {p : P ⟶ X} (hp : g ≫ pX = p) {p' : R ⟶ Y}
    {f : X ⟶ Y} (w : q ≫ p' = p ≫ f) (w₁ : h ≫ p' = pX ≫ f)
    (S : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app S =
      (boundedConstructibleLowerShriek ℓ p').map
          (eqToHom (by rw [hq]) ≫
            (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app S) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w₁).hom.app
          ((boundedConstructibleLowerShriek ℓ g).obj S) ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g pX).inv.app S ≫
            eqToHom (by rw [hp])) := by
  subst hq hp
  have h₁ := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ g h p' S
  have h₂ := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ g pX f S
  have h₁' : (boundedConstructibleLowerShriek ℓ p').map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app S) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ h) p').inv.app S ≫
        eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (h ≫ p')).hom.app S ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h p').hom.app
          ((boundedConstructibleLowerShriek ℓ g).obj S) := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ h) p').hom.app S),
      h₁]
    simp only [Iso.hom_inv_id_app_assoc]
  have h₂' : (boundedConstructibleLowerShriekComp_padicAlgCl ℓ pX f).hom.app
        ((boundedConstructibleLowerShriek ℓ g).obj S) ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g pX).inv.app S) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (pX ≫ f)).inv.app S ≫
        eqToHom (by rw [Category.assoc]) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ (g ≫ pX) f).hom.app S := by
    rw [← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g (pX ≫ f)).hom.app S),
      Iso.hom_inv_id_app_assoc,
      ← cancel_mono ((boundedConstructibleLowerShriek ℓ f).map
        ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ g pX).hom.app S))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [h₂]
    simp only [Functor.comp_obj, eqToHom_refl, Category.id_comp]
  rw [boundedConstructibleLowerShriekSquareIso_padicAlgCl_hom_app,
    boundedConstructibleLowerShriekSquareIso_padicAlgCl_hom_app]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc, h₁',
    Iso.hom_inv_id_app_assoc]
  rw [h₂']
  simp only [reassoc_of%
    (boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_comp_eqToHom_comp_inv_app ℓ g w₁ S),
    eqToHom_trans_assoc]

/-- The inverse composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` read through the units: it is
the conjugate of the inverse composition isomorphism of the pullbacks. -/
theorem unit_app_comp_boundedConstructibleLowerStarComp_inv_app (g : P ⟶ Q) (h : Q ⟶ R)
    (T : Dᵇc(R.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (g ≫ h)).unit.app T ≫
        (boundedConstructibleLowerStarComp ℓ g h).inv.app
          ((boundedConstructibleUpperStar _ ℓ (g ≫ h)).obj T) =
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit.app T ≫
        (boundedConstructibleLowerStar ℓ h).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit.app
            ((boundedConstructibleUpperStar _ ℓ h).obj T)) ≫
        (boundedConstructibleLowerStar ℓ h).map ((boundedConstructibleLowerStar ℓ g).map
          ((boundedConstructibleUpperStarComp _ ℓ g h).inv.app T)) := by
  have hc := unit_conjugateEquiv
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (g ≫ h))
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ h).comp
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ g))
    (boundedConstructibleUpperStarComp _ ℓ g h).inv T
  rw [Adjunction.comp_unit_app] at hc
  simpa [boundedConstructibleLowerStarComp, conjugateIsoEquiv] using hc

/-- The direct-image version of `unit_comp_lowerShriek_map_prodUpperStarCounit`: for a commutative
square `g ≫ (h ≫ p₂') = p₂ ≫ f`, the adjoint of the transported counit of
`(g ≫ h) ≫ p₂' = p₂ ≫ f` for `L(g ≫ h)^* ⊣ R(g ≫ h)_*` is, read through
`Rg_* ⋙ Rh_* ≅ R(g ≫ h)_*`, the adjoint for `Lh^* ⊣ Rh_*` of the base change `Ex_*` of the
square. -/
theorem unit_comp_lowerStar_map_prodUpperStarCounit {g : P ⟶ Q} {h : Q ⟶ R} {p₂ : P ⟶ X}
    {p₂' : R ⟶ Y} {f : X ⟶ Y} (sq : CommSq p₂ g f (h ≫ p₂')) (w₂ : (g ≫ h) ≫ p₂' = p₂ ≫ f)
    (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (g ≫ h)).unit.app
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) ≫
      (boundedConstructibleLowerStar ℓ (g ≫ h)).map (prodUpperStarCounit ℓ w₂ B) ≫
      (boundedConstructibleLowerStarComp ℓ g h).inv.app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B) =
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit.app
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) ≫
      (boundedConstructibleLowerStar ℓ h).map
        ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
            ((boundedConstructibleLowerStar ℓ f).obj B) ≫
          (boundedConstructibleBaseChange ℓ sq).app B) := by
  have hn := (boundedConstructibleLowerStarComp ℓ g h).inv.naturality
    (prodUpperStarCounit ℓ w₂ B)
  have hc := unit_app_comp_boundedConstructibleLowerStarComp_inv_app ℓ g h
    ((boundedConstructibleUpperStar _ ℓ p₂').obj ((boundedConstructibleLowerStar ℓ f).obj B))
  have hu := congrArg (boundedConstructibleLowerStar ℓ h).map
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ g).unit_naturality
      ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
        ((boundedConstructibleLowerStar ℓ f).obj B)))
  have hr := congrArg (fun z ↦
      (boundedConstructibleLowerStar ℓ h).map ((boundedConstructibleLowerStar ℓ g).map z))
    (upperStarComp_inv_app_comp_prodUpperStarCounit_right ℓ w₂ sq.w.symm B)
  simp only [Functor.comp_map] at hn
  simp only [Functor.id_obj] at hc
  simp only [Functor.map_comp] at hu hr
  rw [← homEquiv_prodUpperStarCounit ℓ sq.w.symm B, Adjunction.homEquiv_unit, hn,
    reassoc_of% hc]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hu, hr]

/-- The base change morphism of the vertical composite of a cartesian square
`g ≫ p_Y = p₂ ≫ f` (with `g` and `f` proper) and the triangle `h ≫ p₂' = p_Y`, read through the
units of `Lq^* ⊣ Rq_!` and `Lh^* ⊣ Rh_!`: the adjoint of the transported counit of
`q ≫ p₂' = p₂ ≫ f` is the adjoint of the compact-support base change `Ex_!` of the cartesian
square. -/
theorem unit_comp_lowerShriek_map_prodUpperStarCounit {g : P ⟶ Q} {h : Q ⟶ R} {q : P ⟶ R}
    [IsProper g.left] [IsProper h.left] [IsProper q.left] (hq : g ≫ h = q) {p₂ : P ⟶ X}
    {pY : Q ⟶ Y} {p₂' : R ⟶ Y} {f : X ⟶ Y} [IsProper f.left] (sq : IsPullback p₂ g f pY)
    (wt : h ≫ p₂' = pY) (w₂ : q ≫ p₂' = p₂ ≫ f) (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).unit.app
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) ≫
      (boundedConstructibleLowerShriek ℓ q).map (prodUpperStarCounit ℓ w₂ B) ≫
      eqToHom (by rw [hq]) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ g h).hom.app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B) =
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ h).unit.app
        ((boundedConstructibleUpperStar _ ℓ p₂').obj
          ((boundedConstructibleLowerStar ℓ f).obj B)) ≫
      (boundedConstructibleLowerShriek ℓ h).map
        ((boundedConstructibleUpperStarComp _ ℓ h p₂').inv.app
            ((boundedConstructibleLowerStar ℓ f).obj B) ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj
            ((boundedConstructibleLowerStar ℓ f).obj B)) wt) ≫
          (boundedConstructibleUpperStar _ ℓ pY).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app B) ≫
          (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app B) := by
  subst hq wt
  have hA := unit_comp_lowerStar_map_prodUpperStarCounit ℓ sq.toCommSq w₂ B
  have hI := boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ g h
    ((boundedConstructibleUpperStar _ ℓ p₂).obj B)
  have hP := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ sq B
  rw [← Iso.cancel_iso_hom_right _ _
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).app
        ((boundedConstructibleLowerShriek ℓ g).obj
          ((boundedConstructibleUpperStar _ ℓ p₂).obj B)) ≪≫
    (boundedConstructibleLowerStar ℓ h).mapIso
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).app
        ((boundedConstructibleUpperStar _ ℓ p₂).obj B)))]
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc, eqToHom_refl, Category.id_comp]
  rw [hI]
  simp only [NatIso.naturality_1_assoc]
  dsimp only [Functor.comp_obj]
  rw [NatIso.naturality_1_assoc, hA]
  simp only [← Functor.map_comp, Category.assoc, hP]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Generic

end AlgebraicGeometry.ProEtale.CondensedRing
