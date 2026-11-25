/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence

/-!

# The exceptional projection morphism along a commutative square

Consequences of the coherence of the projection formula (blueprint `prop-sf-pf-coherence`) used
for the exceptional Künneth part of identity (a) of the trace-class source exchange (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 3):

- `ProEtale.CondensedRing.exceptionalProjection_comp_square`: for a commutative square
  `q ≫ p' = p ≫ f`, the projection morphisms of `q` and `p'` combine into those of `p` and `f`
  through the composition law;
- `ProEtale.CondensedRing.whiskerRight_unit_comp_exceptionalProjection`: for proper `q`, the
  projection morphism of `q` after the unit of `Lq^* ⊣ Rq_!` is the unit followed by the tensor
  structure of `Lq^*`;
- `ProEtale.CondensedRing.exceptionalProjection_comp_unit_square`: the two statements combined;
- `ProEtale.CondensedRing.whiskerRight_unit_comp_exceptionalProjection_tensorUnit`: the unit
  compatibility of the projection morphism of a proper morphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {P P' X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The exceptional projection morphisms of equal morphisms agree up to the casts. -/
lemma exceptionalProjection_eqToHom {u u' : P ⟶ Y} (h : u = u')
    (S : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {W : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (z : S ⊗ (boundedConstructibleUpperStar _ ℓ u').obj M ⟶ W) :
    boundedConstructibleExceptionalProjectionMorphism ℓ u S M ≫
        (boundedConstructibleLowerShriek ℓ u).map
          (S ◁ eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj M) h)) ≫
        (boundedConstructibleLowerShriek ℓ u).map z ≫
        eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj W) h) =
      (eqToHom (congrArg (fun r ↦ (boundedConstructibleLowerShriek ℓ r).obj S) h) ▷ M) ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ u' S M ≫
        (boundedConstructibleLowerShriek ℓ u').map z := by
  subst h
  simp

/-- **The exceptional projection morphism along a commutative square** (blueprint
`prop-sf-pf-coherence`, the associativity pentagon applied to both sides of `q ≫ p' = p ≫ f`):
`PF_{p'}` followed by `Rp'_! PF_q` is `PF_f` followed by `Rf_! PF_p`, through the composition
isomorphism `Rq_! ⋙ Rp'_! ≅ Rp_! ⋙ Rf_!` of the square. -/
theorem exceptionalProjection_comp_square {q : P ⟶ P'} {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f) (S : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ p'
        ((boundedConstructibleLowerShriek ℓ q).obj S) M ≫
      (boundedConstructibleLowerShriek ℓ p').map
        (boundedConstructibleExceptionalProjectionMorphism ℓ q S
          ((boundedConstructibleUpperStar _ ℓ p').obj M)) ≫
      (boundedConstructibleLowerShriek ℓ p').map ((boundedConstructibleLowerShriek ℓ q).map
        (S ◁ ((boundedConstructibleUpperStarComp _ ℓ q p').inv.app M ≫
          eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj M) w) ≫
          ((boundedConstructibleUpperStarComp _ ℓ p f).hom.app M :
            _ ⟶ (boundedConstructibleUpperStar _ ℓ p).obj
              ((boundedConstructibleUpperStar _ ℓ f).obj M))))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app
        (S ⊗ (boundedConstructibleUpperStar _ ℓ p).obj
          ((boundedConstructibleUpperStar _ ℓ f).obj M)) =
    ((boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app S ▷ M) ≫
      boundedConstructibleExceptionalProjectionMorphism ℓ f
        ((boundedConstructibleLowerShriek ℓ p).obj S) M ≫
      (boundedConstructibleLowerShriek ℓ f).map
        (boundedConstructibleExceptionalProjectionMorphism ℓ p S
          ((boundedConstructibleUpperStar _ ℓ f).obj M)) := by
  have h₁ := exceptionalProjection_comp ℓ q p' S M
  have h₂ := exceptionalProjection_comp ℓ p f S M
  have h₁' : boundedConstructibleExceptionalProjectionMorphism ℓ p'
        ((boundedConstructibleLowerShriek ℓ q).obj S) M ≫
      (boundedConstructibleLowerShriek ℓ p').map
        (boundedConstructibleExceptionalProjectionMorphism ℓ q S
          ((boundedConstructibleUpperStar _ ℓ p').obj M)) =
      ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ q p').inv.app S ▷ M) ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ (q ≫ p') S M ≫
        (boundedConstructibleLowerShriek ℓ (q ≫ p')).map
          (S ◁ (boundedConstructibleUpperStarComp _ ℓ q p').hom.app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ q p').hom.app _ := by
    rw [reassoc_of% h₁]
    simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id_app, id_whiskerRight,
      Category.id_comp]
    simp
  have hn := (boundedConstructibleLowerShriekComp_padicAlgCl ℓ q p').hom.naturality
    (S ◁ ((boundedConstructibleUpperStarComp _ ℓ q p').inv.app M ≫
      eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj M) w) ≫
      (boundedConstructibleUpperStarComp _ ℓ p f).hom.app M))
  simp only [Functor.comp_map] at hn
  have h₂' := exceptionalProjection_eqToHom ℓ w S M
    (S ◁ (boundedConstructibleUpperStarComp _ ℓ p f).hom.app M)
  simp only [boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, NatTrans.comp_app, eqToHom_app, reassoc_of% h₁']
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc]
  have hc : (boundedConstructibleLowerShriek ℓ (q ≫ p')).map
        (S ◁ (boundedConstructibleUpperStarComp _ ℓ q p').hom.app M) ≫
      (boundedConstructibleLowerShriek ℓ (q ≫ p')).map
        (S ◁ (boundedConstructibleUpperStarComp _ ℓ q p').inv.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app,
      MonoidalCategory.whiskerLeft_id, CategoryTheory.Functor.map_id]
  simp only [MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc,
    reassoc_of% hc]
  rw [reassoc_of% h₂', reassoc_of% h₂]
  simp only [Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id, comp_whiskerRight,
    Category.assoc]

variable (q : P ⟶ P') [IsProper q.left]

/-- For proper `q`, the exceptional projection morphism `PF_{q, Lq^* T, N}` after the unit of
`Lq^* ⊣ Rq_!` at `T` is the unit at `T ⊗ N` followed by `Rq_!` of the tensor structure of
`Lq^*`. -/
lemma whiskerRight_unit_comp_exceptionalProjection
    (T N : Dᵇc(P'.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).unit.app T ▷ N) ≫
      boundedConstructibleExceptionalProjectionMorphism ℓ q
        ((boundedConstructibleUpperStar _ ℓ q).obj T) N =
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).unit.app (T ⊗ N) ≫
      (boundedConstructibleLowerShriek ℓ q).map
        (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ q) T N) := by
  apply ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).homEquiv _
    _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    upperStar_map_exceptionalProjection_comp_counit, Adjunction.counit_naturality,
    Functor.id_obj, Functor.comp_obj, Adjunction.left_triangle_components_assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, ← comp_whiskerRight,
    Adjunction.left_triangle_components, id_whiskerRight, Category.comp_id]

variable {q} in
/-- **The exceptional projection morphism along a commutative square with proper top side**:
for `q ≫ p' = p ≫ f` with `q` proper, `PF_{p'}` followed by `Rp'_!` of the unit of `Lq^* ⊣ Rq_!`
is the unit followed by `PF_f` and `Rf_! PF_p`, through the composition isomorphism of the
square. -/
theorem exceptionalProjection_comp_unit_square {p : P ⟶ X} {p' : P' ⟶ Y} {f : X ⟶ Y}
    (w : q ≫ p' = p ≫ f)
    (T : Dᵇc(P'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ p' T M ≫
      (boundedConstructibleLowerShriek ℓ p').map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).unit.app
            (T ⊗ (boundedConstructibleUpperStar _ ℓ p').obj M) ≫
          (boundedConstructibleLowerShriek ℓ q).map
            (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ q) T
                ((boundedConstructibleUpperStar _ ℓ p').obj M) ≫
              ((boundedConstructibleUpperStar _ ℓ q).obj T ◁
                ((boundedConstructibleUpperStarComp _ ℓ q p').inv.app M ≫
                  eqToHom (congrArg (fun r ↦ (boundedConstructibleUpperStar _ ℓ r).obj M) w) ≫
                  ((boundedConstructibleUpperStarComp _ ℓ p f).hom.app M :
                    _ ⟶ (boundedConstructibleUpperStar _ ℓ p).obj
                      ((boundedConstructibleUpperStar _ ℓ f).obj M)))))) ≫
      (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app
        ((boundedConstructibleUpperStar _ ℓ q).obj T ⊗ (boundedConstructibleUpperStar _ ℓ p).obj
          ((boundedConstructibleUpperStar _ ℓ f).obj M)) =
    (((boundedConstructibleLowerShriek ℓ p').map
          ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).unit.app T) ≫
        (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ w).hom.app
          ((boundedConstructibleUpperStar _ ℓ q).obj T) :
          _ ⟶ (boundedConstructibleLowerShriek ℓ f).obj
            ((boundedConstructibleLowerShriek ℓ p).obj
              ((boundedConstructibleUpperStar _ ℓ q).obj T))) ▷ M) ≫
      boundedConstructibleExceptionalProjectionMorphism ℓ f
        ((boundedConstructibleLowerShriek ℓ p).obj ((boundedConstructibleUpperStar _ ℓ q).obj T))
        M ≫
      (boundedConstructibleLowerShriek ℓ f).map
        (boundedConstructibleExceptionalProjectionMorphism ℓ p
          ((boundedConstructibleUpperStar _ ℓ q).obj T)
          ((boundedConstructibleUpperStar _ ℓ f).obj M)) := by
  have hu := whiskerRight_unit_comp_exceptionalProjection ℓ q T
    ((boundedConstructibleUpperStar _ ℓ p').obj M)
  have hn := boundedConstructibleExceptionalProjectionMorphism_natural_left ℓ p'
    ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ q).unit.app T) M
  have hs := exceptionalProjection_comp_square ℓ w ((boundedConstructibleUpperStar _ ℓ q).obj T) M
  have hu' := congrArg (boundedConstructibleLowerShriek ℓ p').map hu
  simp only [Functor.map_comp] at hu'
  simp only [Functor.map_comp, Category.assoc] at hs ⊢
  rw [← reassoc_of% hu', ← reassoc_of% hn, hs, comp_whiskerRight, Category.assoc]

/-- **The unit compatibility of the projection morphism of a proper morphism**: the unit
`𝟙 ⟶ Rf_! 𝟙` of the lax monoidal functor `Rf_!` followed by `PF_{f, 𝟙, M}` is the unit of
`Lf^* ⊣ Rf_!` at `M`, read through the unitors. -/
theorem whiskerRight_unit_comp_exceptionalProjection_tensorUnit (f : X ⟶ Y) [IsProper f.left]
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app (𝟙_ _) ≫
          (boundedConstructibleLowerShriek ℓ f).map
            (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ f)).inv) ▷ M) ≫
      boundedConstructibleExceptionalProjectionMorphism ℓ f (𝟙_ _) M ≫
      (boundedConstructibleLowerShriek ℓ f).map (λ_ _).hom =
    (λ_ M).hom ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app M := by
  apply ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).homEquiv _
    _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality, Functor.id_obj, Functor.comp_obj,
    Adjunction.left_triangle_components, Category.comp_id]
  rw [reassoc_of% (upperStar_map_exceptionalProjection_comp_counit ℓ f),
    ← Functor.OplaxMonoidal.δ_natural_left_assoc, ← comp_whiskerRight_assoc]
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
    Adjunction.left_triangle_components_assoc, Functor.Monoidal.εIso_inv]
  exact Functor.OplaxMonoidal.left_unitality_hom _ _

end AlgebraicGeometry.ProEtale.CondensedRing
