/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaCoherence
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

/-!

# Coherence of the projection formula

This file derives, in the form used by the Künneth–Verdier theorem, standard coherences of the
canonical isomorphisms of the six-functor formalism on the bounded constructible derived
categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (SGA 4, Exposé XVII, §5), stated for the projection morphism
`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism`
(`PF_f : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)`) and the composition isomorphisms
`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`
(`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`) and `ProEtale.CondensedRing.boundedConstructibleUpperStarComp`
(`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`). They are deduced from the clauses of blueprint
`prop-sf-pf-coherence` stated in `WeilConjectures.PoincareDuality.ProjectionFormulaCoherence`.

The companion coherence of compact-support base change with the pasting of cartesian squares
(blueprint `proposition-composition-base-change-rf-shriek`, clause (2)) is
`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert`
(`WeilConjectures.TraceFormula.BaseChangeCoherence`).

## Main statements

- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_comp`: the projection
  formula is compatible with composition, in the form with `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` applied to
  both sides.
- `ProEtale.CondensedRing.boundedConstructiblePullbackSquareComparison_hom_app_δ`: the pullback
  comparison of a commutative square is monoidal.
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_baseChange`: for
  proper vertical maps, the projection formula is compatible with compact-support base change.

## Implementation notes

The diagram chases are carried out for abstract functors (`Functor.OplaxMonoidal.trans_hom_app_δ`,
`CategoryTheory.ProjectionBaseChange.pfBaseChange_of_counit`). As in
`WeilConjectures.TraceFormula.KunnethVerdierOpen`, the projection of the monoidal category
instance is made the preferred tensor structure. The coefficient ring
`Profinite.padicAlgClRingObj ℓ` is written explicitly in the statement of
`boundedConstructiblePullbackSquareComparison_hom_app_δ`: leaving it to unification produces a
different (propositionally equal) `Precoherent Profinite` instance in the types, and comparing
the two statements then times out.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Functor.OplaxMonoidal

/-- A composite `e₁⁻¹ ≪≫ e ≪≫ e₂ : G₁ ⋙ F₁ ≅ G₂ ⋙ F₂` of isomorphisms compatible with the
comultiplications of oplax monoidal functors `P`, `Q` and of the composites is compatible with
the comultiplications.

The monoidal structures are implicit arguments, determined by unification with the hypotheses,
so that the lemma applies whichever (definitionally equal) instances these are stated with. -/
lemma trans_hom_app_δ {C D E : Type*} [Category C] [Category D] [Category E]
    {_ : MonoidalCategory C} {_ : MonoidalCategory D} {_ : MonoidalCategory E} {D' : Type*}
    [Category D'] {_ : MonoidalCategory D'} {G₁ : C ⥤ D} {F₁ : D ⥤ E} {G₂ : C ⥤ D'}
    {F₂ : D' ⥤ E} {P Q : C ⥤ E}
    {_ : G₁.OplaxMonoidal} {_ : F₁.OplaxMonoidal} {_ : G₂.OplaxMonoidal} {_ : F₂.OplaxMonoidal}
    {_ : P.OplaxMonoidal} {_ : Q.OplaxMonoidal} (e₁ : P ≅ G₁ ⋙ F₁) (e : P ≅ Q) (e₂ : Q ≅ G₂ ⋙ F₂)
    (h₁ : ∀ A B, δ P A B ≫ (e₁.hom.app A ⊗ₘ e₁.hom.app B) =
      e₁.hom.app (A ⊗ B) ≫ F₁.map (δ G₁ A B) ≫ δ F₁ _ _)
    (h : ∀ A B, e.hom.app (A ⊗ B) ≫ δ Q A B = δ P A B ≫ (e.hom.app A ⊗ₘ e.hom.app B))
    (h₂ : ∀ A B, δ Q A B ≫ (e₂.hom.app A ⊗ₘ e₂.hom.app B) =
      e₂.hom.app (A ⊗ B) ≫ F₂.map (δ G₂ A B) ≫ δ F₂ _ _) (A B : C) :
    (e₁.symm ≪≫ e ≪≫ e₂).hom.app (A ⊗ B) ≫ F₂.map (δ G₂ A B) ≫ δ F₂ _ _ =
      F₁.map (δ G₁ A B) ≫ δ F₁ _ _ ≫
        ((e₁.symm ≪≫ e ≪≫ e₂).hom.app A ⊗ₘ (e₁.symm ≪≫ e ≪≫ e₂).hom.app B) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← h₂ A B, reassoc_of% (h A B), ← cancel_epi (e₁.hom.app (A ⊗ B)),
    Iso.hom_inv_id_app_assoc, ← reassoc_of% (h₁ A B)]
  simp only [tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

/-- **The projection formula is compatible with composition** (blueprint `prop-sf-pf-coherence`,
the associativity pentagon; SGA 4, Exposé XVII, 5.2.2): for `f : X ⟶ Y` and `g : Y ⟶ S`, the
projection morphism of `f ≫ g`, followed by the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` and `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, is the composite
```
R(f ≫ g)_! K ⊗ B ≅ Rg_! (Rf_! K) ⊗ B --PF_g--> Rg_! (Rf_! K ⊗ Lg^* B)
  --Rg_! PF_f--> Rg_! Rf_! (K ⊗ Lf^* Lg^* B).
```
This is `exceptionalProjection_comp`, with the composition isomorphism moved to the left. -/
theorem boundedConstructibleExceptionalProjectionMorphism_comp (f : X ⟶ Y) (g : Y ⟶ S)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism ℓ (f ≫ g) K B ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj B) ≫
        (boundedConstructibleLowerShriek ℓ g).map ((boundedConstructibleLowerShriek ℓ f).map
          (K ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app B)) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism ℓ g
          ((boundedConstructibleLowerShriek ℓ f).obj K) B ≫
        (boundedConstructibleLowerShriek ℓ g).map
          (boundedConstructibleExceptionalProjectionMorphism ℓ f K
            ((boundedConstructibleUpperStar _ ℓ g).obj B)) := by
  have hn : (boundedConstructibleLowerShriek ℓ (f ≫ g)).map
        (K ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app B) ≫
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
        (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj
          ((boundedConstructibleUpperStar _ ℓ g).obj B)) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj B) ≫
        (boundedConstructibleLowerShriek ℓ g).map ((boundedConstructibleLowerShriek ℓ f).map
          (K ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app B)) :=
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.naturality _
  rw [← hn, reassoc_of% (exceptionalProjection_comp ℓ f g K B), Iso.inv_hom_id_app]
  erw [Category.comp_id]

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The tensor comparison of `Lr^*` is compatible with the identification `Lr^* = Lr'^*` of equal
morphisms `r = r'`. -/
lemma eqToIso_hom_app_δ_boundedConstructibleUpperStar {r r' : X' ⟶ Y} (hr : r = r')
    (p : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r =
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ r')
    (A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (eqToIso p).hom.app (A ⊗ B) ≫ δ (boundedConstructibleUpperStar _ ℓ r') A B =
      δ (boundedConstructibleUpperStar _ ℓ r) A B ≫
        ((eqToIso p).hom.app A ⊗ₘ (eqToIso p).hom.app B) := by
  subst hr
  rw [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, NatTrans.id_app, NatTrans.id_app,
    Category.id_comp, id_tensorHom_id, Category.comp_id]

/-- A natural isomorphism `θ' = e₁⁻¹ ≪≫ (L u = L v) ≪≫ e₂ : Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*`, for
isomorphisms `e₁ : L u ≅ Lg^* ⋙ Lf'^*` and `e₂ : L v ≅ Lf^* ⋙ Lg'^*` compatible with the tensor
comparisons and `u = v`, is compatible with the tensor comparisons. -/
lemma hom_app_δ_of_eq_trans_eqToIso_trans {u v : X' ⟶ Y} (huv : u = v)
    (e₁ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ u ≅
      boundedConstructibleUpperStar _ ℓ g ⋙ boundedConstructibleUpperStar _ ℓ f')
    (e₂ : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v ≅
      boundedConstructibleUpperStar _ ℓ f ⋙ boundedConstructibleUpperStar _ ℓ g')
    (h₁ : ∀ A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      δ (boundedConstructibleUpperStar _ ℓ u) A B ≫ (e₁.hom.app A ⊗ₘ e₁.hom.app B) =
      e₁.hom.app (A ⊗ B) ≫
        (boundedConstructibleUpperStar _ ℓ f').map (δ (boundedConstructibleUpperStar _ ℓ g) A B) ≫
        δ (boundedConstructibleUpperStar _ ℓ f') _ _)
    (h₂ : ∀ A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      δ (boundedConstructibleUpperStar _ ℓ v) A B ≫ (e₂.hom.app A ⊗ₘ e₂.hom.app B) =
      e₂.hom.app (A ⊗ B) ≫
        (boundedConstructibleUpperStar _ ℓ g').map (δ (boundedConstructibleUpperStar _ ℓ f) A B) ≫
        δ (boundedConstructibleUpperStar _ ℓ g') _ _)
    (p : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ u =
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ v)
    (θ' : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f' ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
    (hθ : θ' = e₁.symm ≪≫ eqToIso p ≪≫ e₂) (A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    θ'.hom.app (A ⊗ B) ≫
        (boundedConstructibleUpperStar _ ℓ g').map (δ (boundedConstructibleUpperStar _ ℓ f) A B) ≫
        δ (boundedConstructibleUpperStar _ ℓ g') _ _ =
      (boundedConstructibleUpperStar _ ℓ f').map (δ (boundedConstructibleUpperStar _ ℓ g) A B) ≫
        δ (boundedConstructibleUpperStar _ ℓ f') _ _ ≫
        (θ'.hom.app A ⊗ₘ θ'.hom.app B) := by
  subst hθ huv
  exact Functor.OplaxMonoidal.trans_hom_app_δ e₁ (eqToIso p) e₂ h₁
    (eqToIso_hom_app_δ_boundedConstructibleUpperStar ℓ rfl p) h₂ A B

/-- **The pullback comparison of a commutative square is monoidal**: the identification
`θ : Lf'^* Lg^* ≅ Lg'^* Lf^*` of a commutative square `g' ≫ f = f' ≫ g`
(`boundedConstructiblePullbackSquareComparison`) commutes with the tensor comparisons of the
pullbacks. -/
lemma boundedConstructiblePullbackSquareComparison_hom_app_δ (sq : CommSq g' f' f g)
    (A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq).hom.app
          (A ⊗ B) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').map
          (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) A B) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g') _ _ =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f').map
          (δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g) A B) ≫
        δ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f') _ _ ≫
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
            sq).hom.app A ⊗ₘ
          (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
            sq).hom.app B) := by
  have h₁ : ∀ A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      δ (boundedConstructibleUpperStar _ ℓ (f' ≫ g)) A B ≫
        ((boundedConstructibleUpperStarComp _ ℓ f' g).hom.app A ⊗ₘ
          (boundedConstructibleUpperStarComp _ ℓ f' g).hom.app B) =
      (boundedConstructibleUpperStarComp _ ℓ f' g).hom.app (A ⊗ B) ≫
        (boundedConstructibleUpperStar _ ℓ f').map (δ (boundedConstructibleUpperStar _ ℓ g) A B) ≫
        δ (boundedConstructibleUpperStar _ ℓ f') _ _ :=
    fun A B ↦ boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ f' g A B
  have h₂ : ∀ A B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      δ (boundedConstructibleUpperStar _ ℓ (g' ≫ f)) A B ≫
        ((boundedConstructibleUpperStarComp _ ℓ g' f).hom.app A ⊗ₘ
          (boundedConstructibleUpperStarComp _ ℓ g' f).hom.app B) =
      (boundedConstructibleUpperStarComp _ ℓ g' f).hom.app (A ⊗ B) ≫
        (boundedConstructibleUpperStar _ ℓ g').map (δ (boundedConstructibleUpperStar _ ℓ f) A B) ≫
        δ (boundedConstructibleUpperStar _ ℓ g') _ _ :=
    fun A B ↦ boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ g' f A B
  have p : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f' ≫ g) =
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g' ≫ f) := by
    rw [sq.w]
  have e : boundedConstructiblePullbackSquareComparison _ ℓ sq =
      (boundedConstructibleUpperStarComp _ ℓ f' g).symm ≪≫ eqToIso p ≪≫
        boundedConstructibleUpperStarComp _ ℓ g' f := rfl
  have key := hom_app_δ_of_eq_trans_eqToIso_trans ℓ sq.w.symm
    (boundedConstructibleUpperStarComp _ ℓ f' g) (boundedConstructibleUpperStarComp _ ℓ g' f)
    h₁ h₂ p (boundedConstructiblePullbackSquareComparison _ ℓ sq) e A B
  exact key

/-- **The projection formula is compatible with base change** (blueprint `prop-sf-pf-coherence`,
the base change square; SGA 4, Exposé XVII, 5.2.2 and 5.2.9), for proper vertical maps: for a
cartesian square `g' ≫ f = f' ≫ g` with `f` and `f'` proper, under compact-support base change
`Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`, the monoidal structures of `Lg^*`, `Lg'^*` and the
identification `θ : Lg'^* Lf^* ≅ Lf'^* Lg^*`, `Lg^*` of the projection morphism of `f` is the
projection morphism of `f'`:
```
Lg^* (Rf_! K ⊗ B) ⟶ Lg^* Rf_! (K ⊗ Lf^* B) ⟶ Rf'_! Lg'^* (K ⊗ Lf^* B)
  ≅ Rf'_! (Lg'^* K ⊗ Lg'^* Lf^* B) ≅ Rf'_! (Lg'^* K ⊗ Lf'^* Lg^* B)
=  Lg^* (Rf_! K ⊗ B) ≅ Lg^* Rf_! K ⊗ Lg^* B ⟶ Rf'_! Lg'^* K ⊗ Lg^* B
  ⟶ Rf'_! (Lg'^* K ⊗ Lf'^* Lg^* B).
```
(`CategoryTheory.ProjectionBaseChange.PFBaseChange`, with `K` and `B` the variables of the formula
and `θ = boundedConstructiblePullbackSquareComparison`). Both projection morphisms are those of
the adjunctions `Lf^* ⊣ Rf_!` and `Lf'^* ⊣ Rf'_!`
(`upperStar_map_exceptionalProjection_comp_counit`) and `Ex_!` is the mate of `θ`, so this is
`CategoryTheory.ProjectionBaseChange.pfBaseChange_of_counit`. -/
theorem boundedConstructibleExceptionalProjectionMorphism_baseChange (sq : IsPullback g' f' f g)
    [IsProper f.left] [IsProper f'.left] :
    ProjectionBaseChange.PFBaseChange
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq)
      (boundedConstructibleExceptionalProjection ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f') := by
  refine ProjectionBaseChange.pfBaseChange_of_counit
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f')
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f) _ _ _ _ _ _
    ?_ ?_ ?_ ?_
  · exact fun A B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ f A B
  · exact fun A B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ f' A B
  · intro K
    refine ProjectionBaseChange.counit_mate_of_unit
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f')
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        sq.toCommSq)
      (fun M ↦ ?_) K
    exact map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app ℓ sq M
  · exact fun A B ↦ boundedConstructiblePullbackSquareComparison_hom_app_δ ℓ sq.toCommSq A B


end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
