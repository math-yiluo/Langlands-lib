/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces
public import WeilConjectures.TraceFormula.CurvePieces
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!

# The open piece coefficient and the counit of the extension by zero

Let `j : U ⟶ X` be an open immersion, `g : X ⟶ X` and `v : Lg^* K ⟶ K`. The open piece
coefficient `u^U : Lg^* j_! Lj^* K ⟶ j_! Lj^* K` is compatible with the counit
`ε : j_! Lj^* K ⟶ K` of `j_! ⊣ Lj^*`:
```
ε ∘ u^U = v ∘ Lg^* ε.
```
This is the first square of the morphism of open–closed triangles induced by `v` (blueprint
`proposition-additivity-trace-classes--2`, proof of item 2, step (a)).

* `ProEtale.CondensedRing.map_counit_comp_eq_openSquareExchange_hom_comp`: the general statement
  for any cartesian square `g_U ≫ j = j' ≫ g` of open immersions and any `v : Lg^* K ⟶ L`. Both
  sides are maps out of `j'_! Lg_U^* Lj^* K`; their `j'_! ⊣ Lj'^*` adjoints agree since the
  open-square exchange restricts to the pullback comparison on `U'`
  (`ProEtale.CondensedRing.unit_comp_map_openSquareExchange_inv`).
* `ProEtale.CondensedRing.Correspondence.graphOpenPieceCoeff_comp_counit`: the graph version, at
  a rational point fixed by `h`.
* `ProEtale.CondensedRing.WeilBoundedConstructible.openPieceCoeff_comp_counit`: the Frobenius
  version.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

/-- A natural transformation `θ : jU ⋙ H ⟶ H' ⋙ jU'` is compatible with the triangle identity of
an adjunction `jS ⊣ jU`: the composite
```
H (jU K) --H η--> H (jU (jS (jU K))) --θ--> jU' (H' (jS (jU K))) --jU' (H' ε)--> jU' (H' K)
```
is `θ_K`. -/
@[reassoc]
lemma map_unit_comp_app_comp_map_map_counit {A B A' B' : Type*} [Category* A]
    [Category* B] [Category* A'] [Category* B'] {jS : A ⥤ B} {jU : B ⥤ A} {jU' : B' ⥤ A'}
    {H : A ⥤ A'} {H' : B ⥤ B'} (aj : jS ⊣ jU) (θ : jU ⋙ H ⟶ H' ⋙ jU') (K : B) :
    H.map (aj.unit.app (jU.obj K)) ≫ θ.app (jS.obj (jU.obj K)) ≫
        jU'.map (H'.map (aj.counit.app K)) =
      θ.app K := by
  have h := θ.naturality (aj.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  rw [← h, ← Functor.map_comp_assoc, Adjunction.right_triangle_components]
  simp

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Cartesian squares of open immersions -/

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {U Y U' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
  [IsSeparated U'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {j : U ⟶ Y} {g : Y' ⟶ Y} {j' : U' ⟶ Y'} {gU : U' ⟶ U}
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

/-- **The open-square exchange and the counits of the extensions by zero**: for a cartesian
square `g_U ≫ j = j' ≫ g` with `j`, `j'` open immersions and a map `v : Lg^* K ⟶ L`,
```
Lg^* j_! Lj^* K --Lg^* ε--> Lg^* K --v--> L
  =  Lg^* j_! Lj^* K --b_g--> j'_! Lg_U^* Lj^* K --j'_! w--> j'_! Lj'^* L --ε--> L,
```
where `w : Lg_U^* Lj^* K ≅ Lj'^* Lg^* K --Lj'^* v--> Lj'^* L` is the restriction of `v` to `U'`
(given through an equation `hw` to allow any presentation of it). -/
lemma map_counit_comp_eq_openSquareExchange_hom_comp (sq : IsPullback gU j' j g)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {L : Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (v : (boundedConstructibleUpperStar _ ℓ g).obj K ⟶ L)
    (w : (boundedConstructibleUpperStar _ ℓ gU).obj
        ((boundedConstructibleUpperStar _ ℓ j).obj K) ⟶
      (boundedConstructibleUpperStar _ ℓ j').obj L)
    (hw : w = (boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq.flip).hom.app K ≫
      (boundedConstructibleUpperStar _ ℓ j').map v) :
    (boundedConstructibleUpperStar _ ℓ g).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app K) ≫
      v =
    (openSquareExchange ℓ sq).hom.app _ ≫
      (boundedConstructibleOpenImmersionLowerShriek _ ℓ j').map w ≫
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j').counit.app L := by
  rw [← cancel_epi ((openSquareExchange ℓ sq).inv.app _), Iso.inv_hom_id_app_assoc]
  refine Eq.trans ?_
    ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j').homEquiv_counit
      (g := w))
  refine Equiv.eq_symm_apply _ |>.2 ?_
  refine ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j').homEquiv_unit
    _ _ _).trans ?_
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, unit_comp_map_openSquareExchange_inv, hw, Category.assoc, Category.assoc]
  exact Adjunction.map_unit_comp_app_comp_map_map_counit_assoc
    (H := boundedConstructibleUpperStar _ ℓ gU)
    (H' := boundedConstructibleUpperStar _ ℓ g) (jU' := boundedConstructibleUpperStar _ ℓ j')
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq.flip).hom K _

end General

/-! ### The graph version -/

section Graph

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace Correspondence

variable (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) {h : X ⟶ X}
  (v : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj K ⟶ K)
  {x : RationalPoint X} (hx : x ≫ h = x)

/-- **The open piece coefficient and the counit** (blueprint
`proposition-additivity-trace-classes--2`, proof of item 2, step (a)): `ε ∘ u^U = v ∘ Lh^* ε` for
the counit `ε : j_! Lj^* K ⟶ K` of the open complement `j : X ∖ {x} ⟶ X` of a rational point fixed
by `h`. -/
@[reassoc]
theorem graphOpenPieceCoeff_comp_counit :
    graphOpenPieceCoeff K v hx ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
          (pointComplι x)).counit.app K =
      (boundedConstructibleUpperStar _ ℓ h).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ
            (pointComplι x)).counit.app K) ≫ v := by
  rw [map_counit_comp_eq_openSquareExchange_hom_comp ℓ
      (isPullback_preimagePointComplRestrict_of_comp_eq hx) K v _ rfl,
    graphOpenPieceCoeff, Category.assoc, Category.assoc]
  congr 1
  have e : graphOpenRestriction K v hx =
      ((boundedConstructiblePullbackSquareComparison _ ℓ
          (isPullback_preimagePointComplRestrict_of_comp_eq hx).toCommSq.flip).hom.app K ≫
        (boundedConstructibleUpperStar _ ℓ (pointComplPreimageι hx ≫ pointComplι x)).map v) ≫
      (boundedConstructibleUpperStarComp _ ℓ (pointComplPreimageι hx) (pointComplι x)).hom.app
        K := by
    rw [graphOpenRestriction, boundedConstructiblePullbackSquareComparison_hom_app]
    simp only [Category.assoc]
  rw [e]
  exact Adjunction.conjugateIsoEquiv_symm_inv_app_comp_map_homEquiv_symm_comp_counit _ _ _
    (boundedConstructibleUpperStarComp _ ℓ (pointComplPreimageι hx) (pointComplι x)) _

end Correspondence

end Graph

/-! ### The Frobenius version -/

section Frobenius

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left]

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)

/-- **The open piece coefficient and the counit** (blueprint
`proposition-additivity-trace-classes--2`, proof of item 2, step (a)): `ε ∘ u^U = φ_m ∘ LΦ_m^* ε`
for the counit `ε : j_! Lj^* K ⟶ K` of an open immersion `j` and a cartesian square
`Φ_{m,U} ≫ j = j ≫ Φ_m`. -/
@[reassoc]
theorem openPieceCoeff_comp_counit (m : ℕ) {ΦU : U ⟶ U}
    (sq : IsPullback ΦU j j (frobeniusIterate Φ m)) :
    K.openPieceCoeff j m sq ≫
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app
          K.carrier =
      (boundedConstructibleUpperStar _ ℓ (frobeniusIterate Φ m)).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).counit.app
            K.carrier) ≫ (K.iterateStr m).hom := by
  rw [openPieceCoeff, Category.assoc]
  refine (map_counit_comp_eq_openSquareExchange_hom_comp ℓ sq K.carrier _ _ ?_).symm
  rw [boundedConstructiblePullbackSquareComparison_hom_app, Category.assoc, Category.assoc]

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
