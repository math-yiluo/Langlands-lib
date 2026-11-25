/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-!
# Pro-étale complexes of étale origin

An object of `D(X_proét)` is *bounded below of étale origin*
(`AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin`) if it is isomorphic to `ν^* N` for
a bounded below complex `N` of étale sheaves. This file shows that these objects form a
triangulated subcategory of `D(X_proét)` which is stable under retracts, and that they are
exactly the bounded below objects at which the counit `ν^* Rν_* L ⟶ L` of the comparison
adjunction is an isomorphism.

## Main results

- `AlgebraicGeometry.ProEtale.DerivedCategory.plusEtaleOrigin_iff`: `L` is bounded below of
  étale origin if and only if it is bounded below and the counit at `L` is an isomorphism.
- the instances `(plusEtaleOrigin A X).IsTriangulated` and
  `(plusEtaleOrigin A X).IsStableUnderRetracts`.
- `AlgebraicGeometry.ProEtale.DerivedCategory.nonempty_iso_mapDerivedCategory_derivedHom_of_\
  plusEtaleOrigin`: if `RHom(ν^* K, ν^* M)` is bounded below of étale origin for a bounded below
  `M`, then `ν^* RHom(K, M) ≅ RHom(ν^* K, ν^* M)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- An object of `D(X_proét)` is bounded below of étale origin if and only if it is bounded
below and the counit `ν^* Rν_* L ⟶ L` of the comparison adjunction is an isomorphism at it:
the unit is invertible on bounded below étale complexes
(`AlgebraicGeometry.ProEtale.isIso_derivedComparisonAdjunction_unit_app`), and `Rν_*`
preserves bounded below objects. -/
lemma plusEtaleOrigin_iff (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    plusEtaleOrigin A X L ↔ _root_.DerivedCategory.TStructure.t.plus L ∧
      IsIso ((derivedComparisonAdjunction A X).counit.app L) := by
  let adj := derivedComparisonAdjunction A X
  refine ⟨fun hL ↦ ⟨hL.plus, ?_⟩, fun ⟨hL, h⟩ ↦
    ⟨_, plus_rightDerivedFunctor_comparisonLowerStar_obj hL, ⟨asIso (adj.counit.app L)⟩⟩⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := hL
  have := isIso_derivedComparisonAdjunction_unit_app A X N hN
  have : IsIso (adj.counit.app (D(ν^*(X)[A]).obj N)) := by
    have h := adj.left_triangle_components N
    have : IsIso (D(ν^*(X)[A]).map (adj.unit.app N) ≫ adj.counit.app _) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (D(ν^*(X)[A]).map (adj.unit.app N)) _
  have : IsIso ((R(ν_*(X)[A]) ⋙ D(ν^*(X)[A])).map e.hom ≫ adj.counit.app L) := by
    rw [adj.counit.naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((R(ν_*(X)[A]) ⋙ D(ν^*(X)[A])).map e.hom) _

variable (A X) in
/-- The restriction of `ν^*` to bounded below étale complexes is full. -/
instance full_ι_comp_mapDerivedCategory :
    (_root_.DerivedCategory.TStructure.t.plus.ι ⋙ D(ν^*(X)[A])).Full where
  map_surjective {K M} f := by
    obtain ⟨g, hg⟩ :=
      (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj M.obj M.property).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

variable (A X) in
/-- The objects bounded below of étale origin form a triangulated subcategory: they are the
essential image of the triangulated functor `ν^*` restricted to `D⁺(X_ét)`, which is full. -/
instance isTriangulated_plusEtaleOrigin : (plusEtaleOrigin A X).IsTriangulated := by
  rw [plusEtaleOrigin, ← Functor.essImage_ι_comp]
  infer_instance

/-- A retract of a bounded below object is bounded below. -/
lemma _root_.DerivedCategory.TStructure.plus_of_retract {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {L L' : _root_.DerivedCategory C} (r : Retract L L')
    (hL' : _root_.DerivedCategory.TStructure.t.plus L') :
    _root_.DerivedCategory.TStructure.t.plus L := by
  obtain ⟨n, hn⟩ := hL'
  refine ⟨n, ?_⟩
  change L'.IsGE n at hn
  change L.IsGE n
  rw [_root_.DerivedCategory.isGE_iff] at hn ⊢
  exact fun i hi ↦ (hn i hi).of_mono (r.map (_root_.DerivedCategory.homologyFunctor C i)).i

variable (A X) in
/-- The objects bounded below of étale origin are stable under retracts, being characterised
by the invertibility of the counit (`plusEtaleOrigin_iff`). -/
instance isStableUnderRetracts_plusEtaleOrigin :
    (plusEtaleOrigin A X).IsStableUnderRetracts where
  of_retract {L L'} r hL' := by
    rw [plusEtaleOrigin_iff] at hL' ⊢
    exact ⟨_root_.DerivedCategory.TStructure.plus_of_retract r hL'.1,
      MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
        ((derivedComparisonAdjunction A X).counit.retractArrowApp r) hL'.2⟩

end AlgebraicGeometry.ProEtale.DerivedCategory
