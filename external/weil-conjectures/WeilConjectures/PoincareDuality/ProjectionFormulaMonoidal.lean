/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.FullSubcategoryUnitor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.PoincareDuality.ProjectionFormulaMonoidalOfCompactification

/-!

# The exceptional projection morphism is a module structure

The exceptional projection morphism `PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` on bounded
constructible complexes (`ProEtale.CondensedRing.boundedConstructibleExceptionalProjection`) is
compatible with the unit and the tensor structure of `Lf^*` in its second variable (the axioms of
a module functor), in exactly the form of the hypotheses `hunit` and `hassoc` of
`CategoryTheory.Adjunction.isIso_exceptionalTensorMap`.

These are the images under the faithful inclusion of the statements on the unbounded derived
categories (`WeilConjectures.PoincareDuality.ProjectionFormulaMonoidalOfCompactification`), proved
for an arbitrary compactification and specialised to `compactificationOverField f`.

## Main statements

- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection_unit`,
  `ProEtale.CondensedRing.boundedConstructibleExceptionalProjection_tensor`.

## Implementation notes

The underlying morphisms are first rewritten into the ambient derived categories with the
`rfl`-lemmas `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification_map_hom`
and the like, so that the ambient statement applies syntactically. The lemmas for `Rf_!^c` and the
comparison maps of `Lf^*` are used with `rw`, not `dsimp`: left to definitional unfolding, these
identifications made the kernel unfold the derived functors (minutes of kernel time and over 5 GB
of memory).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The module axioms on bounded constructible complexes -/

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- `Rf_!^c` on bounded constructible complexes is `Rf_!(c)` on underlying morphisms. -/
lemma boundedConstructibleLowerShriekOfCompactification_map_hom (c : Compactification f.left)
    {K K' : Dᵇc(X.left)⟦𝐐⟧} (φ : K ⟶ K') :
    ((boundedConstructibleLowerShriekOfCompactification ℓ c).map φ).hom =
      (Rf_!(c)⟦𝐐⟧).map φ.hom :=
  rfl

/-- The unit of the derived pullback on bounded constructible complexes is that of `Lf^*` on
underlying objects. -/
lemma boundedConstructibleUpperStar_ε_hom :
    (ε (boundedConstructibleUpperStar 𝐐 ℓ f)).hom = ε L((f.left)^*⟦𝐐⟧) :=
  rfl

/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is unital. -/
lemma boundedConstructibleExceptionalProjectionMorphismOfCompactification_unit
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ 𝟙_ _)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj (𝟙_ _)))
        (exceptionalProjectionMorphismOfCompactification 𝐐 c K.obj (𝟙_ _)) =
      (ρ_ _).hom ≫ (boundedConstructibleLowerShriekOfCompactification ℓ c).map
        ((ρ_ K).inv ≫ K ◁ ε (boundedConstructibleUpperStar 𝐐 ℓ f)) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.rightUnitor_hom_hom]
  rw [boundedConstructibleLowerShriekOfCompactification_map_hom ℓ f c]
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.whiskerLeft_hom,
    ObjectProperty.rightUnitor_inv_hom]
  rw [boundedConstructibleUpperStar_ε_hom]
  exact exceptionalProjectionMorphismOfCompactification_unit 𝐐 c K.obj

/-- `Rf_!^c` on bounded constructible complexes is `Rf_!(c)` on underlying objects. -/
lemma boundedConstructibleLowerShriekOfCompactification_obj_obj (c : Compactification f.left)
    (K : Dᵇc(X.left)⟦𝐐⟧) :
    ((boundedConstructibleLowerShriekOfCompactification ℓ c).obj K).obj =
      (Rf_!(c)⟦𝐐⟧).obj K.obj :=
  rfl

/-- The multiplication of the derived pullback on bounded constructible complexes is that of
`Lf^*` on underlying objects. -/
lemma boundedConstructibleUpperStar_μ_hom (B C : Dᵇc(Y.left)⟦𝐐⟧) :
    (μ (boundedConstructibleUpperStar 𝐐 ℓ f) B C).hom = μ L((f.left)^*⟦𝐐⟧) B.obj C.obj :=
  rfl

/-- The exceptional projection morphism of a compactification `c`, restricted to bounded
constructible complexes, is associative. -/
lemma boundedConstructibleExceptionalProjectionMorphismOfCompactification_tensor
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦𝐐⟧) (B C : Dᵇc(Y.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ (B ⊗ C))
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj (B ⊗ C)))
        (exceptionalProjectionMorphismOfCompactification 𝐐 c K.obj (B ⊗ C).obj) =
      (α_ _ _ _).inv ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj B))
          (exceptionalProjectionMorphismOfCompactification 𝐐 c K.obj B.obj) ▷ C ≫
        ObjectProperty.homMk
          (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            (K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj B) ⊗ C)
          (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
            ((K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj B) ⊗
              (boundedConstructibleUpperStar 𝐐 ℓ f).obj C))
          (exceptionalProjectionMorphismOfCompactification 𝐐 c
            (K ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj B).obj C.obj) ≫
        (boundedConstructibleLowerShriekOfCompactification ℓ c).map
          ((α_ _ _ _).hom ≫ K ◁ μ (boundedConstructibleUpperStar 𝐐 ℓ f) B C) := by
  refine ObjectProperty.hom_ext (P := boundedConstructible _) ?_
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.whiskerRight_hom, ObjectProperty.associator_inv_hom]
  rw [boundedConstructibleLowerShriekOfCompactification_map_hom ℓ f c]
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.whiskerLeft_hom,
    ObjectProperty.associator_hom_hom]
  rw [boundedConstructibleUpperStar_μ_hom]
  exact exceptionalProjectionMorphismOfCompactification_tensor 𝐐 c K.obj B.obj C.obj

/-- **Unitality of the exceptional projection morphism** on bounded constructible complexes, in
the form of the hypothesis `hunit` of `CategoryTheory.Adjunction.isIso_exceptionalTensorMap`. -/
lemma boundedConstructibleExceptionalProjection_unit (A : Dᵇc(X.left)⟦𝐐⟧) :
    ((boundedConstructibleExceptionalProjection ℓ f).app A).app (𝟙_ _) =
      (ρ_ ((boundedConstructibleLowerShriek ℓ f).obj A)).hom ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((ρ_ A).inv ≫ A ◁ ε (boundedConstructibleUpperStar 𝐐 ℓ f)) :=
  boundedConstructibleExceptionalProjectionMorphismOfCompactification_unit ℓ f
    (compactificationOverField f) A

/-- **Associativity of the exceptional projection morphism** on bounded constructible complexes,
in the form of the hypothesis `hassoc` of `CategoryTheory.Adjunction.isIso_exceptionalTensorMap`.
-/
lemma boundedConstructibleExceptionalProjection_tensor (A : Dᵇc(X.left)⟦𝐐⟧)
    (B C : Dᵇc(Y.left)⟦𝐐⟧) :
    ((boundedConstructibleExceptionalProjection ℓ f).app A).app (B ⊗ C) =
      (α_ _ _ _).inv ≫ (((boundedConstructibleExceptionalProjection ℓ f).app A).app B ▷ C) ≫
        ((boundedConstructibleExceptionalProjection ℓ f).app
          (A ⊗ (boundedConstructibleUpperStar 𝐐 ℓ f).obj B)).app C ≫
        (boundedConstructibleLowerShriek ℓ f).map
          ((α_ _ _ _).hom ≫ A ◁ μ (boundedConstructibleUpperStar 𝐐 ℓ f) B C) :=
  boundedConstructibleExceptionalProjectionMorphismOfCompactification_tensor ℓ f
    (compactificationOverField f) A B C

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
