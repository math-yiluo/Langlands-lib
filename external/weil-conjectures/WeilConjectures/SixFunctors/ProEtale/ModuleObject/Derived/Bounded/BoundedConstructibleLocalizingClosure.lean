/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Idempotents.Basic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete

/-! # The localizing hull of bounded constructible pro-étale module complexes

Source: blueprint `definition-localizing-subcategory`, using the bounded constructible
generators needed for the ell-adic cases of `theorem-exceptional-inverse-image`.
(blueprint: def-sfb-bounded-constructible-localizing-closure)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] (X : Scheme.{u})

/-- The intersection of all replete triangulated subcategories containing the bounded
constructible complexes and closed under coproducts in the ambient derived category.
Coproducts are indexed in the coefficient/sheaf morphism universe `u + 1`.

Source: blueprint `definition-localizing-subcategory` and the ell-adic specialization in
`theorem-exceptional-inverse-image`. No completeness condition is added to the hull.
(blueprint: def-sfb-bounded-constructible-localizing-closure) -/
def boundedConstructibleLocalizingClosure :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  sInf {P | boundedConstructible (condensedRingObj Λ X) ≤ P ∧
    ObjectProperty.IsClosedUnderIsomorphisms P ∧ ObjectProperty.IsTriangulated P ∧
    ∀ I : Type (u + 1), ObjectProperty.IsClosedUnderColimitsOfShape P (Discrete I)}

/-- Every bounded constructible complex belongs to its localizing hull. -/
theorem boundedConstructible_le_localizingClosure :
    boundedConstructible (condensedRingObj Λ X) ≤
      boundedConstructibleLocalizingClosure Λ X := by
  apply le_sInf
  intro P hP
  exact hP.1

/-- The universal property of the intersection defining the localizing hull. -/
theorem boundedConstructibleLocalizingClosure_le
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : boundedConstructible (condensedRingObj Λ X) ≤ P)
    [ObjectProperty.IsClosedUnderIsomorphisms P] [ObjectProperty.IsTriangulated P]
    [∀ I : Type (u + 1), ObjectProperty.IsClosedUnderColimitsOfShape P (Discrete I)] :
    boundedConstructibleLocalizingClosure Λ X ≤ P :=
  sInf_le ⟨hP, inferInstance, inferInstance, fun _ ↦ inferInstance⟩

/-- The localizing hull is replete. -/
instance isClosedUnderIsomorphisms_boundedConstructibleLocalizingClosure :
    (boundedConstructibleLocalizingClosure Λ X).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    unfold boundedConstructibleLocalizingClosure at *
    rw [unary_relation_sInf_iff]
    intro P hP
    let : ObjectProperty.IsClosedUnderIsomorphisms P := hP.2.1
    exact ObjectProperty.prop_of_iso P e ((sInf_le hP) _ hK)

/-- The localizing hull contains zero. -/
instance containsZero_boundedConstructibleLocalizingClosure :
    (boundedConstructibleLocalizingClosure Λ X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    unfold boundedConstructibleLocalizingClosure
    rw [unary_relation_sInf_iff]
    intro P hP
    let : ObjectProperty.IsClosedUnderIsomorphisms P := hP.2.1
    let : ObjectProperty.IsTriangulated P := hP.2.2.1
    exact ObjectProperty.prop_zero P⟩

/-- The localizing hull is closed under integer shifts. -/
instance isStableUnderShift_boundedConstructibleLocalizingClosure :
    (boundedConstructibleLocalizingClosure Λ X).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro K hK
    unfold boundedConstructibleLocalizingClosure at *
    rw [ObjectProperty.prop_shift_iff, unary_relation_sInf_iff]
    intro P hP
    let : ObjectProperty.IsTriangulated P := hP.2.2.1
    exact ObjectProperty.le_shift P n K ((sInf_le hP) K hK)⟩

/-- The intersection defining the localizing hull is triangulated. -/
instance isTriangulated_boundedConstructibleLocalizingClosure :
    (boundedConstructibleLocalizingClosure Λ X).IsTriangulated where
  ext₂' T hT h₁ h₃ := by
    apply ObjectProperty.le_isoClosure
    unfold boundedConstructibleLocalizingClosure at *
    rw [unary_relation_sInf_iff]
    intro P hP
    let : ObjectProperty.IsClosedUnderIsomorphisms P := hP.2.1
    let : ObjectProperty.IsTriangulated P := hP.2.2.1
    exact ObjectProperty.ext_of_isTriangulatedClosed₂ P T hT
      ((sInf_le hP) _ h₁) ((sInf_le hP) _ h₃)

/-- The localizing hull is closed under small coproducts in the ambient category. -/
instance isClosedUnderCoproducts_boundedConstructibleLocalizingClosure (I : Type (u + 1)) :
    (boundedConstructibleLocalizingClosure Λ X).IsClosedUnderColimitsOfShape (Discrete I) where
  colimitsOfShape_le K hK := by
    unfold boundedConstructibleLocalizingClosure at *
    rw [unary_relation_sInf_iff]
    intro P hP
    let : ObjectProperty.IsClosedUnderColimitsOfShape P (Discrete I) := hP.2.2.2 I
    exact ObjectProperty.colimitsOfShape_le P (Discrete I) K
      (ObjectProperty.colimitsOfShape_monotone (Discrete I) (sInf_le hP) _ hK)

/-- Coproducts in the localizing hull are computed in the ambient derived category. -/
noncomputable instance hasCoproducts_boundedConstructibleLocalizingClosure
    [IsCommMonObj Λ] :
    HasCoproducts.{u + 1} (boundedConstructibleLocalizingClosure Λ X).FullSubcategory := by
  let : HasColimitsOfSize.{u + 1, u + 1} (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    IsGrothendieckAbelian.hasColimits _
  let : HasCoproducts.{u + 1} (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    fun I ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  let : HasCoproducts.{u + 1} (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    CategoryTheory.derived_hasCoproducts
  intro I
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (boundedConstructibleLocalizingClosure Λ X)

/-- Countable coproducts split idempotents in the triangulated hull. -/
instance isIdempotentComplete_boundedConstructibleLocalizingClosure
    [IsCommMonObj Λ] :
    IsIdempotentComplete (boundedConstructibleLocalizingClosure Λ X).FullSubcategory :=
  isIdempotentComplete_of_countableCoproducts _

/-- It suffices that coproducts are preserved on the source hull, rather than on all
ambient complexes. This is the form used for adic proper pushforward. -/
theorem boundedConstructibleLocalizingClosure_map_of_preservesOnClosure (Y : Scheme.{u})
    (F : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
        DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      ((boundedConstructibleLocalizingClosure Λ X).ι ⋙ F))
    (hbounded : ∀ K, boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ Y) (F.obj K)) :
    boundedConstructibleLocalizingClosure Λ X ≤
      (boundedConstructibleLocalizingClosure Λ Y).inverseImage F := by
  let P := boundedConstructibleLocalizingClosure Λ X ⊓
    (boundedConstructibleLocalizingClosure Λ Y).inverseImage F
  have hcoprod (I : Type (u + 1)) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    let := hF I
    constructor
    intro K hK
    obtain ⟨h⟩ := hK
    have hsource : boundedConstructibleLocalizingClosure Λ X K :=
      (boundedConstructibleLocalizingClosure Λ X).prop_of_isColimit h.isColimit
        (fun j ↦ (h.prop_diag_obj j).1)
    let A := (boundedConstructibleLocalizingClosure Λ X).lift h.diag
      (fun j ↦ (h.prop_diag_obj j).1)
    let c : Cocone A :=
      { pt := ⟨K, hsource⟩
        ι :=
          { app := fun j ↦ ObjectProperty.homMk (h.ι.app j)
            naturality := fun i j f ↦ by
              apply ObjectProperty.hom_ext
              exact h.ι.naturality f } }
    let : PreservesColimit A ((boundedConstructibleLocalizingClosure Λ X).ι ⋙ F) :=
      (hF I).preservesColimit
    let : ReflectsColimitsOfSize.{u + 1, u + 1}
        (boundedConstructibleLocalizingClosure Λ X).ι :=
      fullyFaithful_reflectsColimits _
    let : ReflectsColimit A (boundedConstructibleLocalizingClosure Λ X).ι :=
      ReflectsColimitsOfShape.reflectsColimit
    have hc : IsColimit c := isColimitOfReflects
      (boundedConstructibleLocalizingClosure Λ X).ι h.isColimit
    refine ⟨hsource, ?_⟩
    exact (boundedConstructibleLocalizingClosure Λ Y).prop_of_isColimit
      (isColimitOfPreserves ((boundedConstructibleLocalizingClosure Λ X).ι ⋙ F) hc)
      (fun j ↦ (h.prop_diag_obj j).2)
  have hle : boundedConstructibleLocalizingClosure Λ X ≤ P := by
    apply boundedConstructibleLocalizingClosure_le
    intro K hK
    exact ⟨boundedConstructible_le_localizingClosure Λ X K hK,
      boundedConstructible_le_localizingClosure Λ Y _ (hbounded K hK)⟩
  exact fun K hK ↦ (hle K hK).2

/-- The inclusion of bounded constructible complexes in their localizing hull. -/
noncomputable def boundedConstructibleToLocalizing :
    (boundedConstructible (condensedRingObj Λ X)).FullSubcategory ⥤
    (boundedConstructibleLocalizingClosure Λ X).FullSubcategory :=
  ObjectProperty.ιOfLE (boundedConstructible_le_localizingClosure Λ X)

end AlgebraicGeometry.ProEtale.CondensedRing
