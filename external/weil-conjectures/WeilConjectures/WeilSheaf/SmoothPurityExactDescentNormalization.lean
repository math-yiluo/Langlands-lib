/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentationPaste

/-! # Forgetting an exactly derived descent square -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

open DerivedPresentation

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B C' D' C D : Type*}
  [Category A] [Category B] [Category C'] [Category D'] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C'] [Abelian D'] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C'] [HasDerivedCategory D'] [HasDerivedCategory C] [HasDerivedCategory D]
  (L : A ⥤ B) (T : A ⥤ C') (S : B ⥤ D') (U : C' ⥤ C) (V : D' ⥤ D)
  (R : C ⥤ D) (RW : C' ⥤ D')
  [L.Additive] [T.Additive] [S.Additive] [U.Additive] [V.Additive]
  [R.Additive] [RW.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits RW] [PreservesFiniteColimits RW]

/-- Exact derivation preserves the normalization of a descent comparison after
forgetting. All composition coordinates are retained explicitly. -/
lemma exactDescentComparison_forget
    (b : T ⋙ RW ≅ L ⋙ S) (c : RW ⋙ V ≅ U ⋙ R)
    (d : L ⋙ (S ⋙ V) ≅ (T ⋙ U) ⋙ R)
    (hd : ∀ M, d.hom.app M = V.map (b.inv.app M) ≫ c.hom.app (T.obj M))
    (K : DerivedCategory A) :
    (mapDerivedCategorySquareIso d).hom.app K =
      (mapDerivedCategoryCompIso S V).inv.app (L.mapDerivedCategory.obj K) ≫
        V.mapDerivedCategory.map ((mapDerivedCategorySquareIso b).inv.app K) ≫
        (mapDerivedCategorySquareIso c).hom.app (T.mapDerivedCategory.obj K) ≫
        R.mapDerivedCategory.map ((mapDerivedCategoryCompIso T U).hom.app K) := by
  have h₁ := (derivedRepresents_mapDerivedCategoryCompIso S V).whiskerLeft (ofMap L)
  have h₂ := h₁.comp (derivedRepresents_associator_inv (ofMap L) (ofMap S) (ofMap V))
  have h₃ := h₂.comp ((derivedRepresents_mapDerivedCategorySquareIso b).inv.whiskerRight
    (ofMap V))
  have h₄ := h₃.comp (derivedRepresents_associator (ofMap T) (ofMap RW) (ofMap V))
  have h₅ := h₄.comp ((derivedRepresents_mapDerivedCategorySquareIso c).whiskerLeft (ofMap T))
  have h₆ := h₅.comp (derivedRepresents_associator_inv (ofMap T) (ofMap U) (ofMap R))
  have h₇ := h₆.comp ((derivedRepresents_mapDerivedCategoryCompIso_inv T U).whiskerRight
    (ofMap R))
  have he := (derivedRepresents_mapDerivedCategorySquareIso d).eq_of_eq h₇ (by
    ext M
    simpa using hd M)
  simpa using NatTrans.congr_app he K

end CategoryTheory.Functor
