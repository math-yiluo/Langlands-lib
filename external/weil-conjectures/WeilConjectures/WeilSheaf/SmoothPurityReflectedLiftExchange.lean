/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange

/-! # Reflection of a square whose four functors are restrictions -/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {PA : ObjectProperty A} {PB : ObjectProperty B}
  {PA' : ObjectProperty A'} {PB' : ObjectProperty B'}
  {F : A ⥤ B} {F' : A' ⥤ B'} {T : A ⥤ A'} {T' : B ⥤ B'}
  (hF : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ F).obj K))
  (hF' : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ F').obj K))
  (hT : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ T).obj K))
  (hT' : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ T').obj K))
  (e : F ⋙ T' ≅ T ⋙ F')

/-- The reflected square agrees with the componentwise restriction. -/
lemma preimageIso_liftSquareWithComparisons_lift_hom :
    (preimageIso_liftSquareWithComparisons
      (PB.liftCompιIso (PA.ι ⋙ F) hF)
      (PB'.liftCompιIso (PA'.ι ⋙ F') hF') hT hT' e).hom =
      AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.liftExchange
        e.hom hF hF' hT' hT := by
  apply NatTrans.ext
  funext K
  apply PB'.ι.map_injective
  simp [preimageIso_liftSquareWithComparisons_hom_app_hom, liftCompιIso]

end CategoryTheory.ObjectProperty
