/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-! # The inverse mate and the explicit left exchange -/

@[expose] public section

namespace CategoryTheory.Adjunction

/-- Normalize the two presentations before substituting geometric adjunctions. -/
lemma inverseMate_natTrans_eq_exchangeLeft
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (a : L ⊣ R) (a' : L' ⊣ R') {P : A ⥤ A'} {Q : B ⥤ B'}
    (θ : R ⋙ P ≅ Q ⋙ R') :
    ((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ θ.hom)) =
      exchangeLeft a a' θ := by
  ext K
  simp [mateEquiv_symm_apply, exchangeLeft_app]

end CategoryTheory.Adjunction
