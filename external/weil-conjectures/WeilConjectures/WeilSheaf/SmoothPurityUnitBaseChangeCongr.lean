/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Basic

/-! # Congruence for unit base change with its invertibility witness -/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} {bc bc' : a ⋙ H ⟶ G ⋙ b} [IsIso bc] [IsIso bc']
  {U : D} {U' : D'}

/-- Equality of the left exchange identifies unit base changes, including the
proofs of invertibility required by the definition. -/
lemma unitBaseChange_congr (h : bc = bc') (e : H.obj U ⟶ U') :
    unitBaseChange adj adj' bc e = unitBaseChange adj adj' bc' e := by
  subst bc'
  rfl

end CategoryTheory.Adjunction
