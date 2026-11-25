/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Inverse scalar and geometric mates -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures.ExceptionalIntegralScalar

/-- Invert a scalar comparison before geometric transposition, or invert its
geometric mate before scalar transposition: the two arrows agree.
Source: Stacks Tag 0E46 and the composition law for mates.
(blueprint: lem-sf-inverse-mate-interchange).

Proof: the two successive mates of the original scalar comparison are its
conjugate under the composite adjunctions. Thus the given direct-image comparison
is this conjugate. Conjugation sends inverse isomorphisms to inverse isomorphisms.
The two successive mates of the inverse comparison are consequently the inverse
direct-image comparison. Cancel the scalar mates equivalence. -/
theorem inverseMateInterchange
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {SX : B ⥤ D} {UX : D ⥤ B} {SY : A ⥤ C} {UY : C ⥤ A}
    {PA : A ⥤ B} {RA : B ⥤ A} {PB : C ⥤ D} {RB : D ⥤ C}
    (ax : SX ⊣ UX) (ay : SY ⊣ UY) (ar : PA ⊣ RA) (az : PB ⊣ RB)
    (δ : UY ⋙ PA ≅ PB ⋙ UX) (β : PA ⋙ SX ≅ SY ⋙ PB)
    (d : RB ⋙ UY ≅ UX ⋙ RA)
    (hβ : (mateEquiv ay ax (TwoSquare.mk _ _ _ _ β.hom)) = δ.hom)
    (hd : (mateEquiv az ar (TwoSquare.mk _ _ _ _ δ.hom)) = d.hom) :
    ((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _ d.inv)) =
      (mateEquiv ar az (TwoSquare.mk _ _ _ _ β.inv)) := by
  have hβ' : mateEquiv ay ax (TwoSquare.mk _ _ _ _ β.hom) =
      TwoSquare.mk _ _ _ _ δ.hom := by
    ext K
    exact congr_app hβ K
  have he : conjugateIsoEquiv (ay.comp az) (ar.comp ax) β = d := by
    apply Iso.ext
    change conjugateEquiv (ay.comp az) (ar.comp ax) β.hom = d.hom
    rw [← iterated_mateEquiv_conjugateEquiv ay ax ar az
      (TwoSquare.mk _ _ _ _ β.hom), hβ']
    exact hd
  have hinv : conjugateEquiv (ar.comp ax) (ay.comp az) β.inv = d.inv := by
    change (conjugateIsoEquiv (ar.comp ax) (ay.comp az) β.symm).hom = d.inv
    rw [conjugateIsoEquiv_iso_symm, he]
    rfl
  have hq : mateEquiv ax ay (mateEquiv ar az (TwoSquare.mk _ _ _ _ β.inv)) =
      TwoSquare.mk _ _ _ _ d.inv := by
    ext K
    exact congr_app ((iterated_mateEquiv_conjugateEquiv ar az ay ax
      (TwoSquare.mk _ _ _ _ β.inv)).trans hinv) K
  exact ((mateEquiv ax ay).symm_apply_eq.mpr hq.symm)

end WeilConjectures.ExceptionalIntegralScalar
