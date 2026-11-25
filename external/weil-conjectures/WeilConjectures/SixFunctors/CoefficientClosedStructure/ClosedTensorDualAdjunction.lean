/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.HomCongr

/-! # Tensor transposition and contravariant dual adjunction

Source: the tensor-Hom arrows in the current blueprint's closed-costalk-duality proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory Opposite MonoidalCategory BraidedCategory
namespace WeilConjectures.CoefficientClosedStructure

variable {C : Type u} [Category.{v} C] {H : Cᵒᵖ × C ⥤ C}
  (S : CoefficientClosedStructure H)

/-- Fixing the target of internal Hom gives the usual contravariant dual functor.
Source: Stacks 08J9, functoriality of derived internal Hom. -/
def dual (H : Cᵒᵖ × C ⥤ C) (M : C) : Cᵒᵖ ⥤ C :=
  ((𝟭 Cᵒᵖ).prod' ((Functor.const Cᵒᵖ).obj M)) ⋙ H

end WeilConjectures.CoefficientClosedStructure

namespace CategoryTheory
open Limits
universe a b a' b' a'' b''
private theorem supportedUnit
    {C : Type a} [Category.{b} C] [HasZeroMorphisms C]
    {D : Type a'} [Category.{b'} D]
    {E : Type a''} [Category.{b''} E] [HasZeroMorphisms E]
    (p : C ⥤ D) (q : D ⥤ C) (r : C ⥤ E) (adj : p ⊣ q)
    [IsIso adj.counit]
    (detect : ∀ {X Y : C} (f : X ⟶ Y),
      IsIso (p.map f) → IsIso (r.map f) → IsIso f)
    (zero : ∀ N : D, IsZero (r.obj (q.obj N)))
    (X : C) (hX : IsZero (r.obj X)) : IsIso (adj.unit.app X) := by
  apply detect
  · have : IsIso (p.map (adj.unit.app X) ≫ adj.counit.app (p.obj X)) := by
      rw [adj.left_triangle_components X]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (p.obj X))
  · exact ⟨⟨0, hX.eq_of_src _ _, (zero _).eq_of_src _ _⟩⟩

private theorem projectionOfSupportedUnit
    {C : Type a} [Category.{b} C] {D : Type a'} [Category.{b'} D]
    (p : C ⥤ D) (q : D ⥤ C) (adj : p ⊣ q) [IsIso adj.counit]
    (tc : C × C ⥤ C) (td : D × D ⥤ D)
    (e : tc ⋙ p ≅ p.prod p ⋙ td)
    (hu : ∀ N K, IsIso (adj.unit.app (tc.obj (q.obj N, K)))) :
    Nonempty (q.prod (𝟭 C) ⋙ tc ≅ (𝟭 D).prod p ⋙ td ⋙ q) := by
  let f := q.prod (𝟭 C)
  let eta := Functor.whiskerLeft (f ⋙ tc) adj.unit
  have : IsIso eta := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact hu X.1 X.2
  let b : f ⋙ p.prod p ≅ (𝟭 D).prod p :=
    NatIso.prod (asIso adj.counit) (Iso.refl p)
  exact ⟨asIso eta ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft f e) q ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight b td) q⟩

end CategoryTheory
