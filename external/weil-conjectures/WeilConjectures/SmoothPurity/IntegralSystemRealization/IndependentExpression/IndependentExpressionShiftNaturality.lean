/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.Expression.IntegralExpressionOccurrences

/-! # Shifts of independent expression inputs

Source: blueprint purity transport, Step 2, and the independent input convention
(blueprint: lem-pur-independent-expression-shift-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
attribute [local irreducible] HasDerivedCategory.standard

/-- Shift comparisons for each primitive operation; tensor slots remain separate.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
structure InterpretationShifts {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)]
    [∀ W, HasShift (C W) ℤ] (d : Interpretation C) where
  pull {U V : Scheme.{u}} (f : U ⟶ V) : (d.pull f).CommShift ℤ
  push {U V : Scheme.{u}} (f : U ⟶ V) : (d.push f).CommShift ℤ
  shriek {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] : (d.shriek j).CommShift ℤ
  compactSupport {U V : Scheme.{u}} (f : U ⟶ V) (c : Compactification f) :
    (d.compactSupport f c).CommShift ℤ
  tensorLeft (W : Scheme.{u}) (r : ℤ) :
    tensorShiftFirst (C W) r ⋙ d.tensor W ≅ d.tensor W ⋙ shiftFunctor (C W) r
  tensorRight (W : Scheme.{u}) (r : ℤ) :
    completedTensorShiftSecond (C W) r ⋙ d.tensor W ≅
      d.tensor W ⋙ shiftFunctor (C W) r

/-- Reindex shifts through the actual single-slot context, with the designated
left or right tensor comparison at every tensor vertex.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def Expression.SlotContext.shift {B : Scheme.{u}} {C : Scheme.{u} → Type v}
    [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ] {d : Interpretation C}
    (a : InterpretationShifts d) {A : Over B} (r : ℤ) :
    {W : Over B} → (e : Expression.SlotContext d A W) → (P : C A.left) →
      e.evaluate.obj (P⟦r⟧) ≅ (e.evaluate.obj P)⟦r⟧
  | _, .input, _ => Iso.refl _
  | _, .pull f e, P => (d.pull f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.pull f.left) (self := a.pull f.left) r).app (e.evaluate.obj P)
  | _, .push f _ e, P => (d.push f.left).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.push f.left) (self := a.push f.left) r).app (e.evaluate.obj P)
  | _, .shriek j hj _ e, P =>
    letI := hj
    (d.shriek j.left).mapIso (e.shift a r P) ≪≫
      (Functor.commShiftIso (d.shriek j.left) (self := a.shriek j.left) r).app
        (e.evaluate.obj P)
  | _, .compactSupport f c e, P => (d.compactSupport f.left c).mapIso (e.shift a r P) ≪≫
    (Functor.commShiftIso (d.compactSupport f.left c)
      (self := a.compactSupport f.left c) r).app (e.evaluate.obj P)
  | W, .tensorLeft e N, P =>
    ((Functor.curry.obj (d.tensor W.left)).flip.obj N).mapIso (e.shift a r P) ≪≫
      (a.tensorLeft W.left r).app (e.evaluate.obj P, N)
  | W, .tensorRight M e, P =>
    ((Functor.curry.obj (d.tensor W.left)).obj M).mapIso (e.shift a r P) ≪≫
      (a.tensorRight W.left r).app (M, e.evaluate.obj P)

open Classical in
/-- The actual comparison for a single independently labelled input.
Its endpoint identifications are equalities of explicit evaluations, not chosen isos.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
def IndependentExpression.shift {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {C : Scheme.{u} → Type v} [∀ W, Category.{w} (C W)] [∀ W, HasShift (C W) ℤ]
    (d : Interpretation C) (a : InterpretationShifts d) {W : Over B}
    (e : IndependentExpression B I X W) (K : ∀ i, C (X i).left) (i : I) (r : ℤ) :
    (e.val.evaluate d).obj (Function.update K i ((K i)⟦r⟧)) ≅
      ((e.val.evaluate d).obj K)⟦r⟧ :=
  (eqToIso (e.variableContext_evaluate d K i ((K i)⟦r⟧)).1).symm ≪≫
    (e.variableContext d K i).shift a r (K i) ≪≫
    (shiftFunctor (C W.left) r).mapIso
      (eqToIso (e.variableContext_evaluate d K i (K i)).2)

end WeilConjectures.IntegralSystemRealization
