/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.LimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import WeilConjectures.AlgebraicGeometry.DescendSurjective
public import Mathlib.CategoryTheory.Presentable.Directed
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! Declarations of ours that lived in the upstream file
`WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts` (moved out by the scheduled sync,
tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

@[expose] public section

-- This module preserves private proof helpers extracted from the upstream module.
set_option linter.privateModule false
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def degree {r : ℕ} (n : Fin (r + 1)) : (SimplexCategory.Truncated r)ᵒᵖ :=
  op ⟨SimplexCategory.mk n.val, Nat.le_of_lt_succ n.isLt⟩
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private inductive FiniteSplitIndex (r : ℕ)
  | summand : Fin (r + 1) → FiniteSplitIndex r
  | simplex : (SimplexCategory.Truncated r)ᵒᵖ → FiniteSplitIndex r
namespace FiniteSplitIndex
private def Hom {r : ℕ} : FiniteSplitIndex r → FiniteSplitIndex r → Type
  | .summand n, .summand m => PLift (n = m)
  | .summand n, .simplex Δ => degree n ⟶ Δ
  | .simplex _, .summand _ => PEmpty
  | .simplex Δ, .simplex Γ => Δ ⟶ Γ
private def id {r : ℕ} : (a : FiniteSplitIndex r) → Hom a a
  | .summand _ => ⟨rfl⟩
  | .simplex _ => 𝟙 _
private def comp {r : ℕ} : {a b c : FiniteSplitIndex r} → Hom a b → Hom b c → Hom a c
  | .summand _, .summand _, .summand _, f, g => ⟨f.down.trans g.down⟩
  | .summand _, .summand _, .simplex _, f, g => by obtain ⟨rfl⟩ := f; exact g
  | .summand _, .simplex _, .simplex _, f, g => f ≫ g
  | .simplex _, .simplex _, .simplex _, f, g => f ≫ g
private instance category {r : ℕ} : SmallCategory (FiniteSplitIndex r) where
  Hom := Hom
  id := id
  comp := comp
  id_comp := by
    intro a b f
    cases a <;> cases b <;> simp only [Hom, id, comp, Category.id_comp] at *
    · rfl
    · exact PEmpty.elim f
  comp_id := by
    intro a b f
    cases a <;> cases b <;> simp only [Hom, id, comp, Category.comp_id] at *
    · rfl
    · exact PEmpty.elim f
  assoc := by
    intro a b c d f g h
    cases a <;> cases b <;> cases c <;> cases d <;>
      dsimp only [Hom, comp] at * <;> try contradiction
    all_goals first
      | rfl
      | (obtain ⟨rfl⟩ := f; rfl)
private def inclusion (r : ℕ) : (SimplexCategory.Truncated r)ᵒᵖ ⥤ FiniteSplitIndex r where
  obj := simplex
  map := fun f ↦ f
end FiniteSplitIndex

end AlgebraicGeometry
