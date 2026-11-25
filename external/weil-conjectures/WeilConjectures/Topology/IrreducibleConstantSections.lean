/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.Topology.ConstantSheafLocallyConstantComparison

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat

/-! # Sections of a constant sheaf on an irreducible space
Source: literature/stacks-project/sheaves.tex, Definition 006W
(blueprint: lem-sc-irreducible-constant-sections) -/

/-- Sections of the constant sheaf on nonempty opens of an irreducible space are canonically
identified with the coefficient group, compatibly with restriction.
Source: literature/stacks-project/sheaves.tex, Definition 006W and Example 0081
(blueprint: lem-sc-irreducible-constant-sections)
Proof:
1. A nonempty open subspace of an irreducible space is irreducible, since two nonempty
   opens in it are nonempty opens of the ambient space and meet.
2. Let `L_A` be the presheaf of locally constant `A`-valued maps. By
   `lem-weil-pbc-locally-constant-maps-sheaf` it is a sheaf. The map from the constant
   presheaf to `L_A` sending an element to the corresponding constant map satisfies the
   universal property of the sheafification in `def-weil-pbc-constant-sheaf`: locally
   constant sections are locally constant on a cover, and compatible images glue uniquely.
   Hence the constant sheaf is canonically identified with `L_A`.
3. By `lem-pc-irreducible-space-connected`, every nonempty open is connected, and by
   `lem-weil-pbc-connected-locally-constant-map`, every locally constant map on it is
   constant. Evaluation therefore gives the displayed identifications with `A`.
4. Restricting a constant map to a smaller nonempty open leaves its value unchanged, so
   the identifications carry restriction to the identity of `A`.
-/
theorem irreducible_constant_sections
    (X : TopCat.{u}) [IrreducibleSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (A : Type v) [AddCommGroup A] :
    ∃ e : ∀ U : Opens X, (U : Set X).Nonempty →
      AddEquiv (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of A)).1.obj (op U)) A,
      ∀ (U V : Opens X) (hVU : V ≤ U) (hV : (V : Set X).Nonempty),
        e V hV ∘ ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.map (homOfLE hVU).op = e U (Set.Nonempty.mono hVU hV) := by
  classical
  obtain ⟨c, hc⟩ := constantSheaf_locallyConstant_comparison X A
  let point (U : Opens X) (hU : (U : Set X).Nonempty) : U := ⟨hU.choose, hU.choose_spec⟩
  have preconnected (U : Opens X) : PreconnectedSpace U := by
    let : PreirreducibleSpace U := U.isOpenEmbedding'.preirreducibleSpace
    infer_instance
  let eval (U : Opens X) (hU : (U : Set X).Nonempty) : LocallyConstant U A ≃+ A :=
    { toFun := fun f ↦ f (point U hU)
      invFun := LocallyConstant.const U
      left_inv := by
        intro f
        let := preconnected U
        exact (f.eq_const (point U hU)).symm
      right_inv := by intro a; rfl
      map_add' := by intro f g; rfl }
  refine ⟨fun U hU ↦ (c U).trans (eval U hU), ?_⟩
  intro U V hVU hV
  funext s
  change c V (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of A)).1.map (homOfLE hVU).op s) (point V hV) =
      c U s (point U (Set.Nonempty.mono hVU hV))
  rw [hc]
  let := preconnected U
  exact (c U s).apply_eq_of_preconnectedSpace _ _

end TopCat
