/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Isomorphisms of sheaf modules are local on an open cover

Source: Stacks Project, Sheaves, Section 00AK, Lemma 04TN
(blueprint: lem-weil-pbc-sheaf-isomorphism-local-open-cover).
-/

@[expose] public section

universe u₂ v₂ w₂

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- A morphism of modules on a ringed space is an isomorphism exactly when its
restriction to every member of an open cover is an isomorphism.

Source: Stacks Project, Sheaves, Section 00AK, Lemma 04TN
(blueprint: lem-weil-pbc-sheaf-isomorphism-local-open-cover).
Proof:
1. Restriction is a functor, so it preserves isomorphisms.
2. Forget to sheaves of abelian groups. This functor reflects isomorphisms.
3. The equality `hcover` gives `CoversTop U` for the open-set Grothendieck topology.
4. Underlying abelian sheaves commute definitionally with restriction to `Over (U i)`.
   Thus each local module isomorphism gives a local abelian sheaf isomorphism.
5. Apply Mathlib's `Sheaf.isIso_of_coversTop` and reflect the resulting isomorphism.
-/
theorem sheaf_module_isIso_iff_isIso_over_open_cover
    (X : RingedSpace.{u₂}) (I : Type w₂) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (M N : SheafOfModules.{max u₂ v₂} (moduleRings X))
    (α : M ⟶ N) :
    IsIso α ↔ ∀ i : I, IsIso (α.over (U i)) := by
  constructor
  · intro h i
    exact (SheafOfModules.overFunctor (moduleRings X) (U i)).map_isIso α
  · intro h
    have : IsIso ((SheafOfModules.toSheaf (moduleRings X)).map α) := by
      apply Sheaf.isIso_of_coversTop ((Opens.coversTop_iff X U).2 hcover)
      intro i
      have := h i
      change IsIso ((SheafOfModules.toSheaf ((moduleRings X).over (U i))).map
        (α.over (U i)))
      infer_instance
    exact isIso_of_reflects_iso α (SheafOfModules.toSheaf (moduleRings X))

end AlgebraicGeometry
