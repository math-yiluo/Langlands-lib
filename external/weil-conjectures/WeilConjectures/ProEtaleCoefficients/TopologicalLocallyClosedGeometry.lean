/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace

/-! Geometric factorization used by the topological locally closed extension.
The conclusion is the scheme level open--closed factorization; coefficient transport
and module exactness are handled by the parent theorem.
(blueprint: lem-sfb-topological-locally-closed-extension)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-- A topologically Noetherian target turns an immersion into an open--closed factor. -/
theorem exists_open_closed_factorization {T X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (f : T ⟶ X) [IsImmersion f] :
    ∃ (Z : Scheme.{u}) (j : T ⟶ Z) (i : Z ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f := by
  let : TopologicalSpace.NoetherianSpace T := f.isEmbedding.isInducing.noetherianSpace
  let : QuasiCompact f := inferInstance
  exact IsImmersion.isImmersion_iff_exists_of_quasiCompact.mp inferInstance
