/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.Topology.LocallyConstantMapsPresheaf

/-!
# Sections of colimits of sheaves

- `TopCat.Sheaf.colimitSectionsMap`: for a diagram `D` of sheaves with a colimit and an open `U`,
  the canonical map `colim_i D_i(U) → (colim D)(U)` (Stacks 009F).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat

variable {X : TopCat.{u}} {C : Type*} [Category C]

/-- The canonical map `colim_i D_i(U) → (colim D)(U)` for a diagram of sheaves `D` and an open
`U`; its composite with the `i`-th coprojection is the component at `U` of the coprojection
`D_i → colim D`. (blueprint: `aux-directed-colimit-map`) -/
noncomputable def Sheaf.colimitSectionsMap {J : Type*} [Category J] (D : J ⥤ X.Sheaf C)
    [HasColimit D] (U : (Opens X)ᵒᵖ)
    [HasColimit (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U)] :
    colimit (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U) ⟶ (colimit D).obj.obj U :=
  colimit.post D (sheafToPresheaf _ C ⋙ (evaluation _ C).obj U)

@[reassoc (attr := simp)]
lemma Sheaf.ι_colimitSectionsMap {J : Type*} [Category J] (D : J ⥤ X.Sheaf C)
    [HasColimit D] (U : (Opens X)ᵒᵖ)
    [HasColimit (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U)] (j : J) :
    colimit.ι (D ⋙ sheafToPresheaf _ C ⋙ (evaluation _ C).obj U) j ≫
      Sheaf.colimitSectionsMap D U = (colimit.ι D j).hom.app U :=
  colimit.ι_post _ _ _

end TopCat
