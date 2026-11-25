/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.Topology.LocallyConstantGermEvaluation
import WeilConjectures.Topology.LocallyConstantMapsGluing

/-!
# Local constancy as a local predicate

For a topological space `X` and a type `R`, being locally constant is a local predicate on maps
`U → R` defined on open subsets `U` of `X`.

## Main definitions

- `TopCat.isLocallyConstantLocal`: the local predicate "is locally constant".

Evaluation of germs of locally constant maps and gluing of locally constant maps are
`TopCat.existsUnique_locallyConstant_germ_evaluation` and
`TopCat.locallyConstantMaps_gluing_exists`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat

variable (X : TopCat.{u}) (R : Type u)

/-- Being locally constant is a local predicate on maps from open subsets of `X` to `R`. -/
def isLocallyConstantLocal : LocalPredicate fun _ : X ↦ R where
  pred {_} f := IsLocallyConstant f
  res {_ _} i _ h := h.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f w := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨V, hxV, i, hV⟩ := w x
    have he := Opens.isOpenEmbedding_of_le i.le
    have h := (IsLocallyConstant.iff_eventually_eq _).1 hV ⟨x.1, hxV⟩
    have hm := he.map_nhds_eq ⟨x.1, hxV⟩
    have hi : Set.inclusion i.le ⟨x.1, hxV⟩ = x := rfl
    rw [hi] at hm
    rw [← hm]
    exact Filter.eventually_map.2 h

end TopCat
