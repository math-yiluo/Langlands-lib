/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DefectLocal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!

# Generic points of the centre under a quasi-finite morphism

Let `f : X' ⟶ X` be a locally quasi-finite morphism, `Z = V(I) ⊆ X` and `Z' = V(f^* I)`. A point
`ζ'` of `Z'` lying over a generic point `ζ` of an irreducible component of `Z` is itself a
generic point of an irreducible component of `Z'`
(`ProEtale.CondensedRing.closure_singleton_mem_irreducibleComponents_of_centreMap`): a
generization `ξ` of `ζ'` in `Z'` maps to a generization of `ζ` in `Z`, which is `ζ`, so `ξ = ζ'`
since the fibres of `f` are discrete.

-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  [LocallyQuasiFinite f.left] (I : X.left.IdealSheafData)

/-- The restriction of a locally quasi-finite morphism to the centres is locally quasi-finite. -/
lemma locallyQuasiFinite_centreMap : LocallyQuasiFinite (centreMap f I).left :=
  MorphismProperty.of_isPullback (isPullback_centreMap f I).flip ‹_›

attribute [local instance] locallyQuasiFinite_centreMap

/-- **Points over a generic point of the centre are generic** (`f` locally quasi-finite): if
`ζ'` lies over a point `ζ` whose closure is an irreducible component of `Z = V(I)`, then the
closure of `ζ'` is an irreducible component of `Z' = V(f^* I)`. -/
theorem closure_singleton_mem_irreducibleComponents_of_centreMap
    {ζ' : (centre X' (I.comap f.left)).left} {ζ : (centre X I).left}
    (hζ' : (centreMap f I).left ζ' = ζ)
    (hζ : closure {ζ} ∈ irreducibleComponents (centre X I).left) :
    closure {ζ'} ∈ irreducibleComponents (centre X' (I.comap f.left)).left := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hle ↦ ?_⟩
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hT.closure isClosed_closure
  have hξζ' : ξ ⤳ ζ' := by
    rw [specializes_iff_mem_closure, hξ.def]
    exact subset_closure (hle (subset_closure (Set.mem_singleton ζ')))
  have hfξ : (centreMap f I).left ξ ⤳ ζ := hζ' ▸ hξζ'.map (centreMap f I).left.continuous
  have hle' := hζ.2 isIrreducible_singleton.closure
    (specializes_iff_closure_subset.1 hfξ)
  have hζξ : ζ ⤳ (centreMap f I).left ξ :=
    specializes_iff_closure_subset.2 hle'
  have heq : (centreMap f I).left ξ = (centreMap f I).left ζ' :=
    (hfξ.antisymm hζξ).eq.trans hζ'.symm
  obtain rfl := (centreMap f I).left.eq_of_specializes_of_apply_eq hξζ' heq
  rw [hξ.def]
  exact subset_closure

end AlgebraicGeometry.ProEtale.CondensedRing
