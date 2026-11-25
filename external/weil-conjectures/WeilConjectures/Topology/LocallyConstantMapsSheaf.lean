/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.LocallyConstantMapsPresheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.Topology.LocallyConstantMapsGluing
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Locally constant maps form a sheaf

Source: Stacks Project, Sheaves, Example 6.4 and Definition 6.5 (Tag 006W)
(blueprint: lem-weil-pbc-locally-constant-maps-sheaf).
-/

@[expose] public section

set_option autoImplicit false

universe w z

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Locally constant maps into a set satisfy the sheaf condition on opens.

Source: Stacks Project, Sheaves, Example 6.4 and Definition 6.5 (Tag 006W).
(blueprint: lem-weil-pbc-locally-constant-maps-sheaf).
Proof: for a covering of an open by opens, compatible sections glue pointwise.
The glued map is locally constant because each point lies in a covering member,
and uniqueness is pointwise. -/
theorem locallyConstantMapsPresheaf_isSheaf (X : TopCat.{w}) (R : Type z) :
    Presheaf.IsSheaf (locallyConstantMapsPresheaf X R) := by
  apply (Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).2
  intro ι U sf hsf
  obtain ⟨s, hs⟩ := locallyConstantMaps_gluing_exists X R U sf hsf
  refine ⟨s, hs, ?_⟩
  intro t ht
  apply LocallyConstant.ext
  intro x
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp x.2
  have hst := congrArg (fun q : LocallyConstant {x : X // x ∈ U i} R =>
    q.toFun ⟨x.1, hxi⟩) (ht i)
  have hss := congrArg (fun q : LocallyConstant {x : X // x ∈ U i} R =>
    q.toFun ⟨x.1, hxi⟩) (hs i)
  exact (hst.trans hss.symm)

end TopCat
