/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.LocallyConstantMapsPresheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section
set_option autoImplicit false
universe w z
open CategoryTheory Opposite TopologicalSpace
namespace TopCat

/-- Compatible locally constant maps on an open cover admit a locally constant gluing.
The proof defines the glued function pointwise and checks local constancy on a member of
 the cover containing each point.
(blueprint: lem-weil-pbc-locally-constant-maps-gluing-exists) -/
theorem locallyConstantMaps_gluing_exists (X : TopCat.{w}) (R : Type z) :
    ∀ {ι : Type w} (U : ι → Opens X)
      (sf : ∀ i, ToType ((locallyConstantMapsPresheaf X R).obj (op (U i)))),
      Presheaf.IsCompatible (locallyConstantMapsPresheaf X R) U sf →
      ∃ s : ToType ((locallyConstantMapsPresheaf X R).obj (op (iSup U))),
        Presheaf.IsGluing (locallyConstantMapsPresheaf X R) U sf s := by
  classical
  intro ι U sf hsf
  change ∀ i, LocallyConstant (U i) R at sf
  choose index index_spec using fun x : ↑(iSup U) ↦ Opens.mem_iSup.mp x.2
  let f : ↑(iSup U) → R := fun x ↦ sf (index x) ⟨x.1, index_spec x⟩
  have hf (i : ι) (x : U i) :
      f ⟨x.1, (le_iSup U i) x.2⟩ = sf i x := by
    exact LocallyConstant.congr_fun (hsf (index ⟨x.1, (le_iSup U i) x.2⟩) i)
      ⟨x.1, index_spec ⟨x.1, (le_iSup U i) x.2⟩, x.2⟩
  have hlocal : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).2
    intro x
    let i := index x
    let xi : U i := ⟨x.1, index_spec x⟩
    obtain ⟨V, hV, hxV, hconst⟩ := (sf i).isLocallyConstant.exists_open xi
    let inc : U i → ↑(iSup U) := Set.inclusion (le_iSup U i)
    refine ⟨inc '' V, (U i).isOpen.isOpenMap_inclusion (le_iSup U i) V hV,
      ⟨xi, hxV, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact (hf i z).trans ((hconst z hz).trans (hf i xi).symm)
  refine ⟨⟨f, hlocal⟩, ?_⟩
  intro i
  apply LocallyConstant.ext
  exact hf i

end TopCat
