/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Sober

/-!
# Generic points of the irreducible components

Some basic facts about `genericPoints α`, the set of generic points of the irreducible components
of a topological space `α`: distinct generic points do not lie in each other's closure
(`genericPoints.notMem_closure_of_ne`), any set containing all of them is dense
(`dense_of_genericPoints_subset`), and hence the intersection of a finite family of open sets
each containing all of them is a dense open (`dense_iInf_of_genericPoints_subset`).
-/

@[expose] public section

variable {α : Type*} [TopologicalSpace α]

/-- If `x` and `y` are distinct generic points of irreducible components, then `x` does not lie
in the closure of `y`: otherwise the component of `x` would be contained in the component of
`y`, hence equal to it by maximality. -/
theorem genericPoints.notMem_closure_of_ne [T0Space α] {x y : α} (hx : x ∈ genericPoints α)
    (hy : y ∈ genericPoints α) (hxy : x ≠ y) : x ∉ _root_.closure ({y} : Set α) := by
  intro hmem
  have hle : _root_.closure ({x} : Set α) ⊆ _root_.closure ({y} : Set α) :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
  exact hxy (isGenericPoint_closure.eq (hle.antisymm (hx.2 hy.1 hle)).symm)

/-- The generic points of the irreducible components are dense. -/
theorem dense_genericPoints [QuasiSober α] : Dense (genericPoints α) :=
  dense_iff_closure_eq.mpr genericPoints.closure

/-- A set containing all generic points of the irreducible components is dense. -/
theorem dense_of_genericPoints_subset [QuasiSober α] {s : Set α} (h : genericPoints α ⊆ s) :
    Dense s :=
  dense_genericPoints.mono h

/-- The intersection of a finite family of open sets each of which contains all the generic
points of the irreducible components is dense. -/
theorem dense_iInf_of_genericPoints_subset [QuasiSober α] {ι : Type*} [Finite ι]
    {U : ι → TopologicalSpace.Opens α} (h : ∀ i, genericPoints α ⊆ (U i : Set α)) :
    Dense ((⨅ i, U i : TopologicalSpace.Opens α) : Set α) :=
  dense_of_genericPoints_subset <| by
    rw [TopologicalSpace.Opens.coe_iInf]; exact Set.subset_iInter h

/-- In a quasi-sober `T₀` space, a point is the generic point of an irreducible component if and
only if it has no proper generalization. -/
theorem mem_genericPoints_iff_forall_specializes [QuasiSober α] [T0Space α] {x : α} :
    x ∈ genericPoints α ↔ ∀ y, y ⤳ x → y = x := by
  refine ⟨fun hx y hy ↦ ?_, fun h ↦ ?_⟩
  · have hle : _root_.closure ({x} : Set α) ⊆ _root_.closure {y} :=
      specializes_iff_closure_subset.1 hy
    exact (hy.antisymm (specializes_iff_closure_subset.2
      (hx.2 isIrreducible_singleton.closure hle))).eq
  · have hC := irreducibleComponent_mem_irreducibleComponents x
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hgx := h _ (hg.specializes mem_irreducibleComponent)
    change _root_.closure {x} ∈ irreducibleComponents α
    rw [← hgx, hg.def]
    exact hC

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.Topology.Sober`) -/

-- after `quasiSober_iff`
-- `by copilot`
theorem Homeomorph.quasiSober {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] (f : X ≃ₜ Y) : QuasiSober Y := by
  -- Prove quasi-sobriety of `Y` by producing generic points for irreducible closed sets.
  refine ⟨?_⟩
  intro S hSirr hSclosed
  -- Pull back `S` along the homeomorphism.
  let T : Set X := f.symm '' S
  have hTclosed : IsClosed T := by
    -- `f.symm` is a homeomorphism `Y ≃ₜ X`, so it maps closed sets to closed sets.
    simpa [T] using (Homeomorph.isClosed_image (X := Y) (Y := X) f.symm (s := S)).2 hSclosed
  have hTirr : IsIrreducible T := by
    -- Use `IsIrreducible.image` with `ContinuousOn`.
    -- (`Continuous` implies `ContinuousOn`.)
    simpa [T] using hSirr.image (fun y : Y => f.symm y) (f.symm.continuous.continuousOn)
  -- Get a generic point of `T` in `X`, then transport it to `Y`.
  have hx : IsGenericPoint hTirr.genericPoint T :=
    hTirr.isGenericPoint_genericPoint hTclosed
  -- `hx.image` gives a generic point for `closure (f '' T)`
  have hy : IsGenericPoint (f hTirr.genericPoint) (closure (f '' T)) :=
    hx.image f.continuous
  -- Now show `closure (f '' T) = S`, so `f hTirr.genericPoint` is generic for `S`.
  have hclosure : closure (f '' T) = S := by
    -- First compute `f '' T = S`.
    have himage : f '' T = S := by
      -- `f '' (f.symm '' S) = S` for a homeomorphism.
      ext y
      constructor
      · rintro ⟨x, hxT, rfl⟩
        rcases hxT with ⟨y', hy'S, rfl⟩
        simpa using hy'S
      · intro hyS
        refine ⟨f.symm y, ?_, by simp⟩
        exact ⟨y, hyS, by simp⟩
    -- Since `S` is closed, `closure S = S`.
    simp [himage]
  -- Convert the generic-point target set using `hclosure`.
  have : IsGenericPoint (f hTirr.genericPoint) S := by
    simpa [hclosure] using hy
  exact ⟨f hTirr.genericPoint, this⟩

/-- The product of two quasi-sober spaces is quasi-sober. -/
-- put this at end of the file
instance QuasiSober.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] : QuasiSober (X × Y) := by
  refine ⟨fun {S} hS hSclosed => ?_⟩
  have hX := hS.image Prod.fst continuous_fst.continuousOn
  have hY := hS.image Prod.snd continuous_snd.continuousOn
  have hx₀ := hX.isGenericPoint_genericPoint_closure
  have hy₀ := hY.isGenericPoint_genericPoint_closure
  suffices hmem : (hX.genericPoint, hY.genericPoint) ∈ S by
    refine ⟨_, (closure_minimal (Set.singleton_subset_iff.mpr hmem) hSclosed).antisymm ?_⟩
    rw [← Set.singleton_prod_singleton, closure_prod_eq, hx₀.def, hy₀.def]
    exact fun ⟨a, b⟩ hab => ⟨subset_closure ⟨_, hab, rfl⟩, subset_closure ⟨_, hab, rfl⟩⟩
  by_contra hmem
  obtain ⟨U, V, hU, hV, hx₀U, hy₀V, hUV⟩ :=
    isOpen_prod_iff.mp hSclosed.isOpen_compl _ _ hmem
  have : S ⊆ (Uᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Vᶜ) := fun ⟨a, b⟩ hab => by
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and]
    by_contra h; push Not at h; exact hUV (Set.mk_mem_prod h.1 h.2) hab
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hS.isPreirreducible) _ _
    (hU.isClosed_compl.prod isClosed_univ) (isClosed_univ.prod hV.isClosed_compl) this with h | h
  · have : Prod.fst '' S ⊆ Uᶜ := Set.image_subset_iff.mpr fun p hp => (h hp).1
    exact closure_minimal this hU.isClosed_compl
      (hx₀.def ▸ subset_closure (Set.mem_singleton _)) hx₀U
  · have : Prod.snd '' S ⊆ Vᶜ := Set.image_subset_iff.mpr fun p hp => (h hp).2
    exact closure_minimal this hV.isClosed_compl
      (hy₀.def ▸ subset_closure (Set.mem_singleton _)) hy₀V
