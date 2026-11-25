/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Categorical filtrations from invariant flags

Let `M` be a finite-dimensional representation of a group `P` over `ZMod ℓ` and let
`0 = F 0 ⊆ F 1 ⊆ ⋯ ⊆ F n = M` be a full flag of `P`-stable subspaces such that `P` acts trivially
on each `F (i + 1) / F i`. This file provides tools to realise this flag inside `Rep (ZMod ℓ) P`: a
sequence of monomorphisms `W 0 ⟶ W 1 ⟶ ⋯ ⟶ W n` with `W 0 = 0`, `W n ≅ M` and all cokernels
isomorphic to the trivial representation on `ULift (ZMod ℓ)`.

## Main results

* `Rep.ofStableSubmodule`: the subrepresentation on a `G`-stable submodule, as an object of `Rep`.
* `Rep.cokernelIsoOfRangeEqKer`: the cokernel of `f` is the target of a surjection `p` with
  `ker p = range f`.

The filtration itself is `Rep.exists_categorical_filtration_of_invariant_flag` in
`WeilConjectures.RepresentationTheory.InvariantFlagCategoricalFiltration`.
-/

@[expose] public section

universe u v w

namespace Rep

open CategoryTheory Limits Module

section CommRing

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- The object of `Rep k G` given by a `G`-stable `k`-submodule `S` of `A`, with the restricted
action. -/
abbrev ofStableSubmodule (A : Rep.{w} k G) (S : Submodule k A)
    (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S) : Rep.{w} k G :=
  Rep.of (Subrepresentation.toRepresentation (ρ := A.ρ) ⟨S, fun g _ hx ↦ hS g _ hx⟩)

/-- The inclusion `S ⟶ T` of `G`-stable submodules `S ≤ T`, as a morphism in `Rep k G`. -/
def ofStableSubmoduleInclusion (A : Rep.{w} k G) {S T : Submodule k A}
    (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S) (hT : ∀ (g : G), ∀ x ∈ T, A.ρ g x ∈ T)
    (h : S ≤ T) : A.ofStableSubmodule S hS ⟶ A.ofStableSubmodule T hT :=
  Rep.ofHom ((Submodule.inclusion h).intertwiningMap_of_isIntertwiningMap _ _ fun _ _ ↦ rfl)

/-- The inclusion of a `G`-stable submodule `S` into `A`, as a morphism in `Rep k G`. -/
def ofStableSubmoduleSubtype (A : Rep.{w} k G) (S : Submodule k A)
    (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S) : A.ofStableSubmodule S hS ⟶ A :=
  Rep.ofHom (S.subtype.intertwiningMap_of_isIntertwiningMap _ _ fun _ _ ↦ rfl)

/-- If `p : Y ⟶ Z` in `Rep k G` is surjective with kernel the range of `f : X ⟶ Y`, then
`cokernel f ≅ Z`. -/
noncomputable def cokernelIsoOfRangeEqKer {X Y Z : Rep.{w} k G} (f : X ⟶ Y) (p : Y ⟶ Z)
    (hp : Function.Surjective p.hom)
    (hfp : LinearMap.range f.hom.toLinearMap = LinearMap.ker p.hom.toLinearMap) :
    cokernel f ≅ Z :=
  have hzero : f ≫ p = 0 := by
    ext x
    have hx : f.hom.toLinearMap x ∈ LinearMap.ker p.hom.toLinearMap :=
      hfp ▸ LinearMap.mem_range_self _ x
    simpa using hx
  have hS : (ShortComplex.mk f p hzero).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{w} k G) (ModuleCat.{w} k)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hfp
  have : Epi (ShortComplex.mk f p hzero).g := (epi_iff_surjective p).2 hp
  (cokernelIsCokernel f).coconePointUniqueUpToIso hS.gIsCokernel

end CommRing

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- Let `S ≤ T` be `G`-stable subspaces of `A : Rep k G` with `T` finite-dimensional,
`dim T = dim S + 1`, and `G` acting trivially on `T / S`. Then the cokernel of the inclusion
`S ⟶ T` in `Rep k G` is isomorphic to the trivial representation on any one-dimensional
`k`-vector space `V`. -/
theorem nonempty_cokernel_ofStableSubmoduleInclusion_iso_trivial (A : Rep.{w} k G)
    {S T : Submodule k A} (hS : ∀ (g : G), ∀ x ∈ S, A.ρ g x ∈ S)
    (hT : ∀ (g : G), ∀ x ∈ T, A.ρ g x ∈ T) (hST : S ≤ T) [FiniteDimensional k T]
    (hrank : finrank k T = finrank k S + 1) (htriv : ∀ (g : G), ∀ x ∈ T, A.ρ g x - x ∈ S)
    (V : Type w) [AddCommGroup V] [Module k V] (hV : finrank k V = 1) :
    Nonempty (cokernel (A.ofStableSubmoduleInclusion hS hT hST) ≅ Rep.trivial k G V) := by
  set K := S.comap T.subtype
  have hK : finrank k K = finrank k S := (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
  have hQ : finrank k (T ⧸ K) = finrank k V := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  let e : (T ⧸ K) ≃ₗ[k] V := LinearEquiv.ofFinrankEq _ _ hQ
  let π : T →ₗ[k] V := e.toLinearMap ∘ₗ K.mkQ
  have hπ (g : G) (v : T) : π ((A.ofStableSubmodule T hT).ρ g v) = π v := by
    have hv : (A.ofStableSubmodule T hT).ρ g v - v ∈ K := htriv g v v.2
    rw [← sub_eq_zero, ← map_sub, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero K).2 hv, map_zero]
  refine ⟨cokernelIsoOfRangeEqKer _ (Rep.ofHom (π.intertwiningMap_of_isIntertwiningMap _ _
    fun g v ↦ (hπ g v).trans (Representation.trivial_apply ..).symm))
    (e.surjective.comp K.mkQ_surjective) ?_⟩
  change LinearMap.range (Submodule.inclusion hST) = LinearMap.ker π
  exact (Submodule.range_inclusion _ _ _).trans (by rw [LinearEquiv.ker_comp, Submodule.ker_mkQ])

end Field

end Rep
