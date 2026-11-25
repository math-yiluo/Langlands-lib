/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LisseLocus

/-!
# Smooth irreducible opens on which a Weil sheaf is lisse

A nonempty reduced scheme `X` of finite type over a finite field `k₀` has a nonempty irreducible
open subscheme `V`, smooth over `k₀`, on which a given Weil sheaf is lisse
(`AlgebraicGeometry.WeilSheaf.exists_opens_smooth_irreducibleSpace_isLisse`). This is the generic
step of the Noetherian inductions over Weil sheaves: the smooth locus (`k₀` being perfect) and
the lisse locus (`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`) are dense opens,
and a dense open of a Noetherian space contains a nonempty irreducible open
(`TopologicalSpace.exists_isOpen_isIrreducible_subset_of_dense`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace TopologicalSpace

variable {α : Type*} [TopologicalSpace α] [NoetherianSpace α]

/-- In a nonempty Noetherian space, a dense open subset contains a nonempty irreducible open
subset: its intersection with the complement of all but one irreducible component. -/
theorem exists_isOpen_isIrreducible_subset_of_dense [Nonempty α] {W : Set α} (hW : IsOpen W)
    (hd : Dense W) : ∃ V : Set α, IsOpen V ∧ IsIrreducible V ∧ V ⊆ W := by
  obtain ⟨x⟩ := ‹Nonempty α›
  set Z := irreducibleComponent x
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := α)
  set O := (⋃₀ (irreducibleComponents α \ {Z}))ᶜ
  have hO : IsOpen O := by
    rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hcl : closure O = Z := closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ
  have hOne : O.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hcl
    exact Set.eq_empty_iff_forall_notMem.1 hcl.symm x mem_irreducibleComponent
  have hOZ : O ⊆ Z := hcl ▸ subset_closure
  obtain ⟨y, hyO, hyW⟩ : (O ∩ W).Nonempty := hd.inter_open_nonempty O hO hOne
  exact ⟨W ∩ O, hW.inter hO, hZ.1.2.subset_irreducible
    (show (W ∩ O).Nonempty from ⟨y, hyW, hyO⟩) (hW.inter hO) subset_rfl
    (Set.inter_subset_right.trans hOZ), Set.inter_subset_left⟩

end TopologicalSpace

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Generic smoothness and lissity.** A nonempty reduced `k₀`-scheme `X` of finite type has a
nonempty irreducible open subscheme `V`, smooth over `k₀`, on which a given Weil sheaf `G` is
lisse: the smooth locus (`k₀` is perfect) and the lisse locus
(`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`) are dense opens, and a dense open
of the Noetherian space `X` contains a nonempty irreducible open. -/
theorem exists_opens_smooth_irreducibleSpace_isLisse [IsReduced X] [Nonempty X]
    (G : WeilSheaf k₀ l X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ Smooth (V.toScheme ↘ Spec (CommRingCat.of k₀)) ∧
      IrreducibleSpace V ∧ ((WeilSheaf.upperStar V.ι).obj G).IsLisse := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian X := ⟨⟩
  obtain ⟨L, hLd, hL⟩ := exists_dense_isLisse_upperStar G
  set S := (X ↘ Spec (CommRingCat.of k₀)).smoothLocus
  have hS : Dense (S : Set X) := (X ↘ Spec (CommRingCat.of k₀)).dense_smoothLocus_of_perfectField
  obtain ⟨V₀, hVo, hVi₀, hVsub₀⟩ := exists_isOpen_isIrreducible_subset_of_dense
    (L ⊓ S).isOpen (hLd.inter_of_isOpen_left hS L.isOpen)
  obtain ⟨x, hx⟩ := hVi₀.nonempty
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx hVo
  set V := (W : Set X)
  have hVi : IsIrreducible V := hVi₀.2.subset_irreducible ⟨x, hxW⟩ W.isOpen subset_rfl hWV
  have hVsub : V ⊆ L ⊓ S := hWV.trans hVsub₀
  set V' : X.Opens := W
  have hVL : V' ≤ L := fun x hx ↦ (hVsub hx).1
  have hVS : V' ≤ S := fun x hx ↦ (hVsub hx).2
  refine ⟨V', hW, ?_, isIrreducible_iff_irreducibleSpace.1 hVi, ?_⟩
  · rw [← Scheme.Opens.ι_comp_over, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro x _
    exact hVS x.2
  · have h := ((isLisse_upperStar_comp_iff (X.homOfLE hVL) L.ι G).2 (hL.upperStar _))
    exact (isLisse_upperStar_congr (X.homOfLE_ι hVL) G).1 h

end AlgebraicGeometry.WeilSheaf
