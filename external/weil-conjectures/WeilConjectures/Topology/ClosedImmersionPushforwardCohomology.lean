/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.Topology.Sheaves.LerayAcyclicComparison
import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Cohomology and closed immersion pushforward

Source: literature/stacks-project/cohomology.tex, Lemma 02UV
(blueprint: lem-sc-cohomology-closed-immersion-pushforward)

## Main statements

* `cohomology_closed_immersion_pushforward`: cohomology is invariant under
  pushforward along a closed embedding.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

universe u

namespace TopCat

/-- The epimorphism part of Stacks Tag 01AX for arbitrary closed embeddings.
At a point of the image, a local lift on `V` pulls back from the ambient open
`U \ i(Z \ V)`. Off the closed image, the inverse-image open is empty. -/
private theorem epi_pushforward_closedEmbedding
    {Z X : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} Z} (g : F ⟶ G) [Epi g] :
    Epi ((Sheaf.pushforward AddCommGrpCat.{u} i).map g) := by
  classical
  apply (Sheaf.isLocallySurjective_iff_epi _).1
  apply (Presheaf.isLocallySurjective_iff _).2
  intro U t x hx
  have hg := (Presheaf.isLocallySurjective_iff g.hom).1
    ((Sheaf.isLocallySurjective_iff_epi g).2 inferInstance)
  by_cases hxim : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hxim
    obtain ⟨V, hVU, ⟨s, hs⟩, hz⟩ := hg ((Opens.map i).obj U) t z hx
    let W : Opens X := ⟨U ∩ (i '' (V : Set Z)ᶜ)ᶜ,
      U.isOpen.inter (hi.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
    have hWU : W ≤ U := fun y hy ↦ hy.1
    have hWV : (Opens.map i).obj W ≤ V := by
      intro y hy
      by_contra hyV
      exact hy.2 ⟨y, hyV, rfl⟩
    refine ⟨W, hWU, ⟨F.obj.map (homOfLE hWV).op s, ?_⟩, ?_⟩
    · change g.hom.app (Opposite.op ((Opens.map i).obj W))
        (F.obj.map (homOfLE hWV).op s) =
          G.obj.map (homOfLE ((Opens.map i).monotone hWU)).op t
      rw [← ConcreteCategory.comp_apply, g.hom.naturality, ConcreteCategory.comp_apply, hs]
      change G.obj.map (homOfLE hWV).op (G.obj.map (homOfLE hVU).op t) = _
      rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp]
      rfl
    · exact ⟨hx, fun ⟨y, hy, he⟩ ↦ hy (hi.isEmbedding.injective he ▸ hz)⟩
  · let W : Opens X := ⟨U ∩ (Set.range i)ᶜ, U.isOpen.inter hi.isClosed_range.isOpen_compl⟩
    have hWU : W ≤ U := fun y hy ↦ hy.1
    have he : (Opens.map i).obj W = ⊥ := by
      ext z
      change (i z ∈ U ∧ i z ∉ Set.range i) ↔ False
      exact ⟨fun hz ↦ hz.2 ⟨z, rfl⟩, False.elim⟩
    refine ⟨W, hWU, ⟨0, ?_⟩, hx, hxim⟩
    have ht := G.isTerminalOfEqEmpty he
    have hzero := ConcreteCategory.congr_hom (ht.hom_ext (𝟙 _) 0)
      (G.obj.map (homOfLE ((Opens.map i).monotone hWU)).op t)
    change g.hom.app (Opposite.op ((Opens.map i).obj W)) 0 =
      G.obj.map (homOfLE ((Opens.map i).monotone hWU)).op t
    rw [map_zero]
    exact hzero.symm

/-- Source: literature/stacks-project/cohomology.tex, Lemma 02UV
(blueprint: lem-sc-cohomology-closed-immersion-pushforward).

For a closed embedding of topological spaces, the cohomology of an abelian
sheaf agrees with that of its direct image. The proof uses exactness of direct
image, vanishing of its higher derived functors, and the Leray comparison.
-/
theorem cohomology_closed_immersion_pushforward
    {Z X : TopCat.{u}}
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat Z) (p : ℕ) :
    Nonempty
      (@CategoryTheory.Sheaf.H' (Opens Z) _ (Opens.grothendieckTopology Z) _
          (HasExt.standard _) F p ⊤ ≅
        @CategoryTheory.Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _
          (HasExt.standard _) ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj F) p ⊤) := by
  -- Pushforward is additive and left exact; the helper supplies preservation of epis.
  let : (Sheaf.pushforwardAb i ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
    Functor.additive_of_iso
      (F := sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj
          (Opens.map i).op) (Iso.refl _)
  let : (Sheaf.pushforwardAb i).Additive :=
    Functor.additive_of_comp_faithful (Sheaf.pushforwardAb i)
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let : (Sheaf.pushforwardAb i).PreservesEpimorphisms :=
    ⟨fun g _ ↦ epi_pushforward_closedEmbedding i hi g⟩
  let : Limits.PreservesFiniteLimits (Sheaf.pushforwardAb i) := inferInstance
  let : (Sheaf.pushforwardAb i).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  let : Limits.PreservesFiniteColimits (Sheaf.pushforwardAb i) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  obtain ⟨_, _, ε, _, hiso⟩ := Sheaf.exists_lerayEdge_isIso_of_acyclic i
  have hacyclic : ∀ q : ℕ, 0 < q → Limits.IsZero
      (((Sheaf.pushforwardAb i).rightDerived q).obj F) := by
    intro q hq
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact Functor.isZero_rightDerived_obj_of_exact _ F r
  have := hiso F hacyclic p
  -- Leray uses small Ext groups; the statement fixes HasExt.standard in universe u + 1.
  -- Compare both Ext constructions with morphisms in the same derived category.
  let : HasDerivedCategory.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} Z) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
    HasDerivedCategory.standard _
  let hEZ : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} Z) := HasExt.standard _
  let hEX : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := HasExt.standard _
  let e := (asIso ((ε p).app F)).symm.addCommGroupIsoToAddEquiv
  let eZ := (@CategoryTheory.Abelian.Ext.homAddEquiv.{u + 1, u + 1}
    (TopCat.Sheaf AddCommGrpCat.{u} Z) _ _ hEZ
    ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)) F inferInstance p).trans
    (CategoryTheory.Abelian.Ext.homAddEquiv.{u + 1, u}).symm
  let eX := (@CategoryTheory.Abelian.Ext.homAddEquiv.{u + 1, u + 1}
    (TopCat.Sheaf AddCommGrpCat.{u} X) _ _ hEX
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free))
    ((Sheaf.pushforwardAb i).obj F) inferInstance p).trans
    (CategoryTheory.Abelian.Ext.homAddEquiv.{u + 1, u}).symm
  exact ⟨((eZ.trans e).trans eX.symm).toAddCommGrpIso⟩

end TopCat
