/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import WeilConjectures.Topology.NoetherianOpenClosedCohomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Gluing universal vanishing over two closed subsets

Source: Stacks Project, Proposition 02UZ, component-reduction argument.
(blueprint: lem-sc-closed-union-cohomology-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

private lemma zero_cohomology_of_closed_embedding
    {Y T : TopCat.{u}} (i : Y ⟶ T) (hi : Topology.IsClosedEmbedding i)
    (G : Y.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    (h : IsZero (CategoryTheory.Sheaf.H'
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) q (⊤ : Opens T))) :
    IsZero (@CategoryTheory.Sheaf.H' (Opens Y) _ (Opens.grothendieckTopology Y) _
      (HasExt.standard _) G q ⊤) := by
  obtain ⟨e⟩ := cohomology_closed_immersion_pushforward i hi G q
  have hs := AddCommGrpCat.subsingleton_of_isZero h
  change Subsingleton (Abelian.Ext.{u} _ _ q) at hs
  let : HasExt.{u + 1}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _
  let : Subsingleton (CategoryTheory.Sheaf.H'.{u + 1, u, u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) q (⊤ : Opens T)) := by
    change Subsingleton (Abelian.Ext.{u + 1} _ _ q)
    exact (Abelian.Ext.chgUniv.{u, u + 1}).subsingleton
  have hz : IsZero (CategoryTheory.Sheaf.H'.{u + 1, u, u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) q (⊤ : Opens T)) :=
    AddCommGrpCat.isZero_of_subsingleton _
  exact hz.of_iso e

/-- Universal degree-q vanishing is stable under a binary union of closed subsets.
Source: Stacks Project, Proposition 02UZ, component-reduction argument, using
Lemma 02UV and the open-closed short exact sequence of Modules, Lemma 02UT.
(blueprint: lem-sc-closed-union-cohomology-vanishing).

Proof: Work on T = Z ∪ W, which is Noetherian as a subspace of X. Regard Z and
W as closed subspaces of T with their unchanged intrinsic topologies. Put
U = T \ Z. The open-closed short exact sequence for F has right term the
closed pushforward of F restricted to Z, whose degree-q cohomology is zero
by closed-pushforward comparison and hZ. Its left term j_!j^*F is the closed
pushforward of a sheaf G on closure(U). Since W is closed and contains U,
closure(U) is contained in W. Push G forward along the closed inclusion
closure(U) → W. Hypothesis hW and closed-pushforward comparison imply that
H^q(closure(U),G) is zero, hence the left term has zero degree-q cohomology
on T. Exactness at H^q(T,F) now makes it zero. For q=0 use the initial left
exact part of the same sequence. Empty, equal, and nested Z and W cause no
exception: the inclusions and support statement still apply. -/
theorem cohomology_vanishing_of_closed_union
    (X : Type u) [TopologicalSpace X] [NoetherianSpace X]
    (Z W : Closeds X) (q : ℕ)
    (hZ : ∀ G : Sheaf (Opens.grothendieckTopology (Z : Set X)) AddCommGrpCat.{u},
      IsZero (Sheaf.H' G q (⊤ : Opens (Z : Set X))))
    (hW : ∀ G : Sheaf (Opens.grothendieckTopology (W : Set X)) AddCommGrpCat.{u},
      IsZero (Sheaf.H' G q (⊤ : Opens (W : Set X))))
    (F : Sheaf (Opens.grothendieckTopology ((Z ⊔ W : Closeds X) : Set X))
      AddCommGrpCat.{u}) :
    IsZero (Sheaf.H' F q (⊤ : Opens ((Z ⊔ W : Closeds X) : Set X))) := by
  let T := TopCat.of ↥((Z ⊔ W : Closeds X) : Set X)
  let U : Opens T := ⟨Subtype.val ⁻¹' (Z : Set X)ᶜ,
    Z.isClosed.isOpen_compl.preimage continuous_subtype_val⟩
  let D := TopCat.of ↥((U : Set T)ᶜ)
  let C := TopCat.of ↥(closure (U : Set T))
  have hT : Topology.IsClosedEmbedding (Subtype.val : T → X) :=
    (Z ⊔ W).isClosed.isClosedEmbedding_subtypeVal
  have hD : IsClosed ((U : Set T)ᶜ) := U.isOpen.isClosed_compl
  have hCW : closure (U : Set T) ⊆ Subtype.val ⁻¹' (W : Set X) := by
    apply closure_minimal _ (W.isClosed.preimage continuous_subtype_val)
    intro x hx
    have hxZW : x.val ∈ (Z : Set X) ∪ (W : Set X) := x.property
    exact hxZW.resolve_left hx
  let iD : D ⟶ T := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let kZ : D ⟶ TopCat.of ↥(Z : Set X) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.val.val, by
      have hx : ¬¬ x.val.val ∈ (Z : Set X) := x.property
      exact Classical.not_not.mp hx⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x : D ↦ Classical.not_not.mp x.property)⟩
  have hkZ : Topology.IsClosedEmbedding kZ := by
    apply Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
    exact hT.comp hD.isClosedEmbedding_subtypeVal
  let kW : C ⟶ TopCat.of ↥(W : Set X) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.val.val, hCW x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x : C ↦ hCW x.property)⟩
  have hkW : Topology.IsClosedEmbedding kW := by
    apply Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
    exact hT.comp isClosed_closure.isClosedEmbedding_subtypeVal
  obtain ⟨a, _, ⟨ha, hS⟩, G, _, hG⟩ :=
    noetherian_open_closed_cohomology_sequence T U F
  let S := ShortComplex.mk a
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} iD).unit.app F) ha
  let : HasExt.{u + 1}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _
  have hzD := zero_cohomology_of_closed_embedding kZ hkZ
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} iD).obj F) q
    (hZ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} kZ).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} iD).obj F)))
  obtain ⟨eD⟩ := cohomology_closed_immersion_pushforward iD
    hD.isClosedEmbedding_subtypeVal
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} iD).obj F) q
  have hz₃ : IsZero (CategoryTheory.Sheaf.H'.{u + 1, u, u} S.X₃ q (⊤ : Opens T)) :=
    hzD.of_iso eD.symm
  have hzC := zero_cohomology_of_closed_embedding kW hkW G q
    (hW ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} kW).obj G))
  obtain ⟨eC⟩ := hG q
  have hz₁ : IsZero (CategoryTheory.Sheaf.H'.{u + 1, u, u} S.X₁ q (⊤ : Opens T)) :=
    hzC.of_iso eC.symm
  have hs₁ := AddCommGrpCat.subsingleton_of_isZero hz₁
  have hs₃ := AddCommGrpCat.subsingleton_of_isZero hz₃
  have hsF : Subsingleton (CategoryTheory.Sheaf.H'.{u + 1, u, u} F q (⊤ : Opens T)) := by
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS x (hs₃.elim _ _)
    rw [hs₁.elim y 0, Abelian.Ext.zero_comp]
  change Subsingleton (Abelian.Ext.{u + 1} _ F q) at hsF
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  change Subsingleton (Abelian.Ext.{u} _ F q)
  exact (Abelian.Ext.chgUniv.{u + 1, u}).subsingleton

end TopCat
