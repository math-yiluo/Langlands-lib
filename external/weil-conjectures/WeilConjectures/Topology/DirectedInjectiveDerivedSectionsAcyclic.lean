/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion
import WeilConjectures.CategoryTheory.SiteInjectiveCechAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.Topology.CompactCechDirectedColimit

/-!
# Derived sections of directed colimits of injective sheaves

Source: Stacks Project, Cohomology, Lemma 01FF, final claim and its proof using 01EW.
(blueprint: lem-sc-directed-injective-derived-sections-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat

/-- Directed colimits of injective abelian sheaves are acyclic for sections on compact opens.
Source: Stacks Project, Cohomology, Lemma 01FF, final claim, using Lemma 01EW.
(blueprint: lem-sc-directed-injective-derived-sections-acyclic).

Proof: let B be the compact opens and Cov the finite covers of members of B by members
of B. The basis hypothesis and compactness give finite compact refinements of all covers;
closure under binary intersections gives compactness of every nonempty finite intersection.
For every cover in Cov, sections on each intersection preserve directed colimits by the
degree-zero compact-open section theorem. Finite products preserve these colimits as well,
so the Cech complex of the colimit is the colimit of the Cech complexes of the injectives.
Injective sheaves have zero positive Cech cohomology. Exactness of filtered colimits of
abelian groups implies that the colimit complex also has zero positive cohomology.
Apply the Cech vanishing criterion to B and Cov to deduce vanishing of the right derived
sections on every member of B. This is simultaneously valid on all compact opens, as
required by the criterion. The empty open has zero sections; an empty covering gives
zero Cech complexes. No assertion that the colimit itself is injective is required. -/
theorem directedInjective_isZero_rightDerived_sections
    (X : Type u) [TopologicalSpace X]
    (hbas : ∀ (V : Set X), IsOpen V → ∀ x ∈ V, ∃ W : Set X, IsOpen W ∧
      IsCompact W ∧ x ∈ W ∧ W ⊆ V)
    (hint : ∀ (V W : Set X), IsOpen V → IsOpen W → IsCompact V → IsCompact W →
      IsCompact (V ∩ W))
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (J : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hJ : ∀ i : I, Injective (J.obj i))
    (U : Opens X) (hU : IsCompact (U : Set X)) (n : ℕ) :
    IsZero (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived
        (n + 1)).obj (colimit J)) := by
  classical
  have compact_cech_intersections
      {X : Type u} [TopologicalSpace X]
      (hpairs : ∀ U V : TopologicalSpace.Opens X,
        IsCompact (U : Set X) → IsCompact (V : Set X) →
        IsCompact ((U ⊓ V : TopologicalSpace.Opens X) : Set X))
      {T : Type u} {U : TopologicalSpace.Opens X}
      {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
      (S : SiteCechComplex f hom)
      (hc : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X)) :
      ∀ (p : ℕ) (a : Fin (p + 1) → T),
        IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X) := by
    intro p
    induction p with
    | zero =>
        intro a
        rw [S.W_zero]
        exact hc _
    | succ p ih =>
        intro a
        have he : S.W (p + 1) a = f (a 0) ⊓ S.W p (a ∘ Fin.succ) := by
          apply le_antisymm
          · exact le_inf (S.pr (p + 1) a 0).le (S.indexMap a Fin.succ).le
          · let Z := f (a 0) ⊓ S.W p (a ∘ Fin.succ)
            let b : ∀ k : Fin (p + 1 + 1), Z ⟶ f (a k) :=
              Fin.cases (homOfLE inf_le_left)
                (fun k ↦ homOfLE inf_le_right ≫ S.pr p (a ∘ Fin.succ) k)
            obtain ⟨g, _, _⟩ := S.universal (p + 1) a Z b (fun _ ↦ Subsingleton.elim _ _)
            exact g.le
        rw [he]
        exact hpairs _ _ (hc _) (ih _)
  have compact_basis_cofinal
      {X : Type u} [TopologicalSpace X]
      (hbasis : TopologicalSpace.Opens.IsBasis
        {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
      (U : TopologicalSpace.Opens X) (hU : IsCompact (U : Set X))
      (T : Type u) (V : T → TopologicalSpace.Opens X) (f : ∀ t, V t ⟶ U)
      (hcover : Presieve.ofArrows V f ∈ (Opens.pretopology X).toPrecoverage U) :
      ∃ (K : Type u) (_ : Finite K) (W : K → TopologicalSpace.Opens X)
        (g : ∀ k, W k ⟶ U),
        (∀ k, IsCompact ((W k : TopologicalSpace.Opens X) : Set X)) ∧
        Presieve.ofArrows W g ∈ (Opens.pretopology X).toPrecoverage U ∧
        ∀ k, ∃ (t : T) (a : W k ⟶ V t), a ≫ f t = g k := by
    classical
    have hlocal : ∀ x : U, ∃ (t : T) (W : TopologicalSpace.Opens X),
        IsCompact (W : Set X) ∧ x.val ∈ W ∧ W ≤ V t := by
      intro x
      obtain ⟨Y, a, ha, hx⟩ := hcover x.val x.property
      cases ha with
      | mk t =>
          obtain ⟨W, hW, hxW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp hbasis hx
          exact ⟨t, W, hW, hxW, hWV⟩
    choose t W hc hx hWV using hlocal
    obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X))
      (fun x ↦ (W x).isOpen) (by
        intro x hxU
        exact Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩)
    let g : ∀ k : s, W k.val ⟶ U :=
      fun k ↦ homOfLE ((hWV k.val).trans (f (t k.val)).le)
    refine ⟨s, inferInstance, (fun k ↦ W k.val), g, (fun k ↦ hc k.val), ?_, ?_⟩
    · intro x hxU
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hxU)
      exact ⟨W y, g ⟨y, hy⟩, Presieve.ofArrows.mk (f := g) ⟨y, hy⟩, hxy⟩
    · intro k
      exact ⟨t k.val, homOfLE (hWV k.val), Subsingleton.elim _ _⟩
  have hbasis : Opens.IsBasis {V : Opens X | IsCompact (V : Set X)} := by
    rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨W, ho, hc, hxW, hWV⟩ := hbas V V.isOpen x hx
    exact ⟨⟨W, ho⟩, hc, hxW, hWV⟩
  have hpairs (V W : Opens X) (hV : IsCompact (V : Set X))
      (hW : IsCompact (W : Set X)) : IsCompact ((V ⊓ W : Opens X) : Set X) :=
    hint V W V.isOpen W.isOpen hV hW
  classical
  have htopology : (Opens.grothendieckTopology X).toPrecoverage =
      (Opens.pretopology X).toPrecoverage := by
    rw [← Opens.toPretopology_grothendieckTopology]
    rfl
  have : (Opens.pretopology X).toPrecoverage.HasIsos := htopology ▸ inferInstance
  have : (Opens.pretopology X).toPrecoverage.IsStableUnderComposition := htopology ▸ inferInstance
  have : (Opens.pretopology X).toPrecoverage.IsStableUnderBaseChange := htopology ▸ inferInstance
  have htop : (Opens.pretopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    change (Opens.pretopology X).toCoverage.toPrecoverage.toGrothendieck = _
    rw [Coverage.toGrothendieck_toPrecoverage, Pretopology.toGrothendieck_toCoverage,
      Opens.pretopology_toGrothendieck]
  have hcech : ∀ (U : TopologicalSpace.Opens X), IsCompact (U : Set X) →
      ∀ (T : Type u) [Finite T] (f : T → TopologicalSpace.Opens X)
        (hom : ∀ t, f t ⟶ U)
        (hcompact : ∀ t, IsCompact ((f t : TopologicalSpace.Opens X) : Set X))
        (hcover : Presieve.ofArrows f hom ∈ (Opens.pretopology X).toPrecoverage U)
        (S : SiteCechComplex f hom),
        ∀ p : ℕ, 0 < p →
          IsZero ((S.cohomologyFunctor p).obj (colimit J).obj) := by
    intro U _ T _ f hom hcompact hcover S p hp
    let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      S.cohomologyFunctor p
    have : PreservesColimit J E :=
      Sheaf.compact_siteCech_cohomology_preserves_directedColimit X hbas hint S
        (compact_cech_intersections hpairs S hcompact) J p
    apply (isColimitOfPreserves E (colimit.isColimit J)).isZero_pt
    apply Functor.isZero
    intro i
    have : Injective (J.obj i) := hJ i
    have hinj := @site_injective_cech_acyclic
      (TopologicalSpace.Opens X) _ (Opens.pretopology X).toPrecoverage _ _ _ _
      T U f hom hcover S
    rw [htop] at hinj
    exact (hinj (J.obj i)).1 p hp
  have hcohom : IsZero (CategoryTheory.Sheaf.H' (colimit J) (n + 1) U) := by
    let B : Set (TopologicalSpace.Opens X) := {U | IsCompact (U : Set X)}
    let Cov := fun (U : TopologicalSpace.Opens X) (T : Type u)
      (V : T → TopologicalSpace.Opens X) (f : ∀ t, V t ⟶ U) ↦
        Finite T ∧ IsCompact (U : Set X) ∧
        (∀ t, IsCompact ((V t : TopologicalSpace.Opens X) : Set X)) ∧
        Presieve.ofArrows V f ∈ (Opens.pretopology X).toPrecoverage U
    let S := fun U T V f (h : Cov U T V f) ↦
      (SiteCechComplex.exists_of_covering (Opens.pretopology X).toPrecoverage h.2.2.2).some
    have hc := @Sheaf.isZero_H'_of_siteCech_vanishing.{u, u}
      (TopologicalSpace.Opens X) _ (Opens.pretopology X).toPrecoverage _ _ _ _
    rw [htop] at hc
    apply hc B Cov S (colimit J)
    · intro U T V f h
      exact h.2.2.2
    · intro U T V f h
      exact ⟨h.2.1, h.2.2.1, compact_cech_intersections hpairs (S U T V f h) h.2.2.1⟩
    · intro U hU T V f h
      obtain ⟨K, hK, W, g, hW, hcov, href⟩ := compact_basis_cofinal hbasis U hU T V f h
      exact ⟨K, W, g, ⟨hK, hU, hW, hcov⟩, href⟩
    · intro U T V f h p hp
      have : Finite T := h.1
      exact hcech U h.2.1 T V f h.2.2.1 h.2.2.2 (S U T V f h) p hp
    · exact hU
    · omega
  obtain ⟨e⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    (Opens.grothendieckTopology X) U (n + 1)
  exact hcohom.of_iso (e.app (colimit J)).symm

end TopCat
