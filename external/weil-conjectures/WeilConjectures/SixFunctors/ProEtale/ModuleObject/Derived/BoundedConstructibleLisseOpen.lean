/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!
# Bounded constructible complexes are lisse on a dense open

Let `Λ` be a commutative condensed ring and `D` a nonempty scheme with noetherian underlying
space. For a bounded constructible complex `K` on `D` there is a nonempty open `V` of `D` and a
surjective closed immersion `c : E ⟶ V` such that every cohomology sheaf of the pullback of `K`
to `E` is pro-étale locally finitely presented
(`ProEtale.CondensedRing.exists_isLocallyFinitelyPresented_homology_upperStar`). The scheme `E` is
`V` up to nilpotents: it is the intersection of `V` with strata of stratifications adapted to the
finitely many nonzero cohomology sheaves of `K`, which carry their reduced scheme structures.
The same holds simultaneously for two bounded constructible complexes `K` and `L`
(`ProEtale.CondensedRing.exists_isLocallyFinitelyPresented_homology_upperStar₂`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that the
latter can use these statements.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]

/-- If `k^* g^* M` is pro-étale locally finitely presented, then so is `(k ≫ g)^* M`. -/
lemma isLocallyFinitelyPresented_upperStar_comp {P W X : Scheme.{u}} (k : P ⟶ W) (g : W ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ P) ((k)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M))) :
    IsLocallyFinitelyPresented (condensedRingObj Λ P) ((k ≫ g)^*⟦Λ⟧.obj M) :=
  hM.of_iso ((upperStarComp Λ k g).app M).symm

/-- A constructible sheaf `G` on a nonempty scheme `D` becomes pro-étale locally finitely
presented on a surjective closed immersion `c : E ⟶ W` into a nonempty open `j : W ⟶ D`: take
for `W` a nonempty open contained in a stratum of a stratification adapted to `G`. -/
lemma exists_isLocallyFinitelyPresented_upperStar_of_isConstructible {D : Scheme.{u}}
    [Nonempty D]
    {G : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D)}
    (hG : IsConstructibleModuleObject (condensedRingObj Λ D) G) :
    ∃ (W E : Scheme.{u}) (j : W ⟶ D) (c : E ⟶ W), IsOpenImmersion j ∧ Nonempty W ∧
      IsClosedImmersion c ∧ Surjective c ∧
      IsLocallyFinitelyPresented (condensedRingObj Λ E) ((c ≫ j)^*⟦Λ⟧.obj G) := by
  obtain ⟨S, hS⟩ := hG
  obtain ⟨a, V, ⟨v, hv⟩, hVS⟩ := exists_nonempty_opens_subset_stratum S
  have : Surjective (pullback.fst V.ι (S.immersion a)) :=
    surjective_pullback_fst_of_range_subset _ _ (by
      rw [Scheme.Opens.range_ι, S.range_immersion]
      exact hVS)
  exact ⟨V, _, V.ι, pullback.fst V.ι (S.immersion a), inferInstance, ⟨⟨v, hv⟩⟩,
    IsClosedImmersion.of_isImmersion_of_surjective _, this,
    isLocallyFinitelyPresented_upperStar_comp_of_comm Λ pullback.condition
      ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS a))⟩

/-- Finitely many constructible sheaves `G i` (`i ∈ s`) on a nonempty scheme `D` with noetherian
underlying space all become pro-étale locally finitely presented on a common surjective closed
immersion `c : E ⟶ W` into a nonempty open `j : W ⟶ D`. -/
lemma exists_isLocallyFinitelyPresented_upperStar_of_finset {ι : Type*} (s : Finset ι) :
    ∀ (D : Scheme.{u}) [TopologicalSpace.NoetherianSpace D] [Nonempty D]
      (G : ι → Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D)),
      (∀ i ∈ s, IsConstructibleModuleObject (condensedRingObj Λ D) (G i)) →
      ∃ (W E : Scheme.{u}) (j : W ⟶ D) (c : E ⟶ W), IsOpenImmersion j ∧ Nonempty W ∧
        IsClosedImmersion c ∧ Surjective c ∧ ∀ i ∈ s,
          IsLocallyFinitelyPresented (condensedRingObj Λ E) ((c ≫ j)^*⟦Λ⟧.obj (G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro D _ _ G _
    exact ⟨D, D, 𝟙 D, 𝟙 D, inferInstance, inferInstance, inferInstance, inferInstance,
      fun _ h ↦ absurd h (Finset.notMem_empty _)⟩
  | insert i s _ ih =>
    intro D _ _ G hG
    obtain ⟨W₁, E₁, j₁, c₁, _, _, _, _, h₁⟩ :=
      ih D G fun k hk ↦ hG k (Finset.mem_insert_of_mem hk)
    have : TopologicalSpace.NoetherianSpace W₁ := j₁.isOpenEmbedding.isInducing.noetherianSpace
    obtain ⟨W₂, E₂, j₂, c₂, _, _, _, _, h₂⟩ :=
      exists_isLocallyFinitelyPresented_upperStar_of_isConstructible
        (IsConstructibleModuleObject.upperStar Λ j₁ (hG i (Finset.mem_insert_self i s)))
    have : Surjective (pullback.fst j₂ c₁) := MorphismProperty.pullback_fst _ _ inferInstance
    have : Surjective (pullback.fst (pullback.fst j₂ c₁) c₂) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    let c := pullback.fst (pullback.fst j₂ c₁) c₂ ≫ pullback.fst j₂ c₁
    have hc₁ : c ≫ j₂ ≫ j₁ =
        (pullback.fst (pullback.fst j₂ c₁) c₂ ≫ pullback.snd j₂ c₁) ≫ c₁ ≫ j₁ := by
      simp only [c, Category.assoc, pullback.condition_assoc]
    have hc₂ : c = pullback.snd (pullback.fst j₂ c₁) c₂ ≫ c₂ := by
      simp only [c, pullback.condition]
    refine ⟨W₂, _, j₂ ≫ j₁, c, inferInstance, inferInstance, inferInstance, inferInstance,
      fun k hk ↦ ?_⟩
    rcases Finset.mem_insert.1 hk with rfl | hk
    · rw [← Category.assoc]
      refine isLocallyFinitelyPresented_upperStar_comp _ _ ?_
      rw [hc₂, Category.assoc]
      exact isLocallyFinitelyPresented_upperStar_comp_of_comm Λ rfl h₂
    · exact isLocallyFinitelyPresented_upperStar_comp_of_comm Λ hc₁ (h₁ k hk)

/-- **A bounded constructible complex is lisse on a dense open, up to nilpotents**: on a nonempty
scheme `D` with noetherian underlying space, a bounded constructible complex `K` has a nonempty
open `V` and a surjective closed immersion `c : E ⟶ V` such that all cohomology sheaves of the
pullback of `K` to `E` are pro-étale locally finitely presented. -/
theorem exists_isLocallyFinitelyPresented_homology_upperStar {D : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace D] [Nonempty D]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D))}
    (hK : boundedConstructible (condensedRingObj Λ D) K) :
    ∃ (V : D.Opens) (E : Scheme.{u}) (c : E ⟶ V), (V : Set D).Nonempty ∧
      IsClosedImmersion c ∧ Surjective c ∧ ∀ n : ℤ,
        IsLocallyFinitelyPresented (condensedRingObj Λ E)
          ((DerivedCategory.homologyFunctor _ n).obj ((L(((c ≫ V.ι))^*⟦Λ⟧)).obj K)) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  obtain ⟨W, E, j, c, _, ⟨w⟩, _, _, h⟩ := exists_isLocallyFinitelyPresented_upperStar_of_finset
    (Finset.Icc a b) D (fun n ↦ (DerivedCategory.homologyFunctor _ n).obj K) fun n _ ↦ hc n
  have hcj : (c ≫ j.isoOpensRange.hom) ≫ j.opensRange.ι = c ≫ j := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨j.opensRange, E, c ≫ j.isoOpensRange.hom, ⟨j w, w, rfl⟩, inferInstance,
    inferInstance, fun n ↦ ?_⟩
  rw [hcj]
  refine IsLocallyFinitelyPresented.of_iso ((leftDerivedUpperStarHomologyIso Λ (c ≫ j) n).app K) ?_
  by_cases hn : n ∈ Finset.Icc a b
  · exact h n hn
  · refine isLocallyFinitelyPresented_of_isZero _ ((c ≫ j)^*⟦Λ⟧.map_isZero (hab n ?_))
    rw [Finset.mem_Icc] at hn
    lia

/-- **Two bounded constructible complexes are simultaneously lisse on a dense open, up to
nilpotents**: on a nonempty scheme `D` with noetherian underlying space, bounded constructible
complexes `K` and `L` have a common nonempty open `V` and surjective closed immersion
`c : E ⟶ V` such that all cohomology sheaves of the pullbacks of `K` and of `L` to `E` are
pro-étale locally finitely presented. -/
theorem exists_isLocallyFinitelyPresented_homology_upperStar₂ {D : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace D] [Nonempty D]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D))}
    (hK : boundedConstructible (condensedRingObj Λ D) K)
    (hL : boundedConstructible (condensedRingObj Λ D) L) :
    ∃ (V : D.Opens) (E : Scheme.{u}) (c : E ⟶ V), (V : Set D).Nonempty ∧
      IsClosedImmersion c ∧ Surjective c ∧ (∀ n : ℤ,
        IsLocallyFinitelyPresented (condensedRingObj Λ E)
          ((DerivedCategory.homologyFunctor _ n).obj ((L(((c ≫ V.ι))^*⟦Λ⟧)).obj K))) ∧
      ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ E)
        ((DerivedCategory.homologyFunctor _ n).obj ((L(((c ≫ V.ι))^*⟦Λ⟧)).obj L)) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  obtain ⟨⟨a', b', hab'⟩, hc'⟩ := (mem_boundedConstructible_iff _ L).1 hL
  obtain ⟨W, E, j, c, _, ⟨w⟩, _, _, h⟩ := exists_isLocallyFinitelyPresented_upperStar_of_finset
    ((Finset.Icc a b).disjSum (Finset.Icc a' b')) D
    (Sum.elim (fun n ↦ (DerivedCategory.homologyFunctor _ n).obj K)
      (fun n ↦ (DerivedCategory.homologyFunctor _ n).obj L))
    fun i _ ↦ i.rec hc hc'
  have hcj : (c ≫ j.isoOpensRange.hom) ≫ j.opensRange.ι = c ≫ j := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  refine ⟨j.opensRange, E, c ≫ j.isoOpensRange.hom, ⟨j w, w, rfl⟩, inferInstance,
    inferInstance, fun n ↦ ?_, fun n ↦ ?_⟩
  · rw [hcj]
    refine IsLocallyFinitelyPresented.of_iso
      ((leftDerivedUpperStarHomologyIso Λ (c ≫ j) n).app K) ?_
    by_cases hn : n ∈ Finset.Icc a b
    · exact h (.inl n) (Finset.inl_mem_disjSum.2 hn)
    · refine isLocallyFinitelyPresented_of_isZero _ ((c ≫ j)^*⟦Λ⟧.map_isZero (hab n ?_))
      rw [Finset.mem_Icc] at hn
      lia
  · rw [hcj]
    refine IsLocallyFinitelyPresented.of_iso
      ((leftDerivedUpperStarHomologyIso Λ (c ≫ j) n).app L) ?_
    by_cases hn : n ∈ Finset.Icc a' b'
    · exact h (.inr n) (Finset.inr_mem_disjSum.2 hn)
    · refine isLocallyFinitelyPresented_of_isZero _ ((c ≫ j)^*⟦Λ⟧.map_isZero (hab' n ?_))
      rw [Finset.mem_Icc] at hn
      lia

end AlgebraicGeometry.ProEtale.CondensedRing
