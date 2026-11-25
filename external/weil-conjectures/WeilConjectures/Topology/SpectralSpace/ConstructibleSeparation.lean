/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.Topology.Spectral.Prespectral

/-!
# Constructible separation data in a spectral space

Let `T₁`, `T₂` be disjoint closed subsets of a compact prespectral space `X`. The existence
lemma `PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ` provides compact opens
`O₁`, `O₂` covering `X` with `O₁ ∩ T₁ = ∅` and `O₂ ∩ T₂ = ∅`. Choosing such a pair, the
**constructible separation data** of `(T₁, T₂)` is the pair of complements `(O₁ᶜ, O₂ᶜ)`
(blueprint: `lemma-extending-isomorphism-over-closure-closed--1`). These are closed subsets with
compact complements containing `T₁` and `T₂` respectively, and they are disjoint; in a
spectral (more generally quasi-separated) space they are constructible
(blueprint: `lemma-extending-isomorphism-over-closure-closed--1`).

## Main definitions

- `PrespectralSpace.constructibleSeparation`: the chosen pair `(T₁ᶜ_c, T₂ᶜ_c)`.

## Main results

- `PrespectralSpace.constructibleSeparation_spec`: the separation data are closed,
  constructible, contain `T₁` resp. `T₂`, and are disjoint.
-/

@[expose] public section

open Set

namespace PrespectralSpace

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
  {T₁ T₂ : Set X} (h₁ : IsClosed T₁) (h₂ : IsClosed T₂) (hd : Disjoint T₁ T₂)

/-- **Constructible separation data in a spectral space** (blueprint:
`lemma-extending-isomorphism-over-closure-closed--1`): for disjoint closed subsets `T₁`, `T₂`,
select compact opens `(O₁, O₂)` from
`PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ` (blueprint:
`lemma-extending-isomorphism-over-closure-closed--1`) and return the complements
`(O₁ᶜ, O₂ᶜ)`. -/
noncomputable def constructibleSeparation : Set X × Set X :=
  ((exists_isCompact_isOpen_disjoint_union_eq_univ h₁ h₂ hd).choose ᶜ,
    (exists_isCompact_isOpen_disjoint_union_eq_univ h₁ h₂ hd).choose_spec.choose ᶜ)

/-- The defining properties of the chosen compact opens, in terms of the complements. -/
lemma constructibleSeparation_spec_compl :
    IsOpen (constructibleSeparation h₁ h₂ hd).1ᶜ ∧ IsOpen (constructibleSeparation h₁ h₂ hd).2ᶜ ∧
      IsCompact (constructibleSeparation h₁ h₂ hd).1ᶜ ∧
      IsCompact (constructibleSeparation h₁ h₂ hd).2ᶜ ∧
      Disjoint (constructibleSeparation h₁ h₂ hd).1ᶜ T₁ ∧
      Disjoint (constructibleSeparation h₁ h₂ hd).2ᶜ T₂ ∧
      (constructibleSeparation h₁ h₂ hd).1ᶜ ∪ (constructibleSeparation h₁ h₂ hd).2ᶜ = univ := by
  simp only [constructibleSeparation, compl_compl]
  exact (exists_isCompact_isOpen_disjoint_union_eq_univ h₁ h₂ hd).choose_spec.choose_spec

lemma isClosed_constructibleSeparation_fst : IsClosed (constructibleSeparation h₁ h₂ hd).1 :=
  isOpen_compl_iff.mp (constructibleSeparation_spec_compl h₁ h₂ hd).1

lemma isClosed_constructibleSeparation_snd : IsClosed (constructibleSeparation h₁ h₂ hd).2 :=
  isOpen_compl_iff.mp (constructibleSeparation_spec_compl h₁ h₂ hd).2.1

lemma isCompact_compl_constructibleSeparation_fst :
    IsCompact (constructibleSeparation h₁ h₂ hd).1ᶜ :=
  (constructibleSeparation_spec_compl h₁ h₂ hd).2.2.1

lemma isCompact_compl_constructibleSeparation_snd :
    IsCompact (constructibleSeparation h₁ h₂ hd).2ᶜ :=
  (constructibleSeparation_spec_compl h₁ h₂ hd).2.2.2.1

lemma subset_constructibleSeparation_fst : T₁ ⊆ (constructibleSeparation h₁ h₂ hd).1 :=
  disjoint_compl_left_iff_subset.mp
    (constructibleSeparation_spec_compl h₁ h₂ hd).2.2.2.2.1

lemma subset_constructibleSeparation_snd : T₂ ⊆ (constructibleSeparation h₁ h₂ hd).2 :=
  disjoint_compl_left_iff_subset.mp
    (constructibleSeparation_spec_compl h₁ h₂ hd).2.2.2.2.2.1

lemma disjoint_constructibleSeparation :
    Disjoint (constructibleSeparation h₁ h₂ hd).1 (constructibleSeparation h₁ h₂ hd).2 := by
  rw [disjoint_iff_inter_eq_empty, ← compl_compl ((constructibleSeparation h₁ h₂ hd).1 ∩ _),
    compl_inter, (constructibleSeparation_spec_compl h₁ h₂ hd).2.2.2.2.2.2, compl_univ]

/-- **Properties of the constructible separation data** (blueprint:
`lemma-extending-isomorphism-over-closure-closed--1`): in a compact quasi-separated prespectral
space (for instance a spectral space), the separation data `(T₁_c, T₂_c)` are closed and
constructible, contain `T₁` resp. `T₂`, and are disjoint. Complements of compact opens are
constructible since compact opens of a quasi-separated space are retrocompact. -/
theorem constructibleSeparation_spec [QuasiSeparatedSpace X] :
    IsClosed (constructibleSeparation h₁ h₂ hd).1 ∧
      Topology.IsConstructible (constructibleSeparation h₁ h₂ hd).1 ∧
      IsClosed (constructibleSeparation h₁ h₂ hd).2 ∧
      Topology.IsConstructible (constructibleSeparation h₁ h₂ hd).2 ∧
      T₁ ⊆ (constructibleSeparation h₁ h₂ hd).1 ∧ T₂ ⊆ (constructibleSeparation h₁ h₂ hd).2 ∧
      Disjoint (constructibleSeparation h₁ h₂ hd).1 (constructibleSeparation h₁ h₂ hd).2 := by
  obtain ⟨ho₁, ho₂, hc₁, hc₂, -⟩ := constructibleSeparation_spec_compl h₁ h₂ hd
  exact ⟨isClosed_constructibleSeparation_fst h₁ h₂ hd,
    Topology.isConstructible_compl.mp (hc₁.isConstructible ho₁),
    isClosed_constructibleSeparation_snd h₁ h₂ hd,
    Topology.isConstructible_compl.mp (hc₂.isConstructible ho₂),
    subset_constructibleSeparation_fst h₁ h₂ hd, subset_constructibleSeparation_snd h₁ h₂ hd,
    disjoint_constructibleSeparation h₁ h₂ hd⟩


end PrespectralSpace
