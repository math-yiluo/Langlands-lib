/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusExistence
public import WeilConjectures.TraceFormula.FibreModel

/-!

# Open–closed decompositions of a model

Let `Φ` be the model Frobenius of a model `X₀` of `X = X₀ ×_{k₀} k` over a finite field `k₀`.
For an affine open `U₀ ⊆ X₀` with reduced closed complement `Z₀`, the base changes `U` and `Z`
of `U₀` and `Z₀` are an open subscheme of `X` and its closed complement, both stable under `Φ`,
with the model Frobenii of `U₀` and `Z₀` (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 5). The complement `Z₀` is covered by one
affine open fewer than `X₀`.

## Main results

- `ProEtale.CondensedRing.IsModelFrobenius.exists_finset_isAffineOpen`: the model of a
  quasi-compact `X` is covered by finitely many affine opens.
- `ProEtale.CondensedRing.isProper_hom_of_card_eq_zero`: if the model is covered by
  no affine open, `X` is empty, hence proper.
- `ProEtale.CondensedRing.IsModelFrobenius.exists_isCompl`: the open–closed decomposition along
  an affine open of the model.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

/-- A finite open cover `s` of `n + 1` opens of a space can be shrunk to `n` of its members `t`
together with one further open `U`, which is either `⊥` or a member of `s`, such that the
members of `t` stay distinct outside `U`: if some member of `s` is redundant, drop it and take
`U = ⊥`; otherwise every member has a point lying in no other member, and one may take for `U`
any member of `s`. -/
lemma exists_finset_card_add_one_eq {α : Type*} [TopologicalSpace α] {s : Finset (Opens α)}
    (hs : s.Nonempty) (hcov : ⨆ U ∈ s, U = ⊤) :
    ∃ U, (U = ⊥ ∨ U ∈ s) ∧ ∃ t ⊆ s, t.card + 1 = s.card ∧ U ⊔ ⨆ V ∈ t, V = ⊤ ∧
      Set.InjOn (fun V : Opens α ↦ (V : Set α) \ U) t := by
  classical
  by_cases h : ∃ V ∈ s, ⨆ W ∈ s.erase V, W = ⊤
  · obtain ⟨V, hV, hV'⟩ := h
    refine ⟨⊥, Or.inl rfl, s.erase V, Finset.erase_subset _ _,
      Finset.card_erase_add_one hV, by rw [hV', bot_sup_eq], fun V₁ _ V₂ _ h ↦ ?_⟩
    simpa using h
  · simp only [not_exists, not_and] at h
    obtain ⟨V₀, hV₀⟩ := hs
    refine ⟨V₀, Or.inr hV₀, s.erase V₀, Finset.erase_subset _ _,
      Finset.card_erase_add_one hV₀, ?_, fun V₁ hV₁ V₂ hV₂ hV ↦ ?_⟩
    · have h₁ := Finset.iSup_insert V₀ (s.erase V₀) fun V : Opens α ↦ V
      beta_reduce at h₁
      rw [Finset.insert_erase hV₀, hcov] at h₁
      exact h₁.symm
    · by_contra hne
      obtain ⟨x, hx⟩ : ∃ x, x ∉ ⨆ W ∈ s.erase V₁, W := by
        by_contra! hx
        exact h V₁ (Finset.mem_of_mem_erase hV₁) (eq_top_iff.2 fun x _ ↦ hx x)
      have hxs : x ∈ ⨆ U ∈ s, U := by
        rw [hcov]
        trivial
      simp only [mem_iSup, Finset.mem_erase, ne_eq, not_exists] at hx hxs
      obtain ⟨W, hW, hxW⟩ := hxs
      obtain rfl : W = V₁ := by
        by_contra hWV
        exact hx W ⟨hWV, hW⟩ hxW
      have hx₀ : x ∉ V₀ := hx V₀ ⟨fun h ↦ (Finset.mem_erase.1 hV₁).1 h.symm, hV₀⟩
      have hx₂ : x ∈ (V₂ : Set α) \ V₀ := by
        rw [← show (W : Set α) \ V₀ = (V₂ : Set α) \ V₀ from hV]
        exact ⟨hxW, hx₀⟩
      exact hx V₂ ⟨Ne.symm hne, Finset.mem_of_mem_erase hV₂⟩ hx₂.1

end TopologicalSpace.Opens

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The projection `p : X ⟶ X₀` of a model is surjective: it is the base change of the
surjective morphism `Spec k ⟶ Spec k₀`. -/
lemma IsModelFrobenius.surjective {k : Type u} [Field k] {X : Over (Spec (.of k))} {Φ : X ⟶ X}
    {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} (hΦ : IsModelFrobenius Φ f₀ p) :
    Surjective p := by
  have : Unique (Spec (.of k₀)) := inferInstanceAs (Unique (PrimeSpectrum k₀))
  have : Nonempty (Spec (.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  exact MorphismProperty.of_isPullback hΦ.isPullback.flip ⟨Function.surjective_to_subsingleton _⟩

/-- Let `Φ` be the model Frobenius of a model `X₀` of `X`. For a morphism `i₀ : W₀ ⟶ X₀`, the
base change `W = W₀ ×_{X₀} X` of `i₀` along `p`, an object over `Spec k`, carries the
restriction `Φ_W` of `Φ`, which is the model Frobenius of the model `W₀` over `k₀`. -/
theorem IsModelFrobenius.exists_isModelFrobenius_pullback {k : Type u} [Field k]
    {X : Over (Spec (.of k))} {Φ : X ⟶ X} {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p) {W₀ : Scheme.{u}} (i₀ : W₀ ⟶ X₀) :
    ∃ ΦW : Over.mk (pullback.snd i₀ p ≫ X.hom) ⟶ Over.mk (pullback.snd i₀ p ≫ X.hom),
      ΦW ≫ Over.homMk (pullback.snd i₀ p) rfl = Over.homMk (pullback.snd i₀ p) rfl ≫ Φ ∧
        IsModelFrobenius ΦW (i₀ ≫ f₀) (pullback.fst i₀ p) := by
  obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
  obtain ⟨FW, hFW⟩ := (i₀ ≫ f₀).exists_isFrobenius
  have h : (pullback.fst i₀ p ≫ FW) ≫ i₀ = (pullback.snd i₀ p ≫ Φ.left) ≫ p := by
    rw [Category.assoc, ← hFW.comp_eq_comp (i₀ ≫ f₀) hF₀ i₀, pullback.condition_assoc,
      Category.assoc, hp]
  refine ⟨Over.homMk (pullback.lift _ _ h) ?_, ?_, ⟨?_, FW, hFW, pullback.lift_fst _ _ _⟩⟩
  · simp only [Over.mk_hom]
    rw [pullback.lift_snd_assoc, Category.assoc, Over.w Φ]
  · ext1
    exact pullback.lift_snd _ _ _
  · exact (IsPullback.of_hasPullback i₀ p).paste_vert hΦ.isPullback

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

omit [LocallyOfFiniteType X.hom] [IsSeparated X.hom] in
/-- The model `X₀` of a quasi-compact `X` is covered by finitely many affine opens: it is the
image of `X` under the surjective projection `p`. -/
theorem IsModelFrobenius.exists_finset_isAffineOpen (hΦ : IsModelFrobenius Φ f₀ p) :
    ∃ s : Finset X₀.Opens, (∀ U ∈ s, IsAffineOpen U) ∧ ⨆ U ∈ s, U = ⊤ := by
  classical
  have := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace X₀ := Function.Surjective.compactSpace p.continuous hΦ.surjective.surj
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X₀.affineOpens ↦ ((U : X₀.Opens) : Set X₀)) (fun U ↦ (U : X₀.Opens).isOpen)
    (fun x _ ↦ Set.mem_iUnion.2 (by
      obtain ⟨U, hU, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X₀.isBasis_affineOpens)
          (show x ∈ (⊤ : X₀.Opens) from trivial)
      exact ⟨⟨U, hU⟩, hxU⟩))
  refine ⟨t.image Subtype.val, fun U hU ↦ ?_, eq_top_iff.2 fun x _ ↦ ?_⟩
  · obtain ⟨V, -, rfl⟩ := Finset.mem_image.1 hU
    exact V.2
  · obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨U, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_image_of_mem _ hU, hxU⟩⟩

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [Finite k₀] in
/-- If a scheme `X₀` with a morphism `p : X ⟶ X₀` is covered by no affine open, it is empty, hence
so is `X`, and `X` is proper over `k`. -/
theorem isProper_hom_of_card_eq_zero (p : X.left ⟶ X₀)
    {s : Finset X₀.Opens} (hs : s.card = 0) (hcov : ⨆ U ∈ s, U = ⊤) : IsProper X.hom := by
  have h : (⊤ : X₀.Opens) = ⊥ := by
    rw [← hcov, Finset.card_eq_zero.1 hs]
    simp
  have : IsEmpty X₀ := ⟨fun x ↦ by
    have hx : x ∈ (⊤ : X₀.Opens) := trivial
    rw [h] at hx
    simp at hx⟩
  have : IsEmpty X.left := ⟨fun x ↦ isEmptyElim (p x)⟩
  infer_instance

/-- **Open–closed decomposition along an affine open of the model** (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 5): if the model `X₀` is covered by the
affine opens of a finite set `s` of `n + 1` elements, there are an open immersion `j : U ⟶ X` and
a closed immersion `i : Z ⟶ X` with complementary images, endomorphisms `Φ_U`, `Φ_Z` with
`Φ_U ≫ j = j ≫ Φ` and `Φ_Z ≫ i = i ≫ Φ` which are model Frobenii over `k₀`, the model of `U`
being affine and the model of `Z` being covered by `n` affine opens. -/
theorem IsModelFrobenius.exists_isCompl [IsAlgClosed k] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {n : ℕ} {s : Finset X₀.Opens} (hs : s.card = n + 1)
    (hsa : ∀ U ∈ s, IsAffineOpen U) (hcov : ⨆ U ∈ s, U = ⊤) :
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (Z : Over (Spec (.of k))) (_ : LocallyOfFiniteType Z.hom)
      (_ : QuasiCompact Z.hom) (_ : IsSeparated Z.hom) (j : U ⟶ X) (i : Z ⟶ X)
      (_ : IsOpenImmersion j.left) (_ : IsClosedImmersion i.left) (ΦU : U ⟶ U) (ΦZ : Z ⟶ Z)
      (U₀ : Scheme.{u}) (fU₀ : U₀ ⟶ Spec (.of k₀)) (pU : U.left ⟶ U₀)
      (Z₀ : Scheme.{u}) (fZ₀ : Z₀ ⟶ Spec (.of k₀)) (pZ : Z.left ⟶ Z₀)
      (t : Finset Z₀.Opens),
      ΦU ≫ j = j ≫ Φ ∧ ΦZ ≫ i = i ≫ Φ ∧
        IsCompl (Set.range j.left.base) (Set.range i.left.base) ∧
        IsAffine U₀ ∧ LocallyOfFiniteType fU₀ ∧ IsModelFrobenius ΦU fU₀ pU ∧
        LocallyOfFiniteType fZ₀ ∧ IsModelFrobenius ΦZ fZ₀ pZ ∧
        t.card = n ∧ (∀ V ∈ t, IsAffineOpen V) ∧ ⨆ V ∈ t, V = ⊤ := by
  classical
  obtain ⟨(U₀' : X₀.Opens), hU₀', t', ht's, ht'card, ht'cov, ht'inj⟩ :=
    TopologicalSpace.Opens.exists_finset_card_add_one_eq (Finset.card_pos.1 (by omega)) hcov
  have hU₀a : IsAffineOpen U₀' := by
    rcases hU₀' with rfl | h
    · exact isAffineOpen_bot X₀
    · exact hsa _ h
  have : IsAffine U₀' := hU₀a
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(U₀' : Set X₀)ᶜ, U₀'.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds X₀)
  have hrange : Set.range I.subschemeι = (U₀' : Set X₀)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨ΦU, hΦU, hU⟩ := hΦ.exists_isModelFrobenius_pullback U₀'.ι
  obtain ⟨ΦZ, hΦZ, hZ⟩ := hΦ.exists_isModelFrobenius_pullback I.subschemeι
  have : IsAffineHom p := MorphismProperty.of_isPullback hΦ.isPullback.flip inferInstance
  have : IsAffineHom (pullback.fst U₀'.ι p) := MorphismProperty.pullback_fst _ _ this
  have : IsAffine (pullback U₀'.ι p) := isAffine_of_isAffineHom (pullback.fst U₀'.ι p)
  have key (W : X₀.Opens) : (W : Set X₀) \ U₀' =
      I.subschemeι '' ((I.subschemeι ⁻¹ᵁ W : I.subscheme.Opens) : Set I.subscheme) := by
    rw [Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range, hrange, Set.sdiff_eq]
  refine ⟨Over.mk (pullback.snd U₀'.ι p ≫ X.hom),
    inferInstanceAs (LocallyOfFiniteType (pullback.snd U₀'.ι p ≫ X.hom)),
    inferInstanceAs (QuasiCompact (pullback.snd U₀'.ι p ≫ X.hom)),
    inferInstanceAs (IsSeparated (pullback.snd U₀'.ι p ≫ X.hom)),
    Over.mk (pullback.snd I.subschemeι p ≫ X.hom),
    inferInstanceAs (LocallyOfFiniteType (pullback.snd I.subschemeι p ≫ X.hom)),
    inferInstanceAs (QuasiCompact (pullback.snd I.subschemeι p ≫ X.hom)),
    inferInstanceAs (IsSeparated (pullback.snd I.subschemeι p ≫ X.hom)),
    Over.homMk (pullback.snd U₀'.ι p) rfl, Over.homMk (pullback.snd I.subschemeι p) rfl,
    inferInstanceAs (IsOpenImmersion (pullback.snd U₀'.ι p)),
    inferInstanceAs (IsClosedImmersion (pullback.snd I.subschemeι p)),
    ΦU, ΦZ, U₀', U₀'.ι ≫ f₀, pullback.fst _ _, I.subscheme, I.subschemeι ≫ f₀, pullback.fst _ _,
    t'.image fun V ↦ I.subschemeι ⁻¹ᵁ V, hΦU, hΦZ, ?_, hU₀a, inferInstance, hU, inferInstance,
    hZ, ?_, ?_, ?_⟩
  · have h₁ := Scheme.Pullback.range_snd U₀'.ι p
    have h₂ := Scheme.Pullback.range_snd I.subschemeι p
    rw [Scheme.Opens.range_ι] at h₁
    rw [hrange] at h₂
    erw [h₁, h₂]
    rw [Set.preimage_compl]
    exact isCompl_compl
  · rw [Finset.card_image_of_injOn fun V hV V' hV' h ↦ ht'inj hV hV' (by
      beta_reduce
      rw [key, key, h])]
    omega
  · intro V hV
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hV
    exact (hsa W (ht's hW)).preimage I.subschemeι
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have hz : I.subschemeι z ∈ U₀' ⊔ ⨆ V ∈ t', V := by
      rw [ht'cov]
      trivial
    have hzU : I.subschemeι z ∉ U₀' := by
      have hz' : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
      rw [hrange] at hz'
      exact hz'
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1
      ((TopologicalSpace.Opens.mem_sup.1 hz).resolve_left hzU)
    obtain ⟨hVt, hzV⟩ := TopologicalSpace.Opens.mem_iSup.1 hV
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨I.subschemeι ⁻¹ᵁ V, TopologicalSpace.Opens.mem_iSup.2 ⟨Finset.mem_image_of_mem _ hVt, hzV⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
