/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Filtered colimits of étale sheaves, stalk by stalk

A family of maps `σ i : A i ⟶ B` of modules indexed by a cofiltered category `I`, together with
transition maps `τ f : A j ⟶ A i` for `f : i ⟶ j`, presents `B` as the filtered colimit of the
`A i` *elementwise* (`ModuleCat.IsElementwiseColimit`) if every element of `B` comes from some
`A i` and every element of some `A i` which dies in `B` dies in some `A j`, `j ⟶ i`. Only the
compatibility of `σ` and `τ` is ever used, not the functoriality of `τ`.

For a cocone of étale sheaves of `Λ`-modules over a cofiltered diagram, being a colimit cocone
is the same as being an elementwise colimit on every geometric stalk
(`AlgebraicGeometry.Etale.isElementwiseColimit_sheafFiber_of_isColimit`,
`AlgebraicGeometry.Etale.isColimitOfIsElementwiseColimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace ModuleCat

variable {R : Type*} [Ring R]

/-- The family `σ i : A i ⟶ B` presents `B` as the filtered colimit of the `A i` along the
transition maps `τ`, elementwise: every element of `B` comes from some `A i`, and an element of
`A i` dying in `B` dies in some `A j` along a transition map. -/
def IsElementwiseColimit {I : Type*} [Category I] (A : I → ModuleCat R) (B : ModuleCat R)
    (σ : ∀ i, A i ⟶ B) (τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)) : Prop :=
  (∀ b : B, ∃ (i : I) (a : A i), (σ i).hom a = b) ∧
    ∀ (i : I) (a : A i), (σ i).hom a = 0 → ∃ (j : I) (f : j ⟶ i), (τ f).hom a = 0

namespace IsElementwiseColimit

variable {I : Type*} [Category I]

/-- **Elementwise colimits and cokernels.** Let `A' i ⟶ A'' i ⟶ A i ⟶ 0` be exact sequences
compatible with the transition maps, mapping compatibly to a sequence `B' ⟶ B'' ⟶ B ⟶ 0`
which is exact at `B''` and `B`. If `B'` and `B''` are the elementwise colimits of the `A' i` and
`A'' i`, then `B` is the elementwise colimit of the `A i`. -/
lemma of_cokernel [IsCofiltered I] {A' A'' A : I → ModuleCat R} {B' B'' B : ModuleCat R}
    {σ' : ∀ i, A' i ⟶ B'} {σ'' : ∀ i, A'' i ⟶ B''} {σ : ∀ i, A i ⟶ B}
    {τ' : ∀ {i j : I}, (i ⟶ j) → (A' j ⟶ A' i)} {τ'' : ∀ {i j : I}, (i ⟶ j) → (A'' j ⟶ A'' i)}
    {τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)}
    (r : ∀ i, A' i ⟶ A'' i) (rB : B' ⟶ B'') (d : ∀ i, A'' i ⟶ A i) (dB : B'' ⟶ B)
    (hr : ∀ i, r i ≫ σ'' i = σ' i ≫ rB) (hd : ∀ i, d i ≫ σ i = σ'' i ≫ dB)
    (hrτ : ∀ {i j : I} (f : i ⟶ j), τ' f ≫ r i = r j ≫ τ'' f)
    (hdτ : ∀ {i j : I} (f : i ⟶ j), τ'' f ≫ d i = d j ≫ τ f)
    (hσ' : ∀ {i j : I} (f : i ⟶ j), τ' f ≫ σ' i = σ' j)
    (hσ'' : ∀ {i j : I} (f : i ⟶ j), τ'' f ≫ σ'' i = σ'' j)
    (hτ'' : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), τ'' g ≫ τ'' f = τ'' (f ≫ g))
    (hrd : ∀ i x, (d i).hom ((r i).hom x) = 0)
    (hexB : ∀ y : B'', dB.hom y = 0 → ∃ z, rB.hom z = y)
    (hsurjB : Function.Surjective dB.hom) (hsurj : ∀ i, Function.Surjective (d i).hom)
    (h' : IsElementwiseColimit A' B' σ' τ') (h'' : IsElementwiseColimit A'' B'' σ'' τ'') :
    IsElementwiseColimit A B σ τ := by
  refine ⟨fun b ↦ ?_, fun i a ha ↦ ?_⟩
  · obtain ⟨b'', rfl⟩ := hsurjB b
    obtain ⟨i, a'', rfl⟩ := h''.1 b''
    exact ⟨i, (d i).hom a'', by rw [← ModuleCat.comp_apply, hd]; rfl⟩
  · obtain ⟨a'', rfl⟩ := hsurj i a
    have h0 : dB.hom ((σ'' i).hom a'') = 0 := by
      rw [← ModuleCat.comp_apply, ← hd]; exact ha
    obtain ⟨z', hz'⟩ := hexB _ h0
    obtain ⟨k, y, rfl⟩ := h'.1 z'
    let m := IsCofiltered.min i k
    have e1 : (σ'' m).hom ((τ'' (IsCofiltered.minToLeft i k)).hom a'') = (σ'' i).hom a'' := by
      rw [← ModuleCat.comp_apply, hσ'']
    have e2 : (σ'' m).hom ((r m).hom ((τ' (IsCofiltered.minToRight i k)).hom y)) =
        rB.hom ((σ' k).hom y) := by
      rw [← ModuleCat.comp_apply, hr, ModuleCat.comp_apply, ← ModuleCat.comp_apply (τ' _), hσ']
    have hm : (σ'' m).hom ((τ'' (IsCofiltered.minToLeft i k)).hom a'' -
        (r m).hom ((τ' (IsCofiltered.minToRight i k)).hom y)) = 0 := by
      rw [map_sub, e1, e2, hz', sub_self]
    obtain ⟨l, g, hg⟩ := h''.2 m _ hm
    refine ⟨l, g ≫ IsCofiltered.minToLeft i k, ?_⟩
    rw [map_sub, sub_eq_zero, ← ModuleCat.comp_apply, hτ'',
      ← ModuleCat.comp_apply, ← hrτ, ModuleCat.comp_apply] at hg
    rw [← ModuleCat.comp_apply, ← hdτ, ModuleCat.comp_apply, hg]
    exact hrd l _

/-- **Elementwise colimits and kernels.** Let `0 ⟶ A i ⟶ A' i ⟶ A'' i` be exact sequences
compatible with the transition maps, mapping compatibly to a sequence `B ⟶ B' ⟶ B''` whose first
map is injective. If `B'` and `B''` are the elementwise colimits of the `A' i` and `A'' i`, then
`B` is the elementwise colimit of the `A i`. -/
lemma of_kernel {A A' A'' : I → ModuleCat R} {B B' B'' : ModuleCat R}
    {σ : ∀ i, A i ⟶ B} {σ' : ∀ i, A' i ⟶ B'} {σ'' : ∀ i, A'' i ⟶ B''}
    {τ : ∀ {i j : I}, (i ⟶ j) → (A j ⟶ A i)} {τ' : ∀ {i j : I}, (i ⟶ j) → (A' j ⟶ A' i)}
    {τ'' : ∀ {i j : I}, (i ⟶ j) → (A'' j ⟶ A'' i)}
    (ι : ∀ i, A i ⟶ A' i) (ιB : B ⟶ B') (r : ∀ i, A' i ⟶ A'' i) (rB : B' ⟶ B'')
    (hι : ∀ i, ι i ≫ σ' i = σ i ≫ ιB) (hr : ∀ i, r i ≫ σ'' i = σ' i ≫ rB)
    (hιτ : ∀ {i j : I} (f : i ⟶ j), τ f ≫ ι i = ι j ≫ τ' f)
    (hrτ : ∀ {i j : I} (f : i ⟶ j), τ' f ≫ r i = r j ≫ τ'' f)
    (hσ' : ∀ {i j : I} (f : i ⟶ j), τ' f ≫ σ' i = σ' j)
    (hιB : Function.Injective ιB.hom) (hιi : ∀ i, Function.Injective (ι i).hom)
    (hrB : ∀ y, rB.hom (ιB.hom y) = 0)
    (hex : ∀ i (y : A' i), (r i).hom y = 0 → ∃ a, (ι i).hom a = y)
    (h' : IsElementwiseColimit A' B' σ' τ') (h'' : IsElementwiseColimit A'' B'' σ'' τ'') :
    IsElementwiseColimit A B σ τ := by
  refine ⟨fun b ↦ ?_, fun i a ha ↦ ?_⟩
  · obtain ⟨i, a', ha'⟩ := h'.1 (ιB.hom b)
    have h0 : (σ'' i).hom ((r i).hom a') = 0 := by
      rw [← ModuleCat.comp_apply, hr, ModuleCat.comp_apply, ha', hrB]
    obtain ⟨j, f, hf⟩ := h''.2 i _ h0
    rw [← ModuleCat.comp_apply, ← hrτ, ModuleCat.comp_apply] at hf
    obtain ⟨a, ha⟩ := hex j _ hf
    refine ⟨j, a, hιB ?_⟩
    rw [← ModuleCat.comp_apply, ← hι, ModuleCat.comp_apply, ha,
      ← ModuleCat.comp_apply, hσ', ha']
  · have h0 : (σ' i).hom ((ι i).hom a) = 0 := by
      rw [← ModuleCat.comp_apply, hι, ModuleCat.comp_apply, ha, map_zero]
    obtain ⟨j, f, hf⟩ := h'.2 i _ h0
    refine ⟨j, f, hιi j ?_⟩
    rw [← ModuleCat.comp_apply, hιτ, ModuleCat.comp_apply, hf, map_zero]

end IsElementwiseColimit

end ModuleCat

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- A colimit cocone of modules over the opposite of a cofiltered category is an elementwise
colimit. -/
lemma isElementwiseColimit_of_isColimit {F : Iᵒᵖ ⥤ ModuleCat.{u + 1} Λ} {c : Cocone F}
    (hc : IsColimit c) :
    ModuleCat.IsElementwiseColimit (fun i ↦ F.obj (op i)) c.pt (fun i ↦ c.ι.app (op i))
      (fun f ↦ F.map f.op) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  refine ⟨fun b ↦ ?_, fun i a ha ↦ ?_⟩
  · obtain ⟨⟨i⟩, a, rfl⟩ := Concrete.isColimit_exists_rep F hc b
    exact ⟨i, a, rfl⟩
  · have h : (c.ι.app (op i)).hom a = (c.ι.app (op i)).hom 0 := by rw [map_zero]; exact ha
    obtain ⟨⟨k⟩, f, g, hfg⟩ := (Concrete.isColimit_rep_eq_iff_exists F hc a 0).1 h
    refine ⟨k, f.unop, ?_⟩
    simpa using hfg

variable {X : Scheme.{u}}

/-- The geometric stalks of a colimit cocone of étale sheaves over the opposite of a cofiltered
category are elementwise colimits. -/
lemma isElementwiseColimit_sheafFiber_of_isColimit
    {F : Iᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {c : Cocone F}
    (hc : IsColimit c) (x : X) :
    ModuleCat.IsElementwiseColimit
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.obj (F.obj (op i)))
      ((X.uliftPointSmallEtale x).sheafFiber.obj c.pt)
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.map (c.ι.app (op i)))
      (fun f ↦ (X.uliftPointSmallEtale x).sheafFiber.map (F.map f.op)) :=
  isElementwiseColimit_of_isColimit (F := F ⋙ (X.uliftPointSmallEtale x).sheafFiber)
    (isColimitOfPreserves (X.uliftPointSmallEtale x).sheafFiber hc)

/-- A cocone of étale sheaves over the opposite of a cofiltered category which is an
elementwise colimit on every geometric stalk is a colimit cocone. -/
noncomputable def isColimitOfIsElementwiseColimit
    {F : Iᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (c : Cocone F)
    (h : ∀ x : X, ModuleCat.IsElementwiseColimit
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.obj (F.obj (op i)))
      ((X.uliftPointSmallEtale x).sheafFiber.obj c.pt)
      (fun i ↦ (X.uliftPointSmallEtale x).sheafFiber.map (c.ι.app (op i)))
      (fun f ↦ (X.uliftPointSmallEtale x).sheafFiber.map (F.map f.op))) :
    IsColimit c :=
  have : HasColimitsOfShape Iᵒᵖ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    Sheaf.instHasColimitsOfShape
  have : IsIso ((colimit.isColimit F).desc c) := Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ by
    have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have hc := isColimitOfPreserves (X.uliftPointSmallEtale x).sheafFiber (colimit.isColimit F)
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun z₁ z₂ hz ↦ ?_, fun b ↦ ?_⟩
    · rw [← sub_eq_zero] at hz ⊢
      rw [← map_sub] at hz
      obtain ⟨⟨i⟩, a, ha⟩ := Concrete.isColimit_exists_rep _ hc (z₁ - z₂)
      rw [← ha] at hz ⊢
      simp only [Functor.mapCocone_ι_app, colimit.cocone_ι] at hz ⊢
      erw [← ModuleCat.comp_apply, ← Functor.map_comp, colimit.isColimit_desc,
        colimit.ι_desc] at hz
      obtain ⟨j, f, hf⟩ := (h x).2 i a hz
      erw [← colimit.w F f.op, Functor.map_comp, ModuleCat.comp_apply, hf, map_zero]
    · obtain ⟨i, a, rfl⟩ := (h x).1 b
      refine ⟨((X.uliftPointSmallEtale x).sheafFiber.map (colimit.ι F (op i))).hom a, ?_⟩
      erw [← ModuleCat.comp_apply, ← Functor.map_comp, colimit.isColimit_desc,
        colimit.ι_desc]
  IsColimit.ofPointIso (colimit.isColimit F)

end AlgebraicGeometry.Etale
