/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension
public import WeilConjectures.AlgebraicGeometry.GenericFiber.ProjectiveCoordinate
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Cover
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Deligne.Statement

/-!
# The first step of Deligne's generic constructibility: a good locus with finite complement

Let `b : Y ⟶ S` be proper, covered by finitely many opens `Yα` with closed immersions
`eα : Yα ⟶ 𝔸^{σα}_S` over `S`, and let `j : X ⟶ Y` be an immersion whose generic fibre has
dimension `≤ n`. Granting the generic constructibility theorem in generic dimension `< n`, apply
it to each coordinate `t_{αr} : Yα ⟶ 𝔸¹_S` over the base `𝔸¹_S`: the generic fibre of
`X ∩ Yα` over `𝔸¹_S` has dimension `< n` (`lemma-coordinate-projections--1`). This gives
dense opens `V_{αr} ⊆ 𝔸¹_S`, over whose preimages `G_{αr} ⊆ Yα` the direct image is bounded
constructible and commutes with every base change from `S`. Their union `G` has the same property
(`AlgebraicGeometry.Etale.HasDirectImageBaseChangeOnPlus.of_cover`), and its complement is finite
over a nonempty open of `S` (`lemma-coordinate-projections--2`). This is
`AlgebraicGeometry.Etale.exists_hasDirectImageBaseChangeOnPlus_of_coordinates`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- In `WithBot ℕ∞`, `x + 1 ≤ y < n + 1` implies `x < n`. -/
lemma WithBot.ENat.lt_of_add_one_le_of_lt {x y : WithBot ℕ∞} {n : ℕ} (h₁ : x + 1 ≤ y)
    (h₂ : y < (n + 1 : ℕ)) : x < n := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe x =>
    induction y using WithBot.recBotCoe with
    | bot => exact absurd h₁ (by simp)
    | coe y =>
      have h₁' : x + 1 ≤ y := by exact_mod_cast h₁
      have h₂' : y < (n + 1 : ℕ) := by exact_mod_cast h₂
      have : x + 1 < (n : ℕ∞) + 1 := by
        rw [← Nat.cast_one, ← Nat.cast_add] at *
        exact h₁'.trans_lt h₂'
      have hx : x < n := by
        rwa [ENat.add_lt_add_iff_right ENat.one_ne_top] at this
      exact_mod_cast hx

/-- **The first step of Deligne's generic constructibility**: let `S` be integral of finite type
over a field, `b : Y ⟶ S` proper, covered by finitely many opens `Yα` with closed immersions
`eα : Yα ⟶ 𝔸^{σα}_S` over `S`, and `j : X ⟶ Y` an immersion with generic fibre of dimension
`< n + 1`. If the generic constructibility theorem holds in generic dimension `< n`, then for a
constructible sheaf `F` on `X` there is an open `G ⊆ Y` over which `Rj_* F` is bounded
constructible and commutes with every base change from a noetherian scheme, whose complement is
finite over a nonempty open `W ⊆ S`. -/
theorem exists_hasDirectImageBaseChangeOnPlus_of_coordinates {n : ℕ}
    (hQ : DeligneStatement Λ n) {k : Type u} [Field k] {S Y X : Scheme.{u}} [IsIntegral S]
    (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    [HasInvertibleExponent Λ S] (b : Y ⟶ S) [IsProper b] (j : X ⟶ Y) [IsImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hdim : genericFiberDim (j ≫ b) < (n + 1 : ℕ)) {ι : Type u} [Finite ι] (Uα : ι → Y.Opens)
    (hU : ⨆ α, Uα α = ⊤) (σ : ι → Type u) [∀ α, Finite (σ α)]
    (e : ∀ α, (Uα α).toScheme ⟶ 𝔸(σ α; S)) [∀ α, IsClosedImmersion (e α)]
    (he : ∀ α, e α ≫ 𝔸(σ α; S) ↘ S = (Uα α).ι ≫ b) :
    ∃ (G : Y.Opens) (W : S.Opens), (W : Set S).Nonempty ∧
      HasDirectImageBaseChangeOnPlus Λ (G.ι ≫ b) (j ∣_ G)
        ((((j ⁻¹ᵁ G).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)) Set.univ ∧
      ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i],
        Set.range i ⊆ (G : Set Y)ᶜ → IsFinite ((i ≫ b) ∣_ W) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (b ≫ aS)
  -- the coordinates
  let t (α : ι) (r : σ α) : (Uα α).toScheme ⟶ 𝔸(PUnit; S) :=
    e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S
  have ht (α : ι) (r : σ α) : t α r ≫ 𝔸(PUnit; S) ↘ S = (Uα α).ι ≫ b := by
    simp [t, he]
  have : ∀ α r, LocallyOfFiniteType (t α r) := fun α r ↦ by
    have : LocallyOfFiniteType (t α r ≫ 𝔸(PUnit; S) ↘ S) := by rw [ht]; infer_instance
    exact locallyOfFiniteType_of_comp _ (𝔸(PUnit; S) ↘ S)
  have : ∀ α r, QuasiCompact (t α r) := fun α r ↦ by
    have : QuasiCompact (t α r ≫ 𝔸(PUnit; S) ↘ S) := by rw [ht]; infer_instance
    exact QuasiCompact.of_comp _ (𝔸(PUnit; S) ↘ S)
  have : HasInvertibleExponent Λ 𝔸(PUnit; S) := HasInvertibleExponent.of_hom (𝔸(PUnit; S) ↘ S)
  -- the induction hypothesis over `𝔸¹_S`, for each coordinate
  have hV : ∀ α r, ∃ V : 𝔸(PUnit; S).Opens, (V : Set 𝔸(PUnit; S)).Nonempty ∧
      HasDirectImageBaseChangeOnPlus Λ (t α r) (j ∣_ Uα α)
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (j ⁻¹ᵁ Uα α).ι).obj F)) V := by
    intro α r
    have := IsConstructibleSheaf.upperStar (j ⁻¹ᵁ Uα α).ι F
    refine hQ ((𝔸(PUnit; S) ↘ S) ≫ aS) (t α r) (j ∣_ Uα α) _ ?_
    have h₁ := topologicalKrullDim_fiber_genericPoint_add_one_le
      ((j ∣_ Uα α) ≫ (Uα α).ι ≫ b) ((j ∣_ Uα α) ≫ t α r) (by simp [ht])
    have h₂ : genericFiberDim ((j ∣_ Uα α) ≫ (Uα α).ι ≫ b) ≤ genericFiberDim (j ≫ b) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
      exact genericFiberDim_comp_le _ _
    exact WithBot.ENat.lt_of_add_one_le_of_lt h₁ (h₂.trans_lt hdim)
  choose V hVne hVP using hV
  -- the open `G`
  let G : Y.Opens := ⨆ (p : Σ α, σ α), (Uα p.1).ι ''ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)
  have hGset : (G : Set Y) = ⋃ (α : ι) (r : σ α), (Uα α).ι ''
      ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹' (V α r : Set 𝔸(PUnit; S))) := by
    simp only [G, TopologicalSpace.Opens.coe_iSup, Scheme.Hom.coe_image, Set.iUnion_sigma]
    rfl
  obtain ⟨W, hWne, hW⟩ := exists_isFinite_morphismRestrict_of_range_subset b Uα hU σ e he V
    hVne
  refine ⟨G, W, hWne, ?_, fun Z i _ hi ↦ hW Z i (hGset ▸ hi)⟩
  -- the property over `G`, from the cover by the `G_{αr}`
  have hle (p : Σ α, σ α) : Set.range ((t p.1 p.2 ⁻¹ᵁ V p.1 p.2).ι ≫ (Uα p.1).ι) ⊆
      Set.range G.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    apply le_iSup (fun p : Σ α, σ α ↦ (Uα p.1).ι ''ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)) p
    exact ⟨(t p.1 p.2 ⁻¹ᵁ V p.1 p.2).ι x, x.2, rfl⟩
  let a (p : Σ α, σ α) : (t p.1 p.2 ⁻¹ᵁ V p.1 p.2).toScheme ⟶ G :=
    IsOpenImmersion.lift G.ι _ (hle p)
  have ha (p : Σ α, σ α) : a p ≫ G.ι = (t p.1 p.2 ⁻¹ᵁ V p.1 p.2).ι ≫ (Uα p.1).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have : ∀ p, IsOpenImmersion (a p) := fun p ↦ by
    have : IsOpenImmersion (a p ≫ G.ι) := by rw [ha]; infer_instance
    exact IsOpenImmersion.of_comp (a p) G.ι
  let Xi (p : Σ α, σ α) := ((j ∣_ Uα p.1) ⁻¹ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).toScheme
  have heq (p : Σ α, σ α) :
      (((j ∣_ Uα p.1) ⁻¹ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).ι ≫ (j ⁻¹ᵁ Uα p.1).ι) ≫ j =
        ((j ∣_ Uα p.1) ∣_ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)) ≫ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2).ι ≫
          (Uα p.1).ι := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, ← morphismRestrict_ι,
      Category.assoc]
  have hleX (p : Σ α, σ α) : Set.range
      (((j ∣_ Uα p.1) ⁻¹ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).ι ≫ (j ⁻¹ᵁ Uα p.1).ι) ⊆
      Set.range (j ⁻¹ᵁ G).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    change j _ ∈ G
    rw [← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
    have := hle p ⟨((j ∣_ Uα p.1) ∣_ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)) x, rfl⟩
    rwa [Opens.range_ι] at this
  let bX (p : Σ α, σ α) : Xi p ⟶ (j ⁻¹ᵁ G).toScheme := IsOpenImmersion.lift _ _ (hleX p)
  have hbX (p : Σ α, σ α) : bX p ≫ (j ⁻¹ᵁ G).ι =
      ((j ∣_ Uα p.1) ⁻¹ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).ι ≫ (j ⁻¹ᵁ Uα p.1).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hRG : IsPullback (j ⁻¹ᵁ G).ι (j ∣_ G) j G.ι := (isPullback_morphismRestrict j G).flip
  have hb (p : Σ α, σ α) : IsPullback (bX p) ((j ∣_ Uα p.1) ∣_ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2))
      (j ∣_ G) (a p) := by
    refine IsPullback.of_right ?_ ?_ hRG
    · rw [hbX, ha]
      exact (isPullback_morphismRestrict (j ∣_ Uα p.1) (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).flip.paste_horiz
        (isPullback_morphismRestrict j (Uα p.1)).flip
    · rw [← cancel_mono G.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hbX,
        Category.assoc, Category.assoc, ha, ← Category.assoc _ (j ⁻¹ᵁ Uα p.1).ι j, heq]
  have : LocallyOfFiniteType (G.ι ≫ b) := inferInstance
  refine HasDirectImageBaseChangeOnPlus.of_cover (j ∣_ G) a (fun g ↦ ?_) bX _ hb
    (Ki := fun p ↦ (((((j ∣_ Uα p.1) ⁻¹ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).ι)^*[ModuleCat.{u + 1} Λ]
      ).mapDerivedCategoryPlus.obj ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (j ⁻¹ᵁ Uα p.1).ι).obj F)))) (fun p ↦ ?_)
    (fun p ↦ ?_)
  · obtain ⟨q, hq⟩ := (TopologicalSpace.Opens.mem_iSup).1 g.2
    obtain ⟨y, hy, hyg⟩ := hq
    refine ⟨q, ⟨y, hy⟩, G.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ha]
    exact hyg
  · let eF := ((((j ⁻¹ᵁ Uα p.1).ι)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
      0).symm.app F
    exact (((((j ∣_ Uα p.1) ⁻¹ᵁ (t p.1 p.2 ⁻¹ᵁ V p.1 p.2)).ι)^*[ModuleCat.{u + 1} Λ]
      ).mapDerivedCategoryPlus.mapIso eF) ≪≫
      ((upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) _ (j ⁻¹ᵁ Uα p.1).ι).app _).symm ≪≫
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (bX p) (j ⁻¹ᵁ G).ι _ (hbX p).symm).app _
  · have h := HasDirectImageBaseChangeOnPlus.restrict_of_base (𝔸(PUnit; S) ↘ S) (t p.1 p.2)
      (j ∣_ Uα p.1) (V p.1 p.2) (hVP p.1 p.2) Set.univ
    have hfY : a p ≫ G.ι ≫ b = (t p.1 p.2 ⁻¹ᵁ V p.1 p.2).ι ≫ t p.1 p.2 ≫ 𝔸(PUnit; S) ↘ S := by
      rw [ht, ← Category.assoc, ha, Category.assoc]
    rw [hfY]
    exact h

end Etale

end AlgebraicGeometry
