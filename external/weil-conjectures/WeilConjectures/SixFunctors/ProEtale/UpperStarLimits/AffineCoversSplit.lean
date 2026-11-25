/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.IdempotentBasicOpen
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Schemes over which weakly étale covers by affines split

A scheme `X` has *split affine covers* (`AlgebraicGeometry.Scheme.AffineCoversSplit`) if every
surjective weakly étale morphism from an affine scheme to `X` has a section. For example, the
spectrum of a ring all of whose faithfully flat ind-étale algebras have a retraction (e.g. a
w-contractible ring) has split affine covers.

- `AlgebraicGeometry.Scheme.AffineCoversSplit.exists_retraction`: conversely, if `Spec R` has
  split affine covers, every faithfully flat ind-étale `R`-algebra has a retraction.
- `AlgebraicGeometry.Scheme.AffineCoversSplit.exists_factorization`: a morphism from an affine
  scheme with split affine covers to any scheme `W` factors through a weakly étale morphism
  from an affine scheme to `W` (a finite disjoint union of affine opens of `W`).
- `AlgebraicGeometry.Scheme.AffineCoversSplit.isAffineOpen_of_isClopen`,
  `AlgebraicGeometry.Scheme.AffineCoversSplit.of_isClopen`: an open and closed subscheme of an
  affine scheme with split affine covers is affine, with split affine covers.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` has split affine covers if every surjective weakly étale morphism from an
affine scheme to `X` has a section. -/
def AffineCoversSplit (X : Scheme.{u}) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ [IsAffine T] (p : T ⟶ X) [WeaklyEtale p] [Surjective p],
    ∃ s : X ⟶ T, s ≫ p = 𝟙 X

/-- The spectrum of a ring all of whose faithfully flat ind-étale algebras have a retraction has
split affine covers. -/
lemma affineCoversSplit_Spec {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R) :
    AffineCoversSplit (Spec R) :=
  fun _ _ p _ _ ↦ exists_comp_eq_id_of_forall_exists_retraction hR p

namespace AffineCoversSplit

/-- Having split affine covers is invariant under isomorphisms. -/
lemma of_iso {X X' : Scheme.{u}} (e : X ≅ X') (h : AffineCoversSplit X) :
    AffineCoversSplit X' := by
  intro T _ p _ _
  obtain ⟨s, hs⟩ := h (p ≫ e.inv)
  refine ⟨e.inv ≫ s, ?_⟩
  rw [← cancel_mono e.inv, Category.assoc, Category.assoc, hs]
  simp

/-- If `Spec R` has split affine covers, every faithfully flat ind-étale `R`-algebra has a
retraction. -/
lemma exists_retraction {R : CommRingCat.{u}} (h : AffineCoversSplit (Spec R))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
    [Module.FaithfullyFlat R T] : ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R := by
  let φ : R ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap R T)
  have : WeaklyEtale (Spec.map φ) := weaklyEtale_SpecMap_algebraMap_iff.2 inferInstance
  have : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).2 (RingHom.faithfullyFlat_algebraMap_iff.2 ‹_›)).2
  obtain ⟨s, hs⟩ := h (Spec.map φ)
  have hφ : φ ≫ Spec.preimage s = 𝟙 R :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, hs, Spec.map_id])
  exact ⟨(Spec.preimage s).hom, congrArg CommRingCat.Hom.hom hφ⟩

/-- **Factorization through an affine weakly étale scheme.** A morphism `φ : X ⟶ W` from an
affine scheme `X` with split affine covers factors as `X ⟶ T ⟶ W` with `T` affine and
`T ⟶ W` weakly étale (in fact a finite disjoint union of affine opens of `W`): cover `X` by
finitely many affine opens mapping into affine opens of `W`, and split this cover. -/
lemma exists_factorization {X W : Scheme.{u}} [IsAffine X] (hX : AffineCoversSplit X)
    (φ : X ⟶ W) :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (a : X ⟶ T) (b : T ⟶ W), WeaklyEtale b ∧ a ≫ b = φ := by
  let 𝒰 : X.OpenCover := W.affineCover.pullback₁ φ
  obtain ⟨𝒱, f, _, _⟩ := QuasiCompactCover.exists_hom.{u} 𝒰
  let v (j : 𝒱.I₀) : Spec (𝒱.X j) ⟶ X := 𝒱.f j
  have : WeaklyEtale (Sigma.desc v) := IsZariskiLocalAtSource.sigmaDesc fun j ↦ inferInstance
  have : Surjective (Sigma.desc v) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x ↦ ?_)
    exact Set.mem_iUnion.2 ⟨𝒱.idx x, 𝒱.covers x⟩
  obtain ⟨s, hs⟩ := hX (Sigma.desc v)
  let c (j : 𝒱.I₀) : Spec (𝒱.X j) ⟶ W.affineCover.X (f.s₀ j) :=
    f.h₀ j ≫ pullback.snd φ (W.affineCover.f (f.s₀ j))
  let b : (∐ fun j ↦ W.affineCover.X (f.s₀ j)) ⟶ W :=
    Sigma.desc fun j ↦ W.affineCover.f (f.s₀ j)
  have hb : WeaklyEtale b := IsZariskiLocalAtSource.sigmaDesc fun j ↦ inferInstance
  have hc : Limits.Sigma.map c ≫ b = Sigma.desc v ≫ φ := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp only [b, c, v, Sigma.ι_map_assoc, Sigma.ι_comp_desc,
      Sigma.ι_comp_desc_assoc, Category.assoc]
    rw [← pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ φ) (f.w₀ j)
  refine ⟨_, inferInstance, s ≫ Limits.Sigma.map c, b, hb, ?_⟩
  rw [Category.assoc, hc, ← Category.assoc, hs, Category.id_comp]

variable {X : Scheme.{u}}

/-- An open and closed subset of an affine scheme is an affine open: it is the basic open of an
idempotent. -/
lemma isAffineOpen_of_isClopen [IsAffine X] {O : X.Opens} (hO : IsClopen (O : Set X)) :
    IsAffineOpen O := by
  obtain ⟨e, -, he⟩ := exists_isIdempotentElem_basicOpen_eq hO
  have : O = X.basicOpen e := SetLike.ext' he.symm
  rw [this]
  exact (isAffineOpen_top X).basicOpen e

/-- An open and closed subscheme `O` of an affine scheme `X` with split affine covers has split
affine covers: a surjective weakly étale `T ⟶ O` with `T` affine extends to the surjective weakly
étale `T ⨿ (X ∖ O) ⟶ X`, and a section of the latter maps `O` into `T`. -/
lemma of_isClopen [IsAffine X] (hX : AffineCoversSplit X) {O : X.Opens}
    (hO : IsClopen (O : Set X)) : AffineCoversSplit O := by
  intro T _ p _ _
  let O' : X.Opens := ⟨(O : Set X)ᶜ, hO.isClosed.isOpen_compl⟩
  have : IsAffine O' := isAffineOpen_of_isClopen (O := O') hO.compl
  let q : T ⨿ O'.toScheme ⟶ X := coprod.desc (p ≫ O.ι) O'.ι
  have : WeaklyEtale q := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @WeaklyEtale)
      (coprodOpenCover.{_, 0} T O'.toScheme)]
    rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    · change WeaklyEtale (coprod.inl ≫ q)
      rw [coprod.inl_desc]
      infer_instance
    · change WeaklyEtale (coprod.inr ≫ q)
      rw [coprod.inr_desc]
      infer_instance
  have : Surjective q := by
    refine ⟨fun x ↦ ?_⟩
    by_cases hx : x ∈ O
    · obtain ⟨y, hy⟩ := p.surjective ⟨x, hx⟩
      refine ⟨(coprod.inl : T ⟶ T ⨿ O'.toScheme) y, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inl_desc, Scheme.Hom.comp_apply, hy]
      rfl
    · refine ⟨(coprod.inr : O'.toScheme ⟶ T ⨿ O'.toScheme) ⟨x, hx⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, coprod.inr_desc]
      rfl
  obtain ⟨s, hs⟩ := hX q
  have hrange : Set.range (O.ι ≫ s) ⊆ Set.range (coprod.inl : T ⟶ T ⨿ O'.toScheme) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z | z, hz⟩ := (coprodMk T O'.toScheme).surjective ((O.ι ≫ s) y)
    · exact ⟨z, by rw [← coprodMk_inl, hz]⟩
    · exfalso
      have h₁ : q ((O.ι ≫ s) y) = O.ι y := by
        rw [← Scheme.Hom.comp_apply, Category.assoc, hs, Category.comp_id]
      rw [← hz, coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc] at h₁
      have h₂ : O'.ι z ∈ O' := (Scheme.Opens.range_ι O').subset ⟨z, rfl⟩
      have h₃ : O.ι y ∈ O := (Scheme.Opens.range_ι O).subset ⟨y, rfl⟩
      rw [h₁] at h₂
      exact h₂ h₃
  refine ⟨IsOpenImmersion.lift coprod.inl (O.ι ≫ s) hrange, ?_⟩
  rw [← cancel_mono O.ι, Category.assoc, Category.id_comp]
  have : p ≫ O.ι = coprod.inl ≫ q := (coprod.inl_desc _ _).symm
  rw [this, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hs, Category.comp_id]

end AffineCoversSplit

end AlgebraicGeometry.Scheme
