/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.LisseLocus

/-!
# Fourier inversion: definitions

The Artin–Schreier sheaf `ℒ_{ψ,a}` of a function `a`
(`AlgebraicGeometry.artinSchreierOf`) and the triple product `𝔸³` with points `(x, ξ, y)`
(`AlgebraicGeometry.affineTripleProduct`) with its projections, used in the proof that the
Fourier–Deligne transform of Weil complexes is an equivalence (blueprint `sec-Fourier-inversion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section ArtinSchreierOf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀) in
/-- The morphism `X ⟶ 𝔸¹` over `k₀` defined by a global function `a ∈ Γ(X, 𝒪_X)`. -/
noncomputable def affineLine.homOfSection (a : Γ(X, ⊤)) : X ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (X ↘ Spec (CommRingCat.of k₀)) fun _ ↦ a

instance (a : Γ(X, ⊤)) :
    (affineLine.homOfSection k₀ a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

/-- The Artin–Schreier sheaf `ℒ_{ψ,a}` of a global function `a` on a `k₀`-scheme `X`: the
pullback of `ℒ_ψ` along `a : X ⟶ 𝔸¹` (blueprint `lemma-artin-schreier-character-sheaf--1`). -/
noncomputable def artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    WeilSheaf k₀ l X :=
  (WeilSheaf.upperStar (affineLine.homOfSection k₀ a)).obj (artinSchreier ψ 1)

omit [Finite k₀] in
/-- The function `x` defines the identity of the affine line. -/
theorem affineLine.homOfSection_coord :
    affineLine.homOfSection k₀ (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit) =
      𝟙 (affineLine k₀) := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [affineLine.homOfSection, AffineSpace.homOfVector_over, Category.id_comp]
  · rw [affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord]
    rfl

omit [Finite k₀] in
/-- The multiplication `μ : 𝔸² ⟶ 𝔸¹` is the morphism defined by the function `x y`. -/
theorem affinePlane.mul_eq_homOfSection :
    affinePlane.mul k₀ = affineLine.homOfSection k₀
      ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)) := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [affinePlane.mul, affineLine.homOfSection, AffineSpace.homOfVector_over]
  · rw [affinePlane.mul, affineLine.homOfSection, AffineSpace.homOfVector_appTop_coord]

/-- Unfolding `AlgebraicGeometry.artinSchreierOf`. Rewriting with this equation (rather than
unfolding the definition) keeps the kernel from unfolding the pullback functor. -/
theorem artinSchreierOf_eq (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    artinSchreierOf ψ a =
      (WeilSheaf.upperStar (affineLine.homOfSection k₀ a)).obj (artinSchreier ψ 1) :=
  rfl

/-- The Artin–Schreier sheaf of a function is lisse, as a pullback of a lisse sheaf. -/
theorem isLisse_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    (artinSchreierOf ψ a).IsLisse :=
  ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreier ψ 1)

end ArtinSchreierOf

section TripleProduct

variable (k₀) in
/-- The triple product `𝔸¹ ×_{k₀} 𝔸¹ ×_{k₀} 𝔸¹` with points `(x, ξ, y)`, realised as
`(𝔸¹ ×_{k₀} 𝔸¹) ×_{𝔸¹} (𝔸¹ ×_{k₀} 𝔸¹)` over the middle coordinate `ξ`. -/
noncomputable def affineTripleProduct : Scheme.{u} :=
  pullback (affinePlane.snd k₀) (affinePlane.fst k₀)

noncomputable instance : (affineTripleProduct k₀).Over (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.fst _ _ ≫ affinePlane k₀ ↘ Spec (CommRingCat.of k₀)⟩

variable (k₀) in
/-- The projection `r₁₂ : (x, ξ, y) ↦ (x, ξ)`. -/
noncomputable def affineTripleProduct.proj₁₂ : affineTripleProduct k₀ ⟶ affinePlane k₀ :=
  pullback.fst _ _

variable (k₀) in
/-- The projection `r₂₃ : (x, ξ, y) ↦ (ξ, y)`. -/
noncomputable def affineTripleProduct.proj₂₃ : affineTripleProduct k₀ ⟶ affinePlane k₀ :=
  pullback.snd _ _

variable (k₀) in
/-- The projection `r₁₃ : (x, ξ, y) ↦ (x, y)`. -/
noncomputable def affineTripleProduct.proj₁₃ : affineTripleProduct k₀ ⟶ affinePlane k₀ :=
  pullback.tripleProj₁₃ _ _ _

instance : (affineTripleProduct.proj₁₃ k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.tripleProj₁₃_fst_assoc _ _ _ _⟩

omit [Finite k₀] in
/-- The projection `r₁₃ : 𝔸³ ⟶ 𝔸²` is the trivial line bundle with fibre coordinate `ξ`:
the square `r₁₃, ξ` over `Spec k₀` is cartesian. -/
theorem affineTripleProduct.isPullback_proj₁₃ :
    IsPullback (affineTripleProduct.proj₁₃ k₀)
      (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀)
      (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
  have h := (pullback.isPullback_tripleShear_tripleProj₁₃
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (m := 𝟙 (affinePlane k₀))
    (k := affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) (Category.id_comp _)).flip.paste_vert
    (IsPullback.of_hasPullback _ _).flip
  rw [pullback.tripleShear_fst] at h
  exact (Category.id_comp (affinePlane k₀ ↘ Spec (CommRingCat.of k₀))) ▸ h

instance : IsSeparated (affineTripleProduct.proj₁₃ k₀) :=
  MorphismProperty.of_isPullback affineTripleProduct.isPullback_proj₁₃.flip inferInstance

instance : LocallyOfFiniteType (affineTripleProduct.proj₁₃ k₀) :=
  MorphismProperty.of_isPullback affineTripleProduct.isPullback_proj₁₃.flip inferInstance

instance : QuasiCompact (affineTripleProduct.proj₁₃ k₀) :=
  MorphismProperty.of_isPullback affineTripleProduct.isPullback_proj₁₃.flip inferInstance

instance : LocallyOfFiniteType (affineTripleProduct.proj₁₂ k₀) := by
  have : LocallyOfFiniteType (affinePlane.fst k₀) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact MorphismProperty.pullback_fst _ _ inferInstance

instance : LocallyOfFiniteType (affineTripleProduct k₀ ↘ Spec (CommRingCat.of k₀)) :=
  inferInstanceAs (LocallyOfFiniteType (affineTripleProduct.proj₁₂ k₀ ≫
    affinePlane k₀ ↘ Spec (CommRingCat.of k₀)))

end TripleProduct

end AlgebraicGeometry
