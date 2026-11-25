/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing
public import WeilConjectures.WeilSheaf.FourierTraceAux

/-!
# Composition of kernel transforms of Weil complexes on the affine line

For a lisse Weil sheaf `𝒦` on `𝔸¹ ×_{k₀} 𝔸¹` and `a : ℤ`, the *kernel transform*
`Φ_𝒦(K) = Rpr₂!(pr₁^* K ⊗ 𝒦)[a]` of Weil complexes on the affine line
(`AlgebraicGeometry.WeilComplex.kernelTransform`); the Fourier–Deligne transform is the kernel
transform with kernel `μ^* ℒ_ψ` and shift `1`.

The composite of two kernel transforms is computed on the triple product `𝔸³` with points
`(x, ξ, y)` (blueprint `proposition-fourier-inversion`):

`Φ_{𝒦'}(Φ_𝒦(K)) ≅ Rr₃!(r₁^* K ⊗ r₁₂^* 𝒦 ⊗ r₂₃^* 𝒦')[a][b]`

(`AlgebraicGeometry.WeilComplex.nonempty_iso_kernelTransform_comp`), by compact-support base
change along `pr₁ : (ξ, y) ↦ ξ`, the projection formula for `r₂₃` and the composition laws of
pullbacks and compact-support direct images.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section TripleProduct

instance affineTripleProduct.isOver_proj₁₂ :
    (affineTripleProduct.proj₁₂ k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨rfl⟩

instance affineTripleProduct.isOver_proj₂₃ :
    (affineTripleProduct.proj₂₃ k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    have h : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
        affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
      pullback.condition.symm
    rw [← comp_over (affinePlane.fst k₀) (Spec (CommRingCat.of k₀)), reassoc_of% h,
      comp_over (affinePlane.snd k₀)]
    rfl⟩

end TripleProduct

/-- The *kernel transform* `Φ_𝒦(K) = Rpr₂!(pr₁^* K ⊗ 𝒦)[a]` of Weil complexes on the affine
line, for a lisse Weil sheaf `𝒦` on `𝔸¹ ×_{k₀} 𝔸¹` and a shift `a`
(blueprint `proposition-fourier-inversion`). -/
noncomputable def WeilComplex.kernelTransform (𝒦 : WeilSheaf k₀ l (affinePlane k₀))
    (h𝒦 : 𝒦.IsLisse) (a : ℤ) :
    WeilComplex k₀ l (affineLine k₀) ⥤ WeilComplex k₀ l (affineLine k₀) :=
  WeilComplex.upperStar (affinePlane.fst k₀) ⋙ WeilComplex.tensorLisse 𝒦 h𝒦 ⋙
    WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀) ⋙ shiftFunctor _ a

/-- The Fourier–Deligne transform is the kernel transform with kernel `μ^* ℒ_ψ` and shift `1`. -/
theorem fourierTransform_eq_kernelTransform (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierTransform ψ =
      WeilComplex.kernelTransform (fourierKernel ψ) (isLisse_fourierKernel ψ) 1 :=
  rfl

/-- **Composition of kernel transforms** (blueprint `proposition-fourier-inversion`). On the triple
product `𝔸³` with points `(x, ξ, y)`,

`Φ_{𝒦'}(Φ_𝒦(K)) ≅ Rr₃!(r₂₃^* 𝒦' ⊗ r₁₂^* 𝒦 ⊗ r₁^* K)[a][b]`

naturally in `K`, with `r₁ = r₁₃ ≫ pr₁` and `r₃ = r₁₃ ≫ pr₂`: compact-support base change along
`pr₁ : (ξ, y) ↦ ξ` (`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`)
gives `pr₁^* Rpr₂! ≅ Rr₂₃! r₁₂^*`, the projection formula for `r₂₃` moves `r₂₃^* 𝒦'` inside, and
`r₂₃ ≫ pr₂ = r₁₃ ≫ pr₂`, `r₁₂ ≫ pr₁ = r₁₃ ≫ pr₁` compose the pullbacks and direct images. -/
theorem WeilComplex.nonempty_iso_kernelTransform_comp (𝒦 𝒦' : WeilSheaf k₀ l (affinePlane k₀))
    (h𝒦 : 𝒦.IsLisse) (h𝒦' : 𝒦'.IsLisse) (a b : ℤ) :
    Nonempty (WeilComplex.kernelTransform 𝒦 h𝒦 a ⋙ WeilComplex.kernelTransform 𝒦' h𝒦' b ≅
      WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj 𝒦)
          (ProEtale.IsAdicLisseSheaf.upperStar _ h𝒦) ⋙
        WeilComplex.tensorLisse ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj 𝒦')
          (ProEtale.IsAdicLisseSheaf.upperStar _ h𝒦') ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀) ⋙
        shiftFunctor _ a ⋙ shiftFunctor _ b) := by
  have : QuasiCompact (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have : QuasiCompact (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
    exact inferInstanceAs (QuasiCompact (affinePlane.fst k₀ ≫ _))
  have : QuasiSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have : QuasiSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
    exact inferInstanceAs (QuasiSeparated (affinePlane.fst k₀ ≫ _))
  have h₁₂₃ : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
      affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
    pullback.condition.symm
  have : IsSeparated (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  -- the functorial isomorphisms
  obtain ⟨eBC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affinePlane.snd k₀) (affinePlane.fst k₀) (affineTripleProduct.proj₂₃ k₀)
    (affineTripleProduct.proj₁₂ k₀) (IsPullback.of_hasPullback _ _)
  obtain ⟨eTA⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar (k₀ := k₀)
    (affineTripleProduct.proj₁₂ k₀) 𝒦 h𝒦
  obtain ⟨eP⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse (k₀ := k₀)
    (affineTripleProduct.proj₂₃ k₀) 𝒦' h𝒦'
  obtain ⟨eA₁⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₂ k₀) (affinePlane.fst k₀)
  obtain ⟨eA₂⟩ := WeilComplex.nonempty_upperStar_iso_of_eq (k₀ := k₀) (l := l)
    (f := affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀)
    (g := affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀)
    (pullback.tripleProj₁₃_fst _ _ _).symm
  obtain ⟨eC₁⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₂₃ k₀) (affinePlane.snd k₀)
  obtain ⟨eC₂⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_of_eq (k₀ := k₀) (l := l)
    (f := affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀)
    (g := affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀)
    (pullback.tripleProj₁₃_snd _ _ _).symm
  -- the functors involved
  let A := WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀)
  let A₁₂ := WeilComplex.upperStar (k₀ := k₀) (l := l) (affineTripleProduct.proj₁₂ k₀)
  let A₁₃ := WeilComplex.upperStar (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀)
  let T := WeilComplex.tensorLisse 𝒦 h𝒦
  let T' := WeilComplex.tensorLisse 𝒦' h𝒦'
  have h₁ : ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj 𝒦).IsLisse :=
    ProEtale.IsAdicLisseSheaf.upperStar _ h𝒦
  have h₂ : ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj 𝒦').IsLisse :=
    ProEtale.IsAdicLisseSheaf.upperStar _ h𝒦'
  let T₁ := WeilComplex.tensorLisse
    ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj 𝒦) h₁
  let T₂ := WeilComplex.tensorLisse
    ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj 𝒦') h₂
  let C := WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)
  let C₂₃ := WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₂₃ k₀)
  let D := WeilComplex.derivedLowerShriek k₀ l
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀)
  let Sa := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) a
  let Sb := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) b
  -- the chain of isomorphisms, all composites associated to the right
  have e₀ : WeilComplex.kernelTransform 𝒦 h𝒦 a ⋙ WeilComplex.kernelTransform 𝒦' h𝒦' b ≅
      A ⋙ T ⋙ C ⋙ Sa ⋙ A ⋙ T' ⋙ C ⋙ Sb :=
    Iso.refl _
  have s₁ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft C
    ((Functor.associator _ _ (T' ⋙ C ⋙ Sb)).symm ≪≫
      Functor.isoWhiskerRight (A.commShiftIso a) (T' ⋙ C ⋙ Sb) ≪≫
      Functor.associator _ _ (T' ⋙ C ⋙ Sb))))
  have s₂ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft C
    (Functor.isoWhiskerLeft A
      ((Functor.associator _ _ (C ⋙ Sb)).symm ≪≫
        Functor.isoWhiskerRight (T'.commShiftIso a) (C ⋙ Sb) ≪≫
        Functor.associator _ _ (C ⋙ Sb)))))
  have s₃ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft C
    (Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft T'
      ((Functor.associator _ _ Sb).symm ≪≫
        Functor.isoWhiskerRight (C.commShiftIso a) Sb ≪≫
        Functor.associator _ _ Sb)))))
  have s₄ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft T
    ((Functor.associator _ _ (T' ⋙ C ⋙ Sa ⋙ Sb)).symm ≪≫
      Functor.isoWhiskerRight eBC (T' ⋙ C ⋙ Sa ⋙ Sb) ≪≫
      Functor.associator _ _ (T' ⋙ C ⋙ Sa ⋙ Sb)))
  have s₅ := Functor.isoWhiskerLeft A
    ((Functor.associator _ _ (C₂₃ ⋙ T' ⋙ C ⋙ Sa ⋙ Sb)).symm ≪≫
      Functor.isoWhiskerRight eTA (C₂₃ ⋙ T' ⋙ C ⋙ Sa ⋙ Sb) ≪≫
      Functor.associator _ _ (C₂₃ ⋙ T' ⋙ C ⋙ Sa ⋙ Sb))
  have s₆ := (Functor.associator A A₁₂ (T₁ ⋙ C₂₃ ⋙ T' ⋙ C ⋙ Sa ⋙ Sb)).symm ≪≫
    Functor.isoWhiskerRight (eA₁.symm ≪≫ eA₂) (T₁ ⋙ C₂₃ ⋙ T' ⋙ C ⋙ Sa ⋙ Sb)
  have s₇ := Functor.isoWhiskerLeft A₁₃ (Functor.isoWhiskerLeft T₁
    ((Functor.associator _ _ (C ⋙ Sa ⋙ Sb)).symm ≪≫
      Functor.isoWhiskerRight eP (C ⋙ Sa ⋙ Sb) ≪≫
      Functor.associator _ _ (C ⋙ Sa ⋙ Sb)))
  have s₈ := Functor.isoWhiskerLeft A₁₃ (Functor.isoWhiskerLeft T₁ (Functor.isoWhiskerLeft T₂
    ((Functor.associator C₂₃ C (Sa ⋙ Sb)).symm ≪≫
      Functor.isoWhiskerRight (eC₁.symm ≪≫ eC₂) (Sa ⋙ Sb))))
  exact ⟨e₀ ≪≫ s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅ ≪≫ s₆ ≪≫ s₇ ≪≫ s₈⟩

end AlgebraicGeometry
