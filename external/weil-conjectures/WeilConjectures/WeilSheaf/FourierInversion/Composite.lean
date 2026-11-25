/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.KernelComposition
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing
public import WeilConjectures.WeilSheaf.FourierTraceAux

/-!
# Fourier inversion: the composite of two Fourier transforms

`FT_{ψ⁻¹} ∘ FT_ψ` computed on the triple product `𝔸³` (blueprint `proposition-fourier-inversion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The Fourier kernel `μ^* ℒ_ψ` is the Artin–Schreier sheaf `ℒ_ψ(x y)` of the function `x y`. -/
theorem nonempty_iso_fourierKernel_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierKernel ψ ≅ artinSchreierOf ψ
      ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit))) := by
  rw [artinSchreierOf_eq]
  exact ⟨fourierKernelIso ψ ≪≫ (WeilSheaf.upperStarCongr affinePlane.mul_eq_homOfSection).app _⟩

/-- The Fourier kernels for `ψ` and `ψ⁻¹` pulled back to the triple product `𝔸³` with points
`(x, ξ, y)` multiply to `ℒ_ψ((x - y) ξ)`: tensoring with `r₁₂^* μ^* ℒ_ψ` and then with
`r₂₃^* μ^* ℒ_{ψ⁻¹}` is tensoring with `ℒ_ψ((x - y) ξ)` (blueprint
`lemma-artin-schreier-character-sheaf--2`). -/
theorem WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_sub
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj (fourierKernel (l := l) ψ))
        ((isLisse_fourierKernel ψ).upperStar _) ⋙
      WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj (fourierKernel ψ⁻¹))
        ((isLisse_fourierKernel ψ⁻¹).upperStar _) ≅
      WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop
                (AffineSpace.coord _ PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _)) := by
  have h₁₂₃ : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
      affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
    pullback.condition.symm
  -- the functions `x ξ` on `𝔸²` and `(x - y) ξ` on `𝔸³`
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  have hring : -(affineTripleProduct.proj₂₃ k₀).appTop m +
      (affineTripleProduct.proj₁₂ k₀).appTop m =
      (affineTripleProduct.proj₁₃ k₀).appTop
          ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop X₁) *
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
    have e₁ : (affineTripleProduct.proj₁₃ k₀).appTop
        ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop X₁) =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ -
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
      rw [AffineSpace.sub_appTop_coord, map_sub]
      exact congrArg₂ (· - ·)
        (congrArg (fun f ↦ Scheme.Hom.appTop f X₁) (pullback.tripleProj₁₃_fst _ _ _))
        (congrArg (fun f ↦ Scheme.Hom.appTop f X₁) (pullback.tripleProj₁₃_snd _ _ _))
    have e₂ : (affineTripleProduct.proj₂₃ k₀).appTop m =
        (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀).appTop X₁ *
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ :=
      map_mul _ _ _
    have e₃ : (affineTripleProduct.proj₁₂ k₀).appTop m =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ *
          (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ :=
      map_mul _ _ _
    rw [e₁, e₂, e₃, h₁₂₃]
    ring
  -- the kernels as Artin–Schreier sheaves on `𝔸³`
  obtain ⟨eF⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ
  obtain ⟨eF₁⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ⁻¹
  have eF' : fourierKernel (l := l) ψ ≅ artinSchreierOf ψ m := eF
  have eF₁' : fourierKernel (l := l) ψ⁻¹ ≅ artinSchreierOf ψ⁻¹ m := eF₁
  obtain ⟨eG₁⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₁₂ k₀) ψ m
  obtain ⟨eG₂⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₂₃ k₀) ψ⁻¹ m
  obtain ⟨eInv⟩ := nonempty_iso_artinSchreierOf_inv ψ ((affineTripleProduct.proj₂₃ k₀).appTop m)
  obtain ⟨eT₁⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).mapIso eF' ≪≫ eG₁)
    ((isLisse_fourierKernel ψ).upperStar _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).mapIso eF₁' ≪≫ eG₂ ≪≫ eInv)
    ((isLisse_fourierKernel ψ⁻¹).upperStar _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₁₂⟩ := WeilComplex.nonempty_iso_tensorLisse_comp
    (artinSchreierOf ψ (-(affineTripleProduct.proj₂₃ k₀).appTop m))
    (artinSchreierOf ψ ((affineTripleProduct.proj₁₂ k₀).appTop m))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eMul⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ
    (-(affineTripleProduct.proj₂₃ k₀).appTop m) ((affineTripleProduct.proj₁₂ k₀).appTop m)
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (eMul ≪≫ eqToIso (congrArg (artinSchreierOf ψ) hring))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ _).dual
      (isLisse_artinSchreierOf ψ _))
    (isLisse_artinSchreierOf ψ _)
  exact ⟨Functor.isoWhiskerRight eT₁ _ ≪≫ Functor.isoWhiskerLeft _ eT₂ ≪≫ eT₁₂ ≪≫ eT⟩

/-- **`FT_{ψ⁻¹} ∘ FT_ψ` on the triple product** (blueprint `proposition-fourier-inversion`, without
forming the convolution kernel). On `𝔸³` with points `(x, ξ, y)`,

`FT_{ψ⁻¹} FT_ψ (K) ≅ Rr₃₀!(ℒ_ψ((x - y) ξ) ⊗ r₁^* K)[1][1]`

naturally in `K`, with `r₁ = r₁₃ ≫ pr₁` and `r₃ = r₁₃ ≫ pr₂`: the composition of kernel
transforms (`AlgebraicGeometry.WeilComplex.nonempty_iso_kernelTransform_comp`), which follows
from compact-support
base change along `pr₁ : (ξ, y) ↦ ξ`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`), the projection
formula for `r₂₃` and the composition `R(r₂₃ ≫ pr₂)₀! ≅ Rpr₂₀! Rr₂₃₀!`, together with
`ℒ_ψ(x ξ) ⊗ ℒ_{ψ⁻¹}(ξ y) ≅ ℒ_ψ((x - y) ξ)` (blueprint `lemma-artin-schreier-character-sheaf--2`). -/
theorem nonempty_iso_fourierTransform_comp_fourierTransform_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop
                (AffineSpace.coord _ PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) := by
  obtain ⟨eKT⟩ := WeilComplex.nonempty_iso_kernelTransform_comp (fourierKernel (l := l) ψ)
    (fourierKernel ψ⁻¹) (isLisse_fourierKernel ψ) (isLisse_fourierKernel ψ⁻¹) 1 1
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_sub (l := l) ψ
  let A₁₃ := WeilComplex.upperStar (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀)
  let D := WeilComplex.derivedLowerShriek k₀ l
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀)
  rw [fourierTransform_eq_kernelTransform, fourierTransform_eq_kernelTransform]
  let S₁ := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ)
  exact ⟨eKT ≪≫ Functor.isoWhiskerLeft A₁₃
    ((Functor.associator _ _ (D ⋙ S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight eT (D ⋙ S₁ ⋙ S₁))⟩

end AlgebraicGeometry
