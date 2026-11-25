/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion
public import WeilConjectures.WeilSheaf.FourierInversion.AffinePlaneAdd
public import WeilConjectures.WeilSheaf.FourierInversion.KernelComposition

/-!
# Fourier inversion with the same character

For a nontrivial additive character `ψ`, applying the Fourier–Deligne transform twice with the
same character gives the reflection `ι' : x ↦ -x`, up to the Tate twist:

`FT_ψ ∘ FT_ψ ≅ ι'^* ((-)(-1))`

(`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_self`; blueprint
`proposition-fourier-inversion`, `sec-Fourier-inversion`, second formula). On the triple product
`𝔸³` with points `(x, ξ, y)` the composite is `Rr₃!(ℒ_ψ((x + y) ξ) ⊗ r₁^* K)[1][1]`
(`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_fourierTransform`), and the delta kernel
computation for the function `x + y` on `𝔸²`, whose zero locus is the antidiagonal
`x ↦ (x, -x)`, identifies it with `Rι'₀!(K(-1)[-2])[1][1]`; the compact-support direct image
along the involution `ι'` is the pullback along `ι'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Reflection

variable (k₀) in
/-- The reflection `ι' : x ↦ -x` of the affine line, the inverse of the addition. -/
noncomputable def affineLine.neg : affineLine k₀ ⟶ affineLine k₀ :=
  AffineSpace.neg PUnit.{u + 1} (Spec (CommRingCat.of k₀))

instance : (affineLine.neg k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.neg_over _ _⟩

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLine.neg_comp_neg : affineLine.neg k₀ ≫ affineLine.neg k₀ = 𝟙 _ :=
  AffineSpace.neg_comp_neg _ _

variable (k₀) in
/-- The reflection of the affine line as an automorphism. -/
noncomputable def affineLine.negIso : affineLine k₀ ≅ affineLine k₀ where
  hom := affineLine.neg k₀
  inv := affineLine.neg k₀

instance : IsIso (affineLine.neg k₀) :=
  (affineLine.negIso k₀).isIso_hom

instance : (affineLine.negIso k₀).hom.IsOver (Spec (CommRingCat.of k₀)) :=
  inferInstanceAs ((affineLine.neg k₀).IsOver _)

instance : (affineLine.negIso k₀).inv.IsOver (Spec (CommRingCat.of k₀)) :=
  inferInstanceAs ((affineLine.neg k₀).IsOver _)

variable (k₀) in
/-- The antidiagonal `x ↦ (x, -x)` of the affine line, the zero locus of the addition. -/
noncomputable def affineLine.antidiagonal : affineLine k₀ ⟶ affinePlane k₀ :=
  affineLine.diagonal k₀ ≫ AffineSpace.prodNeg PUnit.{u + 1} (Spec (CommRingCat.of k₀))

instance : IsClosedImmersion (affineLine.antidiagonal k₀) := by
  rw [affineLine.antidiagonal]
  infer_instance

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLine.antidiagonal_fst : affineLine.antidiagonal k₀ ≫ affinePlane.fst k₀ = 𝟙 _ := by
  have h : affineLine.diagonal k₀ ≫ affinePlane.fst k₀ = 𝟙 _ := pullback.diagonal_fst _
  have h' : AffineSpace.prodNeg PUnit.{u + 1} (Spec (CommRingCat.of k₀)) ≫ affinePlane.fst k₀ =
      affinePlane.fst k₀ :=
    AffineSpace.prodNeg_fst _ _
  rw [affineLine.antidiagonal, Category.assoc, h', h]

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLine.antidiagonal_snd :
    affineLine.antidiagonal k₀ ≫ affinePlane.snd k₀ = affineLine.neg k₀ := by
  have h : affineLine.diagonal k₀ ≫ affinePlane.snd k₀ = 𝟙 _ := pullback.diagonal_snd _
  have h' : AffineSpace.prodNeg PUnit.{u + 1} (Spec (CommRingCat.of k₀)) ≫ affinePlane.snd k₀ =
      affinePlane.snd k₀ ≫ affineLine.neg k₀ :=
    AffineSpace.prodNeg_snd _ _
  rw [affineLine.antidiagonal, Category.assoc, h', reassoc_of% h]

instance : (affineLine.antidiagonal k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨show affineLine.antidiagonal k₀ ≫ affinePlane.fst k₀ ≫ _ = _ by
    rw [affineLine.antidiagonal_fst_assoc]⟩


omit [Finite k₀] in
/-- The antidiagonal `x ↦ (x, -x)` is the fibre of the addition over the origin. -/
theorem affineLine.isPullback_antidiagonal :
    IsPullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine.antidiagonal k₀)
      (AffineSpace.zeroSection PUnit.{u + 1} (Spec (CommRingCat.of k₀))) (affinePlane.add k₀) := by
  rw [affinePlane.add_eq]
  exact AffineSpace.isPullback_diagonal_prodNeg_add _ _

end Reflection

/-- The compact-support direct image along an isomorphism is the pullback along its inverse:
`Re₀! ≅ (e⁻¹)^*`. By compact-support base change along `e` itself, whose base change along `e`
is the identity, `e^* ∘ Re₀! ≅ 𝟙`, and `(e⁻¹)^* ∘ e^* ≅ (e ≫ e⁻¹)^* ≅ 𝟙`. -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_hom_upperStar_inv {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (e : X ≅ Y)
    [e.hom.IsOver (Spec (CommRingCat.of k₀))] [e.inv.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.derivedLowerShriek k₀ l e.hom ≅ WeilComplex.upperStar e.inv) := by
  have hsq : IsPullback (𝟙 X) (𝟙 X) e.hom e.hom :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  obtain ⟨BC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    e.hom e.hom (𝟙 X) (𝟙 X) hsq
  obtain ⟨eU⟩ := WeilComplex.nonempty_iso_upperStar_id (k₀ := k₀) (l := l) (X := X)
  obtain ⟨eS⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_id (k₀ := k₀) (l := l) (X := X)
  obtain ⟨eC⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) e.inv e.hom
  obtain ⟨eE⟩ := WeilComplex.nonempty_iso_upperStar_of_eq (k₀ := k₀) (l := l) e.inv_hom_id
  obtain ⟨eV⟩ := WeilComplex.nonempty_iso_upperStar_id (k₀ := k₀) (l := l) (X := Y)
  -- `Re₀! ≅ Re₀! ⋙ e^* ⋙ (e⁻¹)^* ≅ (e⁻¹)^*`
  have e₁ : WeilComplex.upperStar e.hom ⋙ WeilComplex.upperStar e.inv ≅
      𝟭 (WeilComplex k₀ l Y) :=
    eC.symm ≪≫ eE ≪≫ eV
  exact ⟨(Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (WeilComplex.derivedLowerShriek k₀ l e.hom) e₁.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (BC ≪≫ Functor.isoWhiskerRight eU _ ≪≫ Functor.leftUnitor _ ≪≫ eS)
      (WeilComplex.upperStar e.inv) ≪≫ Functor.leftUnitor _⟩

/-- The two Fourier kernels pulled back to the triple product `𝔸³` with points `(x, ξ, y)`
multiply to `ℒ_ψ((x + y) ξ)`: tensoring with `r₁₂^* μ^* ℒ_ψ` and then with `r₂₃^* μ^* ℒ_ψ` is
tensoring with `ℒ_ψ((x + y) ξ)` (blueprint `lemma-artin-schreier-character-sheaf--2`). -/
theorem WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_add
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj (fourierKernel (l := l) ψ))
        ((isLisse_fourierKernel ψ).upperStar _) ⋙
      WeilComplex.tensorLisse
        ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj (fourierKernel ψ))
        ((isLisse_fourierKernel ψ).upperStar _) ≅
      WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((affinePlane.add k₀).appTop
                (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _)) := by
  have h₁₂₃ : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
      affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
    pullback.condition.symm
  -- the functions `x ξ` on `𝔸²` and `(x + y) ξ` on `𝔸³`
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  have hring : (affineTripleProduct.proj₂₃ k₀).appTop m +
      (affineTripleProduct.proj₁₂ k₀).appTop m =
      (affineTripleProduct.proj₁₃ k₀).appTop ((affinePlane.add k₀).appTop X₁) *
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
    have e₁ : (affineTripleProduct.proj₁₃ k₀).appTop ((affinePlane.add k₀).appTop X₁) =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ +
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
      rw [affinePlane.add_appTop_coord, map_add]
      exact congrArg₂ (· + ·)
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
  have eF' : fourierKernel (l := l) ψ ≅ artinSchreierOf ψ m := eF
  obtain ⟨eG₁⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₁₂ k₀) ψ m
  obtain ⟨eG₂⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₂₃ k₀) ψ m
  have h₁ : ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).obj
      (fourierKernel (l := l) ψ)).IsLisse :=
    ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ)
  have h₂ : ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).obj
      (fourierKernel (l := l) ψ)).IsLisse :=
    ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ)
  obtain ⟨eT₁⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar (affineTripleProduct.proj₁₂ k₀)).mapIso eF' ≪≫ eG₁) h₁
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    ((WeilSheaf.upperStar (affineTripleProduct.proj₂₃ k₀)).mapIso eF' ≪≫ eG₂) h₂
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₁₂⟩ := WeilComplex.nonempty_iso_tensorLisse_comp
    (artinSchreierOf ψ ((affineTripleProduct.proj₂₃ k₀).appTop m))
    (artinSchreierOf ψ ((affineTripleProduct.proj₁₂ k₀).appTop m))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eMul⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ
    ((affineTripleProduct.proj₂₃ k₀).appTop m) ((affineTripleProduct.proj₁₂ k₀).appTop m)
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (eMul ≪≫ eqToIso (congrArg (artinSchreierOf ψ) hring))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ _).dual
      (isLisse_artinSchreierOf ψ _))
    (isLisse_artinSchreierOf ψ _)
  exact ⟨Functor.isoWhiskerRight eT₁ _ ≪≫ Functor.isoWhiskerLeft _ eT₂ ≪≫ eT₁₂ ≪≫ eT⟩

/-- **`FT_ψ ∘ FT_ψ` on the triple product** (blueprint `proposition-fourier-inversion`). On `𝔸³`
with points `(x, ξ, y)`,

`FT_ψ FT_ψ (K) ≅ Rr₃₀!(ℒ_ψ((x + y) ξ) ⊗ r₁^* K)[1][1]`

naturally in `K`, with `r₁ = r₁₃ ≫ pr₁` and `r₃ = r₁₃ ≫ pr₂`: the composition of kernel
transforms (`AlgebraicGeometry.WeilComplex.nonempty_iso_kernelTransform_comp`) together with
`ℒ_ψ(x ξ) ⊗ ℒ_ψ(ξ y) ≅ ℒ_ψ((x + y) ξ)` (blueprint `lemma-artin-schreier-character-sheaf--2`). -/
theorem nonempty_iso_fourierTransform_comp_fourierTransform
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ ≅
      WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((affinePlane.add k₀).appTop
                (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) := by
  obtain ⟨eKT⟩ := WeilComplex.nonempty_iso_kernelTransform_comp (fourierKernel (l := l) ψ)
    (fourierKernel ψ) (isLisse_fourierKernel ψ) (isLisse_fourierKernel ψ) 1 1
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_upperStar_fourierKernel_comp_add (l := l) ψ
  let A₁₃ := WeilComplex.upperStar (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀)
  let D := WeilComplex.derivedLowerShriek k₀ l
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀)
  rw [fourierTransform_eq_kernelTransform]
  let S₁ := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ)
  exact ⟨eKT ≪≫ Functor.isoWhiskerLeft A₁₃
    ((Functor.associator _ _ (D ⋙ S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight eT (D ⋙ S₁ ⋙ S₁))⟩

/-- **`FT_ψ ∘ FT_ψ ≅ ι'^* ((-)(-1))`** (blueprint `proposition-fourier-inversion`,
`sec-Fourier-inversion`, second formula), with the shifts `[-2][1][1]` left uncancelled: for a
nontrivial additive character `ψ` and a Weil complex `K` on the affine line,
`FT_ψ FT_ψ (K) ≅ ι'^*(K(-1)[-2])[1][1]`, naturally in `K`, where `ι' : x ↦ -x` is the
reflection. The kernel `ℒ_ψ((x + y) ξ)` of the composite
(`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_fourierTransform`) is the delta kernel of
the zero locus of `x + y`, the antidiagonal `x ↦ (x, -x)`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul`),
and the compact-support direct image along the involution `ι'` is the pullback along `ι'`. -/
theorem nonempty_iso_fourierTransform_comp_self (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ ≅
      WeilComplex.tateTwist k₀ l (affineLine k₀) (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⋙
        WeilComplex.upperStar (affineLine.neg k₀) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) := by
  obtain ⟨e₁⟩ := nonempty_iso_fourierTransform_comp_fourierTransform (l := l) ψ
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀) (affinePlane.fst k₀)
  obtain ⟨e₃⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀) (affinePlane.snd k₀)
  obtain ⟨e₄⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (l := l) ψ hψ (affinePlane.add k₀)
    (affineTripleProduct.proj₁₃ k₀) (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀)
    affineTripleProduct.isPullback_proj₁₃ (affineLine.antidiagonal k₀)
    affineLine.isPullback_antidiagonal
  obtain ⟨e₅⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affineLine.antidiagonal k₀) (affinePlane.fst k₀)
  obtain ⟨e₆⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineLine.antidiagonal k₀) (affinePlane.snd k₀)
  obtain ⟨e₇⟩ := WeilComplex.nonempty_iso_upperStar_of_eq (k₀ := k₀) (l := l)
    (affineLine.antidiagonal_fst (k₀ := k₀))
  obtain ⟨e₈⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_of_eq (k₀ := k₀) (l := l)
    (affineLine.antidiagonal_snd (k₀ := k₀))
  obtain ⟨e₉⟩ := WeilComplex.nonempty_iso_upperStar_id (k₀ := k₀) (l := l)
    (X := affineLine k₀)
  obtain ⟨e₁₀⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_hom_upperStar_inv (k₀ := k₀)
    (l := l) (affineLine.negIso k₀)
  let T := WeilComplex.tensorLisse (artinSchreierOf ψ
    ((affineTripleProduct.proj₁₃ k₀).appTop
        ((affinePlane.add k₀).appTop
                (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit)) *
      (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
        (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _)
  let Dl := WeilComplex.derivedLowerShriek k₀ l (affineLine.antidiagonal k₀)
  let Sh := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)
  let A := WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀)
  let C := WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)
  let tw := WeilComplex.tateTwist k₀ l (affineLine k₀) (-1) ⋙
    shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (-2 : ℤ)
  have eA : A ⋙ WeilComplex.upperStar (affineLine.antidiagonal k₀) ≅ 𝟭 _ :=
    e₅.symm ≪≫ e₇ ≪≫ e₉
  have eC : Dl ⋙ C ≅ WeilComplex.upperStar (affineLine.neg k₀) :=
    e₆.symm ≪≫ e₈ ≪≫ e₁₀
  exact ⟨e₁ ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫
    Functor.isoWhiskerLeft (A ⋙ WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀) ⋙ T)
      (Functor.isoWhiskerRight e₃ Sh) ≪≫
    Functor.isoWhiskerLeft A (Functor.isoWhiskerRight e₄ (C ⋙ Sh)) ≪≫
    Functor.isoWhiskerRight eA (tw ⋙ Dl ⋙ C ⋙ Sh) ≪≫
    Functor.isoWhiskerLeft (𝟭 _ ⋙ tw) (Functor.isoWhiskerRight eC Sh)⟩

end AlgebraicGeometry
