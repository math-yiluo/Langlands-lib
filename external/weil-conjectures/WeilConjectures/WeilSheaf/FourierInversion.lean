/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Composite
public import WeilConjectures.WeilSheaf.FourierInversion.Delta
public import WeilConjectures.WeilSheaf.FourierTraceAux

/-!
# Fourier inversion for Weil complexes

For a nontrivial additive character `ψ` the Fourier–Deligne transform of Weil complexes on the
affine line is an equivalence (blueprint `sec-Fourier-inversion`, `proposition-fourier-inversion`):
`FT_{ψ⁻¹} ∘ FT_ψ ≅ (-)(-1)` (`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_inv`), and
the same with `ψ` and `ψ⁻¹` exchanged.

The composite is computed on the triple product
(`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_fourierTransform_inv`) as
`Rr₃!(ℒ_ψ((x - y) ξ) ⊗ r₁^* K)[1][1]`; factoring `r₃ = r₁₃ ≫ pr₂` and `r₁ = r₁₃ ≫ pr₁`, the
delta kernel computation
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul`)
for the function `x - y` on `𝔸²`, whose zero locus is the diagonal `Δ`, gives
`Rpr₂! RΔ! (Δ^* pr₁^* K)(-1)[-2][1][1] ≅ K(-1)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

/-- If `F ⋙ G` and `G ⋙ F` are isomorphic to equivalences, then `F` is an equivalence. -/
theorem Functor.isEquivalence_of_comp_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (G : D ⥤ C) (T : C ⥤ C) (T' : D ⥤ D) [T.IsEquivalence] [T'.IsEquivalence]
    (e : F ⋙ G ≅ T) (e' : G ⋙ F ≅ T') : F.IsEquivalence := by
  have : (F ⋙ G).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  have : (G ⋙ F).IsEquivalence := Functor.isEquivalence_of_iso e'.symm
  have : F.Faithful := Functor.Faithful.of_comp F G
  have : G.Faithful := Functor.Faithful.of_comp G F
  have : F.Full := Functor.Full.of_comp_faithful F G
  have : F.EssSurj := ⟨fun Y ↦ ⟨G.obj ((G ⋙ F).objPreimage Y),
    ⟨(G ⋙ F).objObjPreimageIso Y⟩⟩⟩
  exact { }

end CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Pullbacks of Weil complexes along equal morphisms are isomorphic. -/
theorem WeilComplex.nonempty_iso_upperStar_of_eq {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] {f g : X ⟶ Y}
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))] (h : f = g) :
    Nonempty (WeilComplex.upperStar (k₀ := k₀) (l := l) f ≅ WeilComplex.upperStar g) := by
  subst h
  exact ⟨Iso.refl _⟩

instance : QuasiCompact (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
  have : QuasiCompact (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  exact inferInstanceAs (QuasiCompact (affinePlane.fst k₀ ≫ _))

instance : QuasiSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
  have : QuasiSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  exact inferInstanceAs (QuasiSeparated (affinePlane.fst k₀ ≫ _))

instance : IsSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
  have : IsSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
  exact inferInstanceAs (IsSeparated (affinePlane.fst k₀ ≫ _))

variable (k₀) in
/-- The subtraction `(x, y) ↦ x - y` on the affine plane. -/
noncomputable def affinePlane.sub : affinePlane k₀ ⟶ affineLine k₀ :=
  AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))

instance : (affinePlane.sub k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.sub_over _ _⟩

variable (k₀) in
/-- The diagonal `x ↦ (x, x)` of the affine line. -/
noncomputable def affineLine.diagonal : affineLine k₀ ⟶ affinePlane k₀ :=
  pullback.diagonal (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

instance : (affineLine.diagonal k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨pullback.diagonal_fst_assoc _ _⟩

instance : IsClosedImmersion (affineLine.diagonal k₀) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.diagonal (affineLine k₀ ↘ Spec (CommRingCat.of k₀))))

/-- **`FT_{ψ⁻¹} ∘ FT_ψ ≅ (-)(-1)`** (blueprint `proposition-fourier-inversion`, first formula), with
the shifts `[-2][1][1]` left uncancelled. -/
theorem nonempty_iso_fourierTransform_comp_inv (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.tateTwist k₀ l (affineLine k₀) (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) := by
  obtain ⟨e₁⟩ := nonempty_iso_fourierTransform_comp_fourierTransform_inv (l := l) ψ
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀) (affinePlane.fst k₀)
  obtain ⟨e₃⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀) (affinePlane.snd k₀)
  obtain ⟨e₄⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (l := l) ψ hψ
    (affinePlane.sub k₀)
    (affineTripleProduct.proj₁₃ k₀) (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀)
    affineTripleProduct.isPullback_proj₁₃ (affineLine.diagonal k₀)
    (AffineSpace.isPullback_diagonal_sub _ _)
  obtain ⟨e₅⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affineLine.diagonal k₀)
    (affinePlane.fst k₀)
  obtain ⟨e₆⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineLine.diagonal k₀)
    (affinePlane.snd k₀)
  obtain ⟨e₇⟩ := WeilComplex.nonempty_iso_upperStar_of_eq (k₀ := k₀) (l := l)
    (f := (affineLine.diagonal k₀) ≫ affinePlane.fst k₀) (g := 𝟙 _) (pullback.diagonal_fst _)
  obtain ⟨e₈⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_of_eq (k₀ := k₀) (l := l)
    (f := (affineLine.diagonal k₀) ≫ affinePlane.snd k₀) (g := 𝟙 _) (pullback.diagonal_snd _)
  obtain ⟨e₉⟩ := WeilComplex.nonempty_iso_upperStar_id (k₀ := k₀) (l := l)
    (X := affineLine k₀)
  obtain ⟨e₁₀⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_id (k₀ := k₀) (l := l)
    (X := affineLine k₀)
  let T := WeilComplex.tensorLisse (artinSchreierOf ψ
    ((affineTripleProduct.proj₁₃ k₀).appTop
        ((affinePlane.sub k₀).appTop (AffineSpace.coord _ PUnit.unit)) *
      (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
        (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _)
  let Dl := WeilComplex.derivedLowerShriek k₀ l (affineLine.diagonal k₀)
  let Sh := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)
  let A := WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀)
  let C := WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)
  let tw := WeilComplex.tateTwist k₀ l (affineLine k₀) (-1) ⋙
    shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (-2 : ℤ)
  have eA : A ⋙ WeilComplex.upperStar (affineLine.diagonal k₀) ≅ 𝟭 _ :=
    e₅.symm ≪≫ e₇ ≪≫ e₉
  have eC : Dl ⋙ C ≅ 𝟭 _ := e₆.symm ≪≫ e₈ ≪≫ e₁₀
  exact ⟨e₁ ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫
    Functor.isoWhiskerLeft (A ⋙ WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀) ⋙ T)
      (Functor.isoWhiskerRight e₃ Sh) ≪≫
    Functor.isoWhiskerLeft A (Functor.isoWhiskerRight e₄ (C ⋙ Sh)) ≪≫
    Functor.isoWhiskerRight eA (tw ⋙ Dl ⋙ C ⋙ Sh) ≪≫
    Functor.isoWhiskerLeft (𝟭 _ ⋙ tw) (Functor.isoWhiskerRight eC Sh)⟩

-- TODO(unify): sec-Fourier-inversion
/-- **Fourier inversion**: for a nontrivial additive character the Fourier–Deligne transform is
an equivalence between the triangulated categories of Weil complexes on the two dual lines, with
quasi-inverse `FT_{ψ⁻¹}` up to the Tate twist `(1)`. -/
theorem isEquivalence_fourierTransform (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    (fourierTransform (l := l) ψ).IsEquivalence := by
  have := WeilComplex.isEquivalence_tateTwist (k₀ := k₀) (l := l) (X := affineLine k₀) (-1)
  obtain ⟨e⟩ := nonempty_iso_fourierTransform_comp_inv (l := l) ψ hψ
  obtain ⟨e'⟩ := nonempty_iso_fourierTransform_comp_inv (l := l) ψ⁻¹ (inv_ne_one.mpr hψ)
  rw [inv_inv] at e'
  exact Functor.isEquivalence_of_comp_iso _ _ _ _ e e'

end AlgebraicGeometry
