/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist

/-!
# The Fourier–Deligne transform commutes with Tate twists

## Main statements

- `AlgebraicGeometry.nonempty_iso_fourierTransform_tateTwist`
(`proposition-base-change-fourier-inversion--2`, clause (2)):
  `FT_ψ(K(m)) ≅ FT_ψ(K)(m)`, naturally in the Weil complex `K`.
- `AlgebraicGeometry.nonempty_iso_fourierTransform_of_iso_constantTwist`: the Fourier transform
  commutes with constant twists `- ⊗ 𝓑_b`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section Fourier

variable [Fact (ringChar k₀ ≠ l)]

/-- If `τ₁ ⋙ F ≅ F ⋙ τ₂` and `τ₂ ⋙ G ≅ G ⋙ τ₃`, then `τ₁ ⋙ F ⋙ G ≅ (F ⋙ G) ⋙ τ₃`. -/
private noncomputable def compCommIso {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {τ₁ : C₁ ⥤ C₁} {τ₂ : C₂ ⥤ C₂} {τ₃ : C₃ ⥤ C₃} {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃}
    (e₁ : τ₁ ⋙ F ≅ F ⋙ τ₂) (e₂ : τ₂ ⋙ G ≅ G ⋙ τ₃) : τ₁ ⋙ F ⋙ G ≅ (F ⋙ G) ⋙ τ₃ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ G ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F e₂ ≪≫ (Functor.associator _ _ _).symm

/-- The Fourier–Deligne transform on the derived categories of pro-étale Weil sheaves,
`K ↦ Rpr₂!(pr₁^* K ⊗ μ^* ℒ_ψ)[1]`, of which `AlgebraicGeometry.fourierTransform` is the
restriction to Weil complexes. -/
private noncomputable abbrev fourierTransformDerived (ψ : AddChar k₀ (PadicAlgCl l)) :
    _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l (affineLine k₀)) ⥤
      _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l (affineLine k₀)) :=
  (ProEtaleWeilSheaf.upperStar k₀ l (affinePlane.fst k₀)).mapDerivedCategory ⋙
    (ProEtaleWeilSheaf.ihomFunctor k₀ l _
      ((fourierKernel ψ).dual (isLisse_fourierKernel ψ)).obj).rightDerivedFunctor ⋙
    ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l (affinePlane.snd k₀)
      (HasCompactification.compactification _
        (hf := hasCompactification_of_over (k₀ := k₀) _)) ⋙
    shiftFunctor _ (1 : ℤ)

/-- The Fourier–Deligne transform of Weil complexes followed by the inclusion into the derived
category is the inclusion followed by `fourierTransformDerived`. -/
private noncomputable def fourierTransformCompιIso (ψ : AddChar k₀ (PadicAlgCl l)) :
    fourierTransform ψ ⋙ (WeilComplex.objectProperty k₀ l (affineLine k₀)).ι ≅
      (WeilComplex.objectProperty k₀ l (affineLine k₀)).ι ⋙ fourierTransformDerived ψ :=
  Functor.isoWhiskerLeft (WeilComplex.upperStar (affinePlane.fst k₀) ⋙
      WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ) ⋙
      WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀))
    ((WeilComplex.objectProperty k₀ l (affineLine k₀)).ι.commShiftIso (1 : ℤ))

/-- The Fourier–Deligne transform on derived categories commutes with constant twists. -/
private noncomputable def constantTwistCompFourierTransformDerivedIso
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : (PadicAlgCl l)ˣ) :
    (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory ⋙
        fourierTransformDerived ψ ≅
      fourierTransformDerived ψ ⋙
        (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory :=
  compCommIso (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompUpperStarIso k₀ l _ b)
    (compCommIso (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedIhomIso _ b)
      (compCommIso
        (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso k₀ l
          (affinePlane.snd k₀) b _)
        (((ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.commShiftIso
          (1 : ℤ)).symm)))

/-- The Fourier–Deligne transform of Weil complexes on the affine line commutes with constant
twists, on underlying objects of the derived category of pro-étale Weil sheaves: if the
underlying object of `K'` is the constant twist by `b` of that of `K`, then the same holds for
their Fourier transforms. -/
theorem nonempty_iso_fourierTransform_of_iso_constantTwist (ψ : AddChar k₀ (PadicAlgCl l))
    (b : (PadicAlgCl l)ˣ) {K K' : WeilComplex k₀ l (affineLine k₀)}
    (e : K'.obj ≅
      (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.obj K.obj) :
    Nonempty (((fourierTransform ψ).obj K').obj ≅
      (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.obj
        ((fourierTransform ψ).obj K).obj) :=
  ⟨(fourierTransformCompιIso ψ).app K' ≪≫ (fourierTransformDerived ψ).mapIso e ≪≫
    (constantTwistCompFourierTransformDerivedIso ψ b).app K.obj ≪≫
    (ProEtaleWeilSheaf.constantTwist k₀ l (affineLine k₀) b).mapDerivedCategory.mapIso
      ((fourierTransformCompιIso ψ).app K).symm⟩

-- TODO(unify): proposition-base-change-fourier-inversion--2
/-- The Fourier–Deligne transform of Weil complexes on the affine line commutes with the Tate
twist: `FT_ψ(K(m)) ≅ FT_ψ(K)(m)` as Weil complexes, naturally in `K`. This is the Weil
structure part of the second clause of the base linearity proposition; the underlying
statement on étale complexes is `AlgebraicGeometry.Etale.nonempty_iso_fourierTransform_tateTwist`.

The Tate twist is the constant twist by `χ_ℓ(σ)^m`
(`AlgebraicGeometry.ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso`), and each
constituent of the Fourier–Deligne transform commutes with constant twists.
(blueprint: `proposition-base-change-fourier-inversion--2`, clause (2)) -/
theorem nonempty_iso_fourierTransform_tateTwist (ψ : AddChar k₀ (PadicAlgCl l)) (m : ℤ) :
    Nonempty (WeilComplex.tateTwist k₀ l (affineLine k₀) m ⋙ fourierTransform ψ ≅
      fourierTransform ψ ⋙ WeilComplex.tateTwist k₀ l (affineLine k₀) m) := by
  let P := WeilComplex.objectProperty k₀ l (affineLine k₀)
  let e := ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso
    (k₀ := k₀) (l := l) (X := affineLine k₀) m
  refine ⟨((P.fullyFaithfulι.whiskeringRight _).preimageIso ?_)⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (WeilComplex.tateTwist k₀ l (affineLine k₀) m)
      (fourierTransformCompιIso ψ) ≪≫
    (Functor.associator P.ι _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft P.ι e) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P.ι (constantTwistCompFourierTransformDerivedIso ψ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fourierTransformCompιIso ψ).symm _ ≪≫
    Functor.isoWhiskerLeft _ e.symm ≪≫
    (Functor.associator (fourierTransform ψ) P.ι _).symm

end Fourier

end AlgebraicGeometry
