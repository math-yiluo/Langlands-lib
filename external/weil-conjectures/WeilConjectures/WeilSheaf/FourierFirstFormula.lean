/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.FourierInversion.ConvolutionKernel

/-!
# The first Fourier formula

The Fourier–Deligne transform of Weil complexes on the affine line exchanges the constant sheaf
`ℚ̄_ℓ` and the skyscraper `δ₀ = i₀,* ℚ̄_ℓ` at the origin (blueprint
`lemma-fourier-transform-constant-sheaf`): for a nontrivial additive character `ψ`,

* `FT_ψ(ℚ̄_ℓ) ≅ δ₀(-1)[-1]` (`AlgebraicGeometry.nonempty_iso_fourierTransform_obj_adicConstant`):
  `FT_ψ(ℚ̄_ℓ) = Rpr₂!(μ^* ℒ_ψ)[1]`, and the delta kernel computation for the function `ξ` on the
  dual line, whose zero locus is the origin, gives `i₀,!(ℚ̄_ℓ(-1)[-2])[1]`;
* `FT_ψ(δ₀) ≅ ℚ̄_ℓ[1]` (`AlgebraicGeometry.nonempty_iso_fourierTransform_obj_delta`): by
  compact-support base change, `pr₁^* δ₀` is the constant sheaf on the line `{0} × 𝔸¹`, along
  which the kernel restricts to `ℒ_{ψ,0} ≅ ℚ̄_ℓ`, and `pr₂` maps this line isomorphically onto
  the dual line.
-/

@[expose] public section

-- As in `WeilConjectures.WeilSheaf.VerdierDualLocalization`: `Spec k₀` lies over itself through
-- the identity, so that the structure-morphism instances `(X ↘ S).IsOver S` apply.
attribute [instance 1100] CategoryTheory.instOverClass

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The compact-support direct image of Weil complexes commutes with the Tate twist:
`Rf₀!(K(m)) ≅ (Rf₀! K)(m)`, naturally in `K`. The Tate twist is the constant twist by
`χ_ℓ(σ)^m` on underlying complexes (`AlgebraicGeometry.WeilComplex.tateTwistCompιIso`), which
commutes with the compact-support direct image of pro-étale Weil sheaves. -/
theorem WeilComplex.nonempty_iso_tateTwist_comp_derivedLowerShriek {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (m : ℤ) :
    Nonempty (WeilComplex.tateTwist k₀ l X m ⋙ WeilComplex.derivedLowerShriek k₀ l f ≅
      WeilComplex.derivedLowerShriek k₀ l f ⋙ WeilComplex.tateTwist k₀ l Y m) := by
  let P := WeilComplex.objectProperty k₀ l Y
  let eD : WeilComplex.derivedLowerShriek k₀ l f ⋙ P.ι ≅
      (WeilComplex.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
        (HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)) :=
    ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _
  refine ⟨(P.fullyFaithfulι.whiskeringRight _).preimageIso ?_⟩
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (WeilComplex.tateTwist k₀ l X m) eD ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (WeilComplex.tateTwistCompιIso m) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ProEtaleWeilSheaf.mapDerivedCategoryConstantTwistCompRightDerivedLowerShriekIso
        k₀ l f _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eD.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (WeilComplex.tateTwistCompιIso m).symm ≪≫
    (Functor.associator _ _ _).symm

section Origin

variable (k₀) in
/-- The origin `0 : Spec k₀ ⟶ 𝔸¹` of the affine line. -/
noncomputable def affineLine.zero : Spec (CommRingCat.of k₀) ⟶ affineLine k₀ :=
  AffineSpace.zeroSection PUnit.{u + 1} (Spec (CommRingCat.of k₀))


instance : (affineLine.zero k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.zeroSection_over _ _⟩

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLine.zero_over :
    affineLine.zero k₀ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀) = 𝟙 _ :=
  AffineSpace.zeroSection_over _ _

instance : IsClosedImmersion (affineLine.zero k₀) := by
  have : IsClosedImmersion (affineLine.zero k₀ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [affineLine.zero_over]
    infer_instance
  exact IsClosedImmersion.of_comp _ (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

variable (k₀ l) in
/-- The skyscraper `δ₀ = i₀,* ℚ̄_ℓ` at the origin of the affine line, the extension by zero of
the constant Weil complex on the origin `i₀ : Spec k₀ ⟶ 𝔸¹` (a closed immersion, so that
`i₀,! = i₀,*`). -/
noncomputable def affineLine.delta : WeilComplex k₀ l (affineLine k₀) :=
  (WeilComplex.derivedLowerShriek k₀ l (affineLine.zero k₀)).obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable (k₀) in
/-- The line `ξ ↦ (0, ξ)` of the affine plane, the fibre of the first projection over the
origin. -/
noncomputable def affineLine.zeroFibre : affineLine k₀ ⟶ affinePlane k₀ :=
  pullback.lift ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ≫ affineLine.zero k₀) (𝟙 _)
    (by simp)

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLine.zeroFibre_fst :
    affineLine.zeroFibre k₀ ≫ affinePlane.fst k₀ =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ≫ affineLine.zero k₀ :=
  pullback.lift_fst _ _ _

omit [Finite k₀] in
@[reassoc (attr := simp)]
lemma affineLine.zeroFibre_snd : affineLine.zeroFibre k₀ ≫ affinePlane.snd k₀ = 𝟙 _ :=
  pullback.lift_snd _ _ _

instance : (affineLine.zeroFibre k₀).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨show affineLine.zeroFibre k₀ ≫ affinePlane.fst k₀ ≫ _ = _ by
    rw [affineLine.zeroFibre_fst_assoc, affineLine.zero_over]
    rw [Category.comp_id]⟩

instance : IsClosedImmersion (affineLine.zeroFibre k₀) := by
  have : IsClosedImmersion (affineLine.zeroFibre k₀ ≫ affinePlane.snd k₀) := by
    rw [affineLine.zeroFibre_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (affinePlane.snd k₀)

omit [Finite k₀] in
/-- The line `ξ ↦ (0, ξ)` is the fibre of the first projection `pr₁ : 𝔸² ⟶ 𝔸¹` over the
origin. -/
theorem affineLine.isPullback_zeroFibre :
    IsPullback (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine.zeroFibre k₀)
      (affineLine.zero k₀) (affinePlane.fst k₀) := by
  have h₀ : IsPullback (affinePlane.snd k₀) (affinePlane.fst k₀)
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (affineLine.zeroFibre k₀ ≫ affinePlane.snd k₀)
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine.zero k₀ ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [affineLine.zeroFibre_snd, affineLine.zero_over]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (IsPullback.of_right s affineLine.zeroFibre_fst h₀).flip



omit [Finite k₀] in
/-- The function `x ξ` on the affine plane vanishes on the line `ξ ↦ (0, ξ)`. -/
lemma affineLine.zeroFibre_appTop_mul :
    (affineLine.zeroFibre k₀).appTop
      ((affinePlane.fst k₀).appTop (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit) *
        (affinePlane.snd k₀).appTop (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit)) =
      0 := by
  have h : (affineLine.zeroFibre k₀).appTop
      ((affinePlane.fst k₀).appTop (AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit)) =
      0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, affineLine.zeroFibre_fst,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineLine.zero,
      AffineSpace.zeroSection_appTop_coord, map_zero]
  rw [map_mul, h, zero_mul]

/-- **The transform of the skyscraper at the origin** (blueprint
`lemma-fourier-transform-constant-sheaf`, second formula): `FT_ψ(δ₀) ≅ ℚ̄_ℓ[1]`. By compact-support
base change along `pr₁`, `pr₁^* δ₀` is the constant complex on the line `ξ ↦ (0, ξ)`; by the
projection formula the kernel `μ^* ℒ_ψ` restricts to `ℒ_{ψ,0} ≅ ℚ̄_ℓ` on it, and `pr₂` maps this
line isomorphically onto the dual line. -/
theorem nonempty_iso_fourierTransform_obj_delta (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty ((fourierTransform ψ).obj (affineLine.delta k₀ l) ≅
      (shiftFunctor _ (1 : ℤ)).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀)))) := by
  let U₀ := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  obtain ⟨BC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affineLine.zero k₀) (affinePlane.fst k₀) (affineLine.zeroFibre k₀)
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) affineLine.isPullback_zeroFibre
  obtain ⟨PF⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse (k₀ := k₀)
    (affineLine.zeroFibre k₀) (fourierKernel (l := l) ψ) (isLisse_fourierKernel ψ)
  -- the kernel restricted to the line `ξ ↦ (0, ξ)` is `ℒ_{ψ,0} ≅ ℚ̄_ℓ`
  obtain ⟨eF⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ
  have eF' : fourierKernel (l := l) ψ ≅ artinSchreierOf ψ m := eF
  obtain ⟨eG⟩ := nonempty_iso_upperStar_artinSchreierOf (affineLine.zeroFibre k₀) ψ m
  obtain ⟨e0⟩ := nonempty_iso_artinSchreierOf_zero (X := affineLine k₀) (l := l) ψ
  have eK : (WeilSheaf.upperStar (affineLine.zeroFibre k₀)).obj (fourierKernel (l := l) ψ) ≅
      WeilSheaf.adicConstant k₀ l (affineLine k₀) :=
    (WeilSheaf.upperStar (affineLine.zeroFibre k₀)).mapIso eF' ≪≫ eG ≪≫
      eqToIso (congrArg (artinSchreierOf ψ) affineLine.zeroFibre_appTop_mul) ≪≫ e0
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso eK
    ((isLisse_fourierKernel ψ).upperStar _) (WeilSheaf.isLisse_adicConstant k₀ l _)
  obtain ⟨eI⟩ := WeilComplex.nonempty_iso_tensorLisse_adicConstant (k₀ := k₀) (l := l)
    (X := affineLine k₀)
  -- `pr₂` maps the line isomorphically onto the dual line
  obtain ⟨eC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineLine.zeroFibre k₀) (affinePlane.snd k₀)
  obtain ⟨eE⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_of_eq (k₀ := k₀) (l := l)
    (affineLine.zeroFibre_snd (k₀ := k₀))
  obtain ⟨eId⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_id (k₀ := k₀) (l := l)
    (X := affineLine k₀)
  let D := WeilComplex.derivedLowerShriek k₀ l (affineLine.zeroFibre k₀)
  have e₁ : (WeilComplex.upperStar (affinePlane.fst k₀)).obj (affineLine.delta k₀ l) ≅ D.obj U :=
    BC.app U₀ ≪≫ D.mapIso (WeilComplex.upperStarAdicConstantIso _)
  have e₂ : (WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).obj (D.obj U) ≅
      D.obj U :=
    PF.app U ≪≫ D.mapIso (eT.app U ≪≫ eI.app U)
  have e₃ : (WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)).obj (D.obj U) ≅ U :=
    (eC.app U).symm ≪≫ eE.app U ≪≫ eId.app U
  exact ⟨(shiftFunctor _ (1 : ℤ)).mapIso
    ((WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)).mapIso
      ((WeilComplex.tensorLisse (fourierKernel ψ) (isLisse_fourierKernel ψ)).mapIso e₁ ≪≫ e₂) ≪≫
      e₃)⟩



/-- **The transform of the constant sheaf** (blueprint `lemma-fourier-transform-constant-sheaf`,
first formula): for a nontrivial additive character `ψ`, `FT_ψ(ℚ̄_ℓ) ≅ δ₀(-1)[-1]`. Here
`FT_ψ(ℚ̄_ℓ) = Rpr₂!(ℒ_ψ(ξ x))[1]` with `pr₂ : (x, ξ) ↦ ξ` the trivial line bundle with fibre
coordinate `x` over the dual line, and the delta kernel computation
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul`)
for the coordinate `ξ`, whose zero locus is the origin, gives `i₀,!(ℚ̄_ℓ(-1)[-2])[1]`. -/
theorem nonempty_iso_fourierTransform_obj_adicConstant (ψ : AddChar k₀ (PadicAlgCl l))
    (hψ : ψ ≠ 1) :
    Nonempty ((fourierTransform ψ).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))) ≅
      (shiftFunctor _ (-1 : ℤ)).obj
        ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj (affineLine.delta k₀ l))) := by
  let U₀ := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  have hi : IsPullback (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
      (affineLine.zero k₀) (AffineSpace.zeroSection PUnit.{u + 1} (Spec (CommRingCat.of k₀)))
      (𝟙 (affineLine k₀)) :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  obtain ⟨e₄⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (l := l) ψ hψ (𝟙 (affineLine k₀)) (affinePlane.snd k₀) (affinePlane.fst k₀)
    (IsPullback.of_hasPullback _ _).flip (affineLine.zero k₀) hi
  -- the kernel `μ^* ℒ_ψ` is `ℒ_ψ(ξ x)`
  have hm : m = (affinePlane.snd k₀).appTop (Scheme.Hom.appTop (𝟙 (affineLine k₀)) X₁) *
      (affinePlane.fst k₀).appTop X₁ := by
    rw [mul_comm]
    rfl
  obtain ⟨eF⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ
  have eF' : fourierKernel (l := l) ψ ≅ artinSchreierOf ψ m := eF
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (eF' ≪≫ eqToIso (congrArg (artinSchreierOf ψ) hm)) (isLisse_fourierKernel ψ)
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eTw⟩ := WeilComplex.nonempty_iso_tateTwist_comp_derivedLowerShriek (k₀ := k₀) (l := l)
    (affineLine.zero k₀) (-1)
  let Z := WeilComplex.derivedLowerShriek k₀ l (affineLine.zero k₀)
  let tw₀ := WeilComplex.tateTwist k₀ l (Spec (CommRingCat.of k₀)) (-1)
  have e₁ : (WeilComplex.upperStar (affinePlane.fst k₀)).obj U ≅
      (WeilComplex.upperStar (affinePlane.snd k₀)).obj U :=
    WeilComplex.upperStarAdicConstantIso _ ≪≫ (WeilComplex.upperStarAdicConstantIso _).symm
  have e₂ : Z.obj ((shiftFunctor _ (-2 : ℤ)).obj (tw₀.obj
      ((WeilComplex.upperStar (affineLine.zero k₀)).obj U))) ≅
      (shiftFunctor _ (-2 : ℤ)).obj
        ((WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)).obj (affineLine.delta k₀ l)) :=
    Z.mapIso ((shiftFunctor _ (-2 : ℤ)).mapIso
        (tw₀.mapIso (WeilComplex.upperStarAdicConstantIso _))) ≪≫
      (Z.commShiftIso (-2 : ℤ)).app _ ≪≫ (shiftFunctor _ (-2 : ℤ)).mapIso (eTw.app U₀)
  exact ⟨(shiftFunctor _ (1 : ℤ)).mapIso
      ((WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)).mapIso
        (eT.app _ ≪≫ (WeilComplex.tensorLisse _ (isLisse_artinSchreierOf ψ _)).mapIso e₁) ≪≫
        e₄.app U ≪≫ e₂) ≪≫
    ((shiftFunctorAdd' _ (-2 : ℤ) 1 (-1) (by norm_num)).app _).symm⟩

end Origin

end AlgebraicGeometry
