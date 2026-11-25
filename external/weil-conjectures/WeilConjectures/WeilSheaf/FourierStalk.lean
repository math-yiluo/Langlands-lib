/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierFunctions
public import WeilConjectures.WeilSheaf.ArtinSchreierPullback
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierTateTwist
public import WeilConjectures.WeilSheaf.FourierTraceAux
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.LowerShriekOperations
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.WeilSheaf.StalkRationalPoint
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-!
# Stalks of the Fourier–Deligne transform at rational points

At a `k₀`-rational point `a` of the dual line, the stalk of the Fourier–Deligne transform of a
Weil complex `K` is the compactly supported cohomology of `K ⊗ ℒ_{ψ(a x)}`, shifted by one, with
its Frobenius: this is the stalk formula of the transform, a consequence of compact support base
change along `a : Spec k₀ ⟶ 𝔸¹`. At the origin the kernel `ℒ_{ψ(0 · x)}` is the constant sheaf,
and tensoring with it does nothing.

## Main declarations

- `AlgebraicGeometry.affineLine.rationalPoint`: the closed point `x = a` of `𝔸¹_{k₀}`.
- `AlgebraicGeometry.nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint`: the
  stalk formula at rational points (blueprint `proposition-base-change-fourier-inversion--3`), by
  compact support base change along `AlgebraicGeometry.affineLine.rationalPointHom` and the
  restriction of the kernel to the fibre `AlgebraicGeometry.affineLine.fibreInclusion`.
- `AlgebraicGeometry.nonempty_iso_artinSchreier_zero`: `ℒ_{ψ(0 · x)} ≅ ℚ̄_ℓ` (blueprint
  `lemma-artin-schreier-character-sheaf`), from `AS^* ℒ_ψ ≅ ℚ̄_ℓ`.
- `AlgebraicGeometry.WeilComplex.tensorLisseObjIsoOfIso`: tensoring with a Weil sheaf isomorphic
  to `ℚ̄_ℓ` is the identity.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀) in
/-- The `k₀`-rational point `x = a` of the affine line, as a closed point. -/
noncomputable def affineLine.rationalPoint (a : k₀) : (affineLine k₀).finitePoints :=
  ⟨(AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀)))
      fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom a).base (IsLocalRing.closedPoint k₀),
    Scheme.Hom.mem_finitePoints_of_comp_eq_id (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) _
      (AffineSpace.homOfVector_over _ _) _⟩

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The derived internal hom `R𝓗om(F^∨, -)` out of the dual of a Weil sheaf `F ≅ ℚ̄_ℓ` is the
identity: `F^∨ ≅ 𝓗om(ℚ̄_ℓ, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, the functor `𝓗om(ℚ̄_ℓ, -)` is the identity, and so is
its derived functor. -/
noncomputable def rightDerivedFunctorIhomFunctorDualIsoOfIso (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (e : F ≅ WeilSheaf.adicConstant k₀ l X) :
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X (F.dual hF).obj).rightDerivedFunctor ≅
      𝟭 (_root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :=
  have eD : (F.dual hF).obj ≅ ProEtaleWeilSheaf.adicConstant k₀ l X :=
    (ProEtaleWeilSheaf.ihomMapIsoLeft ((ObjectProperty.ι _).mapIso e).symm _) ≪≫
      ProEtaleWeilSheaf.ihomAdicConstantIso _
  Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.ihomFunctorMapIsoLeft eD.symm ≪≫
      ProEtaleWeilSheaf.ihomFunctorAdicConstantIso k₀ l X) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Tensoring with a lisse Weil sheaf `F ≅ ℚ̄_ℓ` does not change a Weil complex. -/
noncomputable def tensorLisseObjIsoOfIso (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (e : F ≅ WeilSheaf.adicConstant k₀ l X) (K : WeilComplex k₀ l X) :
    (tensorLisse F hF).obj K ≅ K :=
  ObjectProperty.isoMk _ ((rightDerivedFunctorIhomFunctorDualIsoOfIso F hF e).app K.obj)

end WeilComplex

/-- `ℒ_{ψ(0 · x)}`, the Artin–Schreier sheaf of the zero function, is the constant Weil sheaf
`ℚ̄_ℓ`: over the zero function the Artin–Schreier cover is split, `#k₀` copies of the line with
trivial Frobenius, so all the isotypic summands of the pushforward are constant. It is the unit
of the kernel family `ℒ_{ψ(a x)}`. (blueprint: `lemma-artin-schreier-character-sheaf`, the case
`f = 0`) -/
theorem nonempty_iso_artinSchreier_zero (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreier ψ 0 ≅ WeilSheaf.adicConstant k₀ l (affineLine k₀)) :=
  nonempty_artinSchreier_zero_iso_adicConstant ψ

section RationalPoint

variable (k₀) in
/-- The `k₀`-rational point `x = a` of the affine line, as a morphism `Spec k₀ ⟶ 𝔸¹`. -/
noncomputable def affineLine.rationalPointHom (a : k₀) :
    Spec (CommRingCat.of k₀) ⟶ affineLine k₀ :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k₀)))
    fun _ ↦ (Scheme.ΓSpecIso (.of k₀)).inv.hom a

instance (a : k₀) : (affineLine.rationalPointHom k₀ a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨AffineSpace.homOfVector_over _ _⟩

omit [Finite k₀] in
lemma affineLine.rationalPointHom_comp_over (a : k₀) :
    affineLine.rationalPointHom k₀ a ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀) = 𝟙 _ :=
  AffineSpace.homOfVector_over _ _

variable (k₀) in
/-- The fibre `x ↦ (x, a)` of the second projection `pr₂ : 𝔸² ⟶ 𝔸¹` over the rational point
`a`. -/
noncomputable def affineLine.fibreInclusion (a : k₀) : affineLine k₀ ⟶ affinePlane k₀ :=
  pullback.lift (𝟙 _) (affineLine k₀ ↘ Spec (CommRingCat.of k₀) ≫ affineLine.rationalPointHom k₀ a)
    (by rw [Category.assoc, affineLine.rationalPointHom_comp_over, Category.comp_id,
      Category.id_comp])

omit [Finite k₀] in
lemma affineLine.fibreInclusion_fst (a : k₀) :
    affineLine.fibreInclusion k₀ a ≫ affinePlane.fst k₀ = 𝟙 _ :=
  pullback.lift_fst _ _ _

omit [Finite k₀] in
lemma affineLine.fibreInclusion_snd (a : k₀) :
    affineLine.fibreInclusion k₀ a ≫ affinePlane.snd k₀ =
      affineLine k₀ ↘ Spec (CommRingCat.of k₀) ≫ affineLine.rationalPointHom k₀ a :=
  pullback.lift_snd _ _ _

instance (a : k₀) : (affineLine.fibreInclusion k₀ a).IsOver (Spec (CommRingCat.of k₀)) :=
  ⟨by
    change _ ≫ pullback.fst _ _ ≫ _ = _
    rw [← Category.assoc]
    exact (congrArg (· ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine.fibreInclusion_fst a)).trans (Category.id_comp _)⟩

omit [Finite k₀] in
/-- The fibre of `pr₂ : 𝔸² ⟶ 𝔸¹` over the rational point `a` is the line `x ↦ (x, a)`. -/
lemma affineLine.isPullback_fibreInclusion (a : k₀) :
    IsPullback (affineLine.fibreInclusion k₀ a) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affinePlane.snd k₀) (affineLine.rationalPointHom k₀ a) := by
  have hout : IsPullback (affineLine.fibreInclusion k₀ a ≫ affinePlane.fst k₀)
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
      (affineLine.rationalPointHom k₀ a ≫ affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [affineLine.fibreInclusion_fst, affineLine.rationalPointHom_comp_over]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  exact hout.of_right (affineLine.fibreInclusion_snd a) (IsPullback.of_hasPullback _ _)

omit [Finite k₀] in
/-- Along the fibre `x ↦ (x, a)`, the product `x ξ` restricts to `a x`: with the scaling,
`ι_a ≫ μ ≫ (1 ·) = (a ·)`. -/
lemma affineLine.fibreInclusion_comp_mul_comp_smul_one (a : k₀) :
    affineLine.fibreInclusion k₀ a ≫ affinePlane.mul k₀ ≫ affineLine.smul k₀ 1 =
      affineLine.smul k₀ a := by
  have hc : (affineLine.fibreInclusion k₀ a).appTop
      ((affinePlane k₀ ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom 1) *
        ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
          (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit))) =
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom a) *
        AffineSpace.coord _ PUnit.unit := by
    have h₁ : (affineLine.fibreInclusion k₀ a).appTop
        ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
          (affineLine.fibreInclusion k₀ a ≫ affinePlane.fst k₀).appTop
            (AffineSpace.coord _ PUnit.unit) := rfl
    have h₂ : (affineLine.fibreInclusion k₀ a).appTop
        ((affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit)) =
          (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).appTop
            ((affineLine.rationalPointHom k₀ a).appTop (AffineSpace.coord _ PUnit.unit)) := by
      change (affineLine.fibreInclusion k₀ a ≫ affinePlane.snd k₀).appTop _ = _
      rw [affineLine.fibreInclusion_snd]
      rfl
    rw [map_mul, map_mul, h₁, h₂, affineLine.fibreInclusion_fst, affineLine.rationalPointHom,
      AffineSpace.homOfVector_appTop_coord, map_one, map_one, map_one, one_mul, mul_comm]
    rfl
  rw [affinePlane.mul_eq_homOfSection, affineLine.homOfSection_comp_smul,
    affineLine.comp_homOfSection, hc, ← affineLine.homOfSection_comp_smul,
    affineLine.homOfSection_coord, Category.id_comp]

end RationalPoint

/-- Restricted to the fibre `x ↦ (x, a)`, the pullback along `(x, ξ) ↦ 1 · x ξ` is the pullback
along `x ↦ a x`. -/
theorem nonempty_iso_upperStar_fibreInclusion_mul_smul_one (a : k₀)
    (F : WeilSheaf k₀ l (affineLine k₀)) :
    Nonempty ((WeilSheaf.upperStar (affineLine.fibreInclusion k₀ a)).obj
      ((WeilSheaf.upperStar (affinePlane.mul k₀)).obj
        ((WeilSheaf.upperStar (affineLine.smul k₀ 1)).obj F)) ≅
      (WeilSheaf.upperStar (affineLine.smul k₀ a)).obj F) := by
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj (affinePlane.mul k₀)
    (affineLine.smul k₀ 1) _ rfl F
  obtain ⟨e₂⟩ := WeilSheaf.nonempty_iso_upperStar_obj_upperStar_obj
    (affineLine.fibreInclusion k₀ a) (affinePlane.mul k₀ ≫ affineLine.smul k₀ 1) _
    (affineLine.fibreInclusion_comp_mul_comp_smul_one a) F
  exact ⟨(WeilSheaf.upperStar (affineLine.fibreInclusion k₀ a)).mapIso e₁ ≪≫ e₂⟩

/-- The Fourier kernel restricted to the fibre `x ↦ (x, a)` is `ℒ_{ψ(a x)}`. -/
theorem nonempty_iso_upperStar_fibreInclusion_fourierKernel (ψ : AddChar k₀ (PadicAlgCl l))
    (a : k₀) :
    Nonempty ((WeilSheaf.upperStar (affineLine.fibreInclusion k₀ a)).obj (fourierKernel ψ) ≅
      artinSchreier ψ a) := by
  obtain ⟨e⟩ : Nonempty ((WeilSheaf.upperStar (affineLine.fibreInclusion k₀ a)).obj
      ((WeilSheaf.upperStar (affinePlane.mul k₀)).obj (artinSchreier ψ 1)) ≅
        artinSchreier ψ a) := by
    rw [artinSchreier, artinSchreier]
    exact nonempty_iso_upperStar_fibreInclusion_mul_smul_one a _
  exact ⟨(WeilSheaf.upperStar (affineLine.fibreInclusion k₀ a)).mapIso (fourierKernelIso ψ) ≪≫ e⟩

/-- **The fibre of the Fourier transform over a rational point**: pulled back to the point
`a : Spec k₀ ⟶ 𝔸¹`, the transform `FT_ψ(K)` is `RΓ_c(𝔸¹, K ⊗ ℒ_{ψ(a x)})[1]`, by compact support
base change along `a` and the restriction `ℒ_{ψ(a x)}` of the kernel to the fibre. -/
theorem nonempty_iso_fourierTransform_comp_upperStar_rationalPointHom
    (ψ : AddChar k₀ (PadicAlgCl l)) (a : k₀) :
    Nonempty (fourierTransform ψ ⋙ WeilComplex.upperStar (affineLine.rationalPointHom k₀ a) ≅
      WeilComplex.tensorLisse (artinSchreier ψ a) (isLisse_artinSchreier ψ a) ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) ⋙
          shiftFunctor _ (1 : ℤ)) := by
  obtain ⟨BC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affinePlane.snd k₀) (affineLine.rationalPointHom k₀ a)
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) (affineLine.fibreInclusion k₀ a)
    (affineLine.isPullback_fibreInclusion a)
  obtain ⟨TL⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar
    (affineLine.fibreInclusion k₀ a) (fourierKernel ψ) (isLisse_fourierKernel ψ)
  obtain ⟨eK⟩ := nonempty_iso_upperStar_fibreInclusion_fourierKernel (l := l) ψ a
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso eK
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_fourierKernel ψ)) (isLisse_artinSchreier ψ a)
  -- `ι_a^* ∘ pr₁^* ≅ (ι_a ≫ pr₁)^* = 𝟙^* ≅ 𝟭`
  have eP : WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀) ⋙
      WeilComplex.upperStar (affineLine.fibreInclusion k₀ a) ≅ 𝟭 _ :=
    (WeilComplex.upperStarCompIso _ _).symm ≪≫
      WeilComplex.upperStarCongrIso (affineLine.fibreInclusion_fst a) ≪≫
      WeilComplex.upperStarIdIso _
  rw [fourierTransform_eq]
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ((WeilComplex.upperStar
          (affineLine.rationalPointHom k₀ a)).commShiftIso (1 : ℤ)) ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight BC _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight TL _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eP _ ≪≫ Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerRight eT _⟩

/-- **Stalks of the Fourier transform are fibre integrals**, at the `k₀`-rational points of the
dual line: for a Weil complex `K` on `𝔸¹` and `a ∈ k₀`, the stalk of `𝓗ʳ FT_ψ(K)` at the point
`a` is `H_c^{r+1}(𝔸¹ ⊗ k̄, K ⊗ ℒ_{ψ(a x)})`, with its Frobenius. The fibre of the second
projection over `a` is the line `x ↦ (x, a)`, along which the kernel `μ^* ℒ_ψ` restricts to
`ℒ_{ψ(a x)}`, and compact support base change along `a : Spec k₀ ⟶ 𝔸¹` identifies the stalk of
`Rpr₂!` with the compactly supported cohomology of the fibre, compatibly with the Weil
structures; the shift `[1]` of the transform moves `r` to `r + 1`.
(blueprint: `proposition-base-change-fourier-inversion--3`) -/
theorem nonempty_equiv_stalk_homologySheaf_fourierTransform_rationalPoint
    (ψ : AddChar k₀ (PadicAlgCl l)) (K : WeilComplex k₀ l (affineLine k₀)) (a : k₀) (r : ℤ) :
    Nonempty ((((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K)).stalk
      (affineLine.rationalPoint k₀ a)).Equiv
        (((WeilComplex.tensorLisse (artinSchreier ψ a) (isLisse_artinSchreier ψ a)).obj
          K).compactlySupportedCohomology (r + 1))) := by
  set p := affineLine.rationalPointHom k₀ a
  -- the unique point of `Spec k₀`, of degree one, mapping to the rational point `a`
  have hy := Scheme.Hom.mem_finitePoints_of_comp_eq_id
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) (𝟙 _) (Category.id_comp _)
    (IsLocalRing.closedPoint k₀)
  let y : (Spec (CommRingCat.of k₀)).finitePoints := ⟨_, hy⟩
  have hdy : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 = 1 :=
    Scheme.Hom.degreeOver_eq_one_of_comp_eq_id _ (𝟙 _) (Category.id_comp _) _
  have hdx : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).degreeOver
      (affineLine.rationalPoint k₀ a).1 = 1 :=
    Scheme.Hom.degreeOver_eq_one_of_comp_eq_id _ p (affineLine.rationalPointHom_comp_over a) _
  obtain ⟨e₁⟩ := WeilSheaf.nonempty_equiv_stalk_upperStar p
    ((WeilComplex.homologySheaf r).obj ((fourierTransform ψ).obj K)) y
    (affineLine.rationalPoint k₀ a) rfl (hdy.trans hdx.symm)
  replace e₁ := e₁.symm
  -- the stalk on the point is the global sections
  set G := (WeilSheaf.upperStar p).obj ((WeilComplex.homologySheaf r).obj
    ((fourierTransform ψ).obj K))
  set s := (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y
  have hs₁ : s ≫ ((Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      1).asIso.hom = (specGeometricFrobenius k₀ ^ 1).asIso.hom ≫ s :=
    hdy ▸ Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ y
  have : IsIso s := by
    have : IsIso (pullback.snd (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
        (Scheme.specAlgebraicClosure k₀).hom) := by
      change IsIso (pullback.snd (𝟙 _) _)
      infer_instance
    have hs : s ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have : IsIso (s ≫ pullback.snd _ _) := by rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_right s (pullback.snd _ _)
  obtain ⟨e₂⟩ := G.nonempty_equiv_stalkAt_of_eq s hdy
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ y) hs₁
  obtain ⟨e₃⟩ := G.nonempty_equiv_globalSections_stalkAt s hs₁
  -- the pullback of the transform to the point
  obtain ⟨E⟩ := nonempty_iso_fourierTransform_comp_upperStar_rationalPointHom (l := l) ψ a
  have E' := E.app K
  simp only [Functor.comp_obj] at E'
  have e₄ := WeilSheaf.globalSectionsEquivOfIso
    ((WeilComplex.homologySheafUpperStarIso p r ((fourierTransform ψ).obj K)).symm ≪≫
      (WeilComplex.homologySheaf r).mapIso E' ≪≫
      WeilComplex.homologySheafShiftIso _ 1 r (r + 1) (add_comm 1 r))
  exact ⟨(e₁.trans (e₂.trans e₃.symm)).trans e₄⟩


end AlgebraicGeometry
