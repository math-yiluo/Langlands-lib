/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySeparatedAdjunction

public import WeilConjectures.PointCount
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.StalkRationalPoint
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.WeilSheaf.VerdierDualFinite
public import WeilConjectures.WeilSheaf.VerdierDualLocalization

/-!
# Poincaré duality for a lisse Weil sheaf as an isomorphism of Frobenius modules

Let `X₀` be a smooth separated `k₀`-scheme of finite type and pure dimension `d`, with structure
morphism `a : X₀ ⟶ Spec k₀`, and `F` a lisse Weil sheaf on `X₀`. Poincaré duality identifies
`H^j(X₀ ⊗ k̄, F^∨(d))` with the dual `H_c^i(X₀ ⊗ k̄, F)^∨` for `i + j = 2d`, compatibly with
the geometric Frobenius. It is read off from the duality theory of Weil complexes:

1. `𝔻_X F ≅ F^∨(d)[2d]`, from `ω_X ≅ ℚ̄_ℓ(d)[2d]` and `RHom(F, -) ≅ F^∨ ⊗ -`
   (`AlgebraicGeometry.WeilComplex.nonempty_verdierDual_toComplex_iso_of_isLisse`);
2. the Verdier exchange `𝔻_{Spec k₀} Ra_! F ≅ Ra_* 𝔻_X F`
   (`AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso`);
3. on the point `Spec k₀` the Verdier dual is t-exact and is the coefficient dual in each
   degree, `𝓗⁻ⁱ(𝔻 A) ≅ (𝓗ⁱ A)^∨`
   (`AlgebraicGeometry.WeilComplex.nonempty_homologySheaf_neg_verdierDual_iso`);
4. the global sections of a Weil sheaf on `Spec k₀` are its stalk, and the stalk of a dual is
   the dual of the stalk (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_globalSections_stalkAt`,
   `AlgebraicGeometry.WeilSheaf.stalkAtDualEquiv`).

## Main statements

- `WeilSheaf.nonempty_derivedLowerStar_dual_shift_iso_verdierDual_derivedLowerShriek`:
  `(Ra_* F^∨(d))[2d] ≅ 𝔻(Ra_! F)` as Weil complexes on `Spec k₀`.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_dual_compactlySupportedCohomology`:
  `H^j(X₀ ⊗ k̄, F^∨(d)) ≅ H_c^i(X₀ ⊗ k̄, F)^∨` as Frobenius modules, for `i + j = 2d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Duality on the point.** For a Weil sheaf `H` on `Spec k₀`, which is lisse, the global
sections of the dual `H^∨` are the dual of the global sections of `H`, compatibly with the
Frobenius: both are read on the stalk at the geometric point `Spec k̄ ≅ Spec k₀ ⊗ k̄`. -/
theorem nonempty_equiv_globalSections_dual (H : WeilSheaf k₀ l (Spec (CommRingCat.of k₀)))
    (hH : H.IsLisse) : Nonempty ((H.dual hH).globalSections.Equiv H.globalSections.dual) := by
  have hy := Scheme.Hom.mem_finitePoints_of_comp_eq_id
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) (𝟙 _) (Category.id_comp _)
    (IsLocalRing.closedPoint k₀)
  let y : (Spec (CommRingCat.of k₀)).finitePoints := ⟨_, hy⟩
  have hdy : (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 = 1 :=
    Scheme.Hom.degreeOver_eq_one_of_comp_eq_id _ (𝟙 _) (Category.id_comp _) _
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
  obtain ⟨e₁⟩ := (H.dual hH).nonempty_equiv_globalSections_stalkAt s hs₁
  obtain ⟨e₂⟩ := H.nonempty_equiv_globalSections_stalkAt s hs₁
  exact ⟨e₁.trans ((stalkAtDualEquiv s 1 hs₁ H hH).trans e₂.symm.dual)⟩

/-- **The Verdier dual on the point in degree `-i`**: for a Weil complex `A` on `Spec k₀`,
`𝓗⁻ⁱ(𝔻 A) ≅ (𝓗ⁱ A)^∨`, the Verdier dual on `Spec k₀` being t-exact with `𝔻 (G[0]) ≅ G^∨[0]`. -/
theorem nonempty_homologySheaf_neg_verdierDual_iso_dual
    [WeilComplex.HasUpperShriek k₀ l (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))]
    (A : WeilComplex k₀ l (Spec (CommRingCat.of k₀))) (i : ℤ) :
    Nonempty ((WeilComplex.homologySheaf (-i)).obj
        ((WeilComplex.verdierDual k₀ l (Spec (CommRingCat.of k₀))).obj (op A)) ≅
      ((WeilComplex.homologySheaf i).obj A).dual
        (isLisse_of_isFinite_of_isReduced ((WeilComplex.homologySheaf i).obj A))) := by
  set H := (WeilComplex.homologySheaf i).obj A
  have hH : H.IsLisse := isLisse_of_isFinite_of_isReduced H
  obtain ⟨R₁⟩ := WeilComplex.nonempty_homologySheaf_neg_verdierDual_iso A i
  obtain ⟨R₂⟩ := WeilComplex.nonempty_verdierDual_toComplex_iso_of_isFinite H
  obtain ⟨R₃⟩ := nonempty_dual_tensorObj_tateTwistSheaf_iso H hH 0
  let R₄ : (H.dual hH).constantTwist (cyclotomicUnit k₀ l ^ (0 : ℤ)) ≅ H.dual hH :=
    ObjectProperty.isoMk _ (constantTwistObjIso _ _ ≪≫
      ProEtaleWeilSheaf.constantTwistCongrIso (zpow_zero _) _ ≪≫
      ProEtaleWeilSheaf.constantTwistOneObjIso _)
  exact ⟨R₁ ≪≫ (WeilComplex.homologySheaf 0).mapIso R₂ ≪≫
    toComplexCompHomologySheafIso.app _ ≪≫ R₃ ≪≫ R₄⟩

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Poincaré duality for a lisse Weil sheaf, derived form**: for `X₀` smooth of pure dimension
`d` over `k₀` and `F` lisse, `(Ra_* F^∨(d))[2d] ≅ 𝔻(Ra_! F)` as Weil complexes on `Spec k₀`, by
`𝔻_X F ≅ F^∨(d)[2d]` and the Verdier exchange `𝔻 Ra_! ≅ Ra_* 𝔻_X`. -/
theorem nonempty_derivedLowerStar_dual_shift_iso_verdierDual_derivedLowerShriek (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [WeilComplex.HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
    [WeilComplex.HasUpperShriek k₀ l (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    Nonempty (((WeilComplex.derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj ((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d))))⟦(2 * d : ℤ)⟧ ≅
      (WeilComplex.verdierDual k₀ l (Spec (CommRingCat.of k₀))).obj
        (op ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
          (toComplex.obj F)))) := by
  obtain ⟨eU⟩ := WeilComplex.nonempty_verdierDual_toComplex_iso_of_isLisse d F hF
  obtain ⟨eT⟩ := nonempty_dual_tensorObj_tateTwistSheaf_iso F hF d
  let eG : (F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ (d : ℤ)) ≅
      (F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d) :=
    ObjectProperty.isoMk _ (constantTwistObjIso _ _ ≪≫
      ProEtaleWeilSheaf.constantTwistCongrIso (zpow_natCast _ _) _ ≪≫
      (constantTwistObjIso _ _).symm)
  obtain ⟨eV⟩ := WeilComplex.nonempty_verdierDual_derivedLowerShriek_iso (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀)) (toComplex.obj F)
  let R := WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) (X ↘ Spec (CommRingCat.of k₀))
  exact ⟨((R.commShiftIso (2 * d : ℤ)).app _).symm ≪≫
    R.mapIso (((shiftFunctor _ (2 * d : ℤ)).mapIso (toComplex.mapIso (eT ≪≫ eG))).symm ≪≫
      eU.symm) ≪≫ eV.symm⟩

/-- The cohomology sheaf `𝓗ʲ(Ra_* F^∨(d))` on `Spec k₀` is `𝓗⁻ⁱ(𝔻 Ra_! F)` for `i + j = 2d`:
the degree `-i` part of
`nonempty_derivedLowerStar_dual_shift_iso_verdierDual_derivedLowerShriek`. -/
theorem nonempty_homologySheaf_derivedLowerStar_dual_iso (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [WeilComplex.HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
    [WeilComplex.HasUpperShriek k₀ l (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X} (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    Nonempty ((WeilComplex.homologySheaf j).obj
        ((WeilComplex.derivedLowerStar (X ↘ Spec (CommRingCat.of k₀))).obj
          (toComplex.obj ((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)))) ≅
      (WeilComplex.homologySheaf (-i)).obj
        ((WeilComplex.verdierDual k₀ l (Spec (CommRingCat.of k₀))).obj
          (op ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
            (toComplex.obj F))))) := by
  obtain ⟨e⟩ := nonempty_derivedLowerStar_dual_shift_iso_verdierDual_derivedLowerShriek d hF
  exact ⟨(WeilComplex.homologySheafShiftIso _ (2 * d : ℤ) (-i) j (by lia)).symm ≪≫
    (WeilComplex.homologySheaf (-i)).mapIso e⟩


/-- **Poincaré duality for a lisse Weil sheaf, as an isomorphism of Frobenius modules**
(blueprint `corollary-degreewise-duality-over-fields--1`, with the Frobenius equivariance of
`theorem-poincare-duality-frobenius--3`): for `X₀` smooth, separated, of finite type and
pure dimension `d` over `k₀`, `F` lisse and `i + j = 2d`,
`H^j(X₀ ⊗ k̄, F^∨(d)) ≅ H_c^i(X₀ ⊗ k̄, F)^∨`, the dual carrying the inverse transpose of the
Frobenius. Here `F^∨(d)` is the constant twist of `F^∨` by `χ_ℓ(σ)ᵈ`. -/
theorem nonempty_equiv_cohomology_dual_compactlySupportedCohomology (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    Nonempty ((((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).Equiv
      (F.compactlySupportedCohomology i).dual) := by
  have := WeilComplex.isLeftAdjoint_derivedLowerShriek_of_separated_base (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀))
  have := WeilComplex.isLeftAdjoint_derivedLowerShriek_of_separated_base (k₀ := k₀) (l := l)
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
  obtain ⟨E₁⟩ := nonempty_homologySheaf_derivedLowerStar_dual_iso d hF i j h
  obtain ⟨E₂⟩ := nonempty_homologySheaf_neg_verdierDual_iso_dual
    ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F)) i
  obtain ⟨D⟩ := nonempty_equiv_globalSections_dual _
    (isLisse_of_isFinite_of_isReduced ((WeilComplex.homologySheaf i).obj
      ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj F))))
  exact ⟨(globalSectionsEquivOfIso (E₁ ≪≫ E₂)).trans D⟩

end AlgebraicGeometry.WeilSheaf
