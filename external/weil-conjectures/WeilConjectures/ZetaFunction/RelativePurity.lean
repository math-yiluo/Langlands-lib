/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy
public import WeilConjectures.DeligneLaumon.Reduction.DirectImage
public import WeilConjectures.DeligneLaumon.Reduction.MixedStalk
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.AlgebraicGeometry.ResidueFieldFiniteEtale
public import WeilConjectures.WeilSheaf.FiniteLeray
public import WeilConjectures.WeilSheaf.FinitePointCohomology
public import WeilConjectures.WeilSheaf.ProperBaseChange
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaFunction.LissePurity
public import WeilConjectures.ZetaFunction.Weights
public import WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteness

/-!
# Relative purity for smooth proper morphisms

Let `f : X₀ ⟶ Y₀` be a smooth proper morphism of pure relative dimension `d` of separated
`k₀`-schemes of finite type, and `F` a lisse Weil sheaf on `X₀` which is punctually `ι`-pure of
weight `w`. Then for every `i` (blueprint `theorem-purity-higher-direct-images-under`, the relative
clauses of `theorem-purity-higher-direct-images-under`):

- **(a)** `Rⁱf₀!F ≅ Rⁱf₀*F` as Weil sheaves, and this sheaf is lisse;
- **(b)** it is punctually `ι`-pure of weight `w + i`.

The upper bound on the weights is the Deligne–Laumon direct-image theorem
(`AlgebraicGeometry.hasDirectImageWeightBound_over_finiteField`).
The lower bound in (b) is proved fibrewise rather than by the relative Verdier duality of the
blueprint proof (Step 3), which needs `RHom`, `Rf^!` and the smooth orientation for Weil
complexes (not available, see `WeilConjectures.WeilSheaf.Operations`). For a closed point `y`,
proper base change to `Spec κ(y)` (`theorem-purity-higher-direct-images-under--2`), the Leray
isomorphism over the finite étale `Spec κ(y)` and purity of `Hⁱ(X_y ⊗ k̄, F)` for lisse coefficients
(Deligne–Laumon and degreewise Poincaré duality `corollary-degreewise-duality-over-fields--1` on the
smooth proper fibre `X_y`) give purity of the stalk of `Rⁱf₀*F` at `y`.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarOfIsProper`:
  `Rf₀!K ≅ Rf₀*K` for a proper `f`.
- `AlgebraicGeometry.WeilSheaf.higherLowerShriekObjIsoOfIsProper`: `Rⁱf₀!F ≅ Rⁱf₀*F`.
- `AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_higherLowerStar_of_isProper`: the upper
  bound for proper `f`.
- `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_higherLowerStar`: clause (b).
- `AlgebraicGeometry.WeilSheaf.smooth_proper_relative_purity`: clauses (a) and (b) together.
- `AlgebraicGeometry.WeilSheaf.isPunctuallyPureOfWeight_higherLowerStar_adicConstant`: the case
  of the constant sheaf.

## Implementation notes

The local constancy of Step 1 is
`ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`
(`WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLisse`), for the `ℓ`-adic sheaves on the
geometric fibres (the Weil-level
`AlgebraicGeometry.WeilSheaf.isLisse_higherLowerStar_of_smooth_of_isProper` is derived from it).
Following the blueprint, a lattice of `F` exists étale locally on the base: on the regular
geometric fibres by the finite orbits of lattices, and nearby by proper base change in degree
zero for the sheaf of lattices; on a lattice the finite-level smooth proper base change theorems
apply.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

/-- **Local constancy over a point.** Over an algebraically closed field `K` of characteristic
`≠ ℓ`, the higher direct images of a lisse `ℓ`-adic sheaf along any quasi-compact quasi-separated
morphism of finite type `f : X ⟶ Spec K` are lisse: they are constructible by the finiteness
theorem, and a constructible sheaf on the spectrum of a field is lisse. This is the case of the
point of `isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_isField
    (f : X ⟶ Spec (.of K)) (hK : ringChar K ≠ l) [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj
      ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  (isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar (𝟙 _) f hK
    hF.isAdicConstructibleSheaf n).isAdicLisseSheaf_of_isField

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]

section ProperCoincidence

attribute [local instance] Compactification.over

/-- **Proper coincidence.** For a proper morphism `f` of `k₀`-schemes the direct image with
compact support is the direct image: for the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`
the open immersion `i` is proper, so that `Rf_! K = Rg_*(i_! K) ≅ Rg_*(i_* K) ≅ Rf_* K`, as Weil
complexes (blueprint `theorem-purity-higher-direct-images-under`, Step 1, and
`proposition-forgetting-supports-composition--3`). -/
noncomputable def WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarOfIsProper (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (WeilComplex.derivedLowerShriek k₀ l f).obj K ≅ (WeilComplex.derivedLowerStar f).obj K := by
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have : IsProper c.i := c.isProper_openImmersion inferInstance
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  refine ObjectProperty.isoMk _ ?_
  change (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).mapDerivedCategory.obj K.obj) ≅ _
  exact (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).rightDerivedFunctorIsoMapDerivedCategory.app
        K.obj).symm ≪≫
    (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompIso
      (ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso l c.i
        (comp_over c.i _))
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l c.g (comp_over c.g _))).symm.app
        K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (Functor.isoWhiskerRight
      (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l c.i))
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g))).app K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCompIso k₀ l c.i c.g)).app
      K.obj ≪≫
    (Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l c.comm.symm)).app
      K.obj

/-- **Proper coincidence for higher direct images** (clause (a) of
`theorem-purity-higher-direct-images-under`, first half): for a proper morphism `f` of `k₀`-schemes,
`Rⁱf₀!F ≅ Rⁱf₀*F` as Weil sheaves. -/
noncomputable def WeilSheaf.higherLowerShriekObjIsoOfIsProper (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (i : ℕ) (F : WeilSheaf k₀ l X) :
    (WeilSheaf.higherLowerShriek k₀ l f i).obj F ≅ (WeilSheaf.higherLowerStar f i).obj F :=
  (WeilComplex.homologySheaf i).mapIso
    (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStarOfIsProper f (WeilSheaf.toComplex.obj F))

end ProperCoincidence

namespace WeilSheaf

variable {ι : PadicAlgCl l →+* ℂ}

section Relative

variable (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **Upper bound** (Step 2 of `theorem-purity-higher-direct-images-under`): for a proper morphism
`f` of separated `k₀`-schemes of finite type and a Weil sheaf `F` mixed of weights at most `w`,
`Rⁱf₀*F ≅ Rⁱf₀!F` is mixed of weights at most `w + i`, by the Deligne–Laumon theorem
`theorem-direct-image-mixed-sheaf--1`. -/
theorem isMixedOfWeightsAtMost_higherLowerStar_of_isProper {F : WeilSheaf k₀ l X} {w : ℝ}
    (hF : F.IsMixedOfWeightsAtMost ι w) (i : ℕ) :
    ((higherLowerStar f i).obj F).IsMixedOfWeightsAtMost ι (w + i) :=
  (hasDirectImageWeightBound_over_finiteField ι f w F hF i).of_iso
    (higherLowerShriekObjIsoOfIsProper f i F)

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- **Local constancy** (Step 1 of `theorem-purity-higher-direct-images-under`, second half of
clause (a)): for a smooth proper morphism `f` and a lisse Weil sheaf `F`, the higher direct
images `Rⁱf₀*F` are lisse. The underlying `ℓ`-adic sheaf of `Rⁱf₀*F` is the higher direct image
`Rⁱf̄_* F̄` along the base change `f̄` to the geometric fibres, forgetting the Weil structure
commuting with right derivation; so this is
`ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper`. -/
theorem isLisse_higherLowerStar_of_smooth_of_isProper [hs : Smooth f] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse)
    (i : ℕ) : ((higherLowerStar f i).obj F).IsLisse := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have : Smooth (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) f _ hs
  have : IsProper (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) f _ ‹_›
  let e : (IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l f).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj)) ≅
      (Scheme.Hom.geometricFiberMap f
        (comp_over f (Spec (CommRingCat.of k₀))))_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj.carrier) :=
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
      Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app F.obj)
  exact (ProEtale.isAdicLisseSheaf_homology_rightDerivedFunctor_lowerStar_of_smooth_of_isProper
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _
    ringChar_algebraicClosure_ne hF i).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ i).mapIso e.symm ≪≫
        ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso i).symm.app _)

variable (d : ℕ) [SmoothOfRelativeDimension d f]

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
include d in
/-- **Clause (b) of `theorem-purity-higher-direct-images-under`**: for a smooth proper morphism `f`
of pure relative dimension `d` between separated `k₀`-schemes of finite type and a lisse Weil
sheaf `F` punctually `ι`-pure of weight `w`, the sheaf `Rⁱf₀*F` is punctually `ι`-pure of weight
`w + i`.

The proof is fibrewise. For a closed point `y` of `Y₀`, let `P = Spec κ(y)`, a finite étale
`k₀`-scheme, and `X_y = X₀ ×_{Y₀} P`, smooth and proper of pure dimension `d` over `k₀`. By proper
base change (`AlgebraicGeometry.WeilSheaf.nonempty_upperStar_higherLowerStar_iso_of_isProper`) the
pullback of `Rⁱf₀*F` to `P` is `Rⁱf_{y*}(F|_{X_y})`. Over the finite étale `P` the Leray
isomorphism gives `Hⁱ(X_y ⊗ k̄, F) ≅ Γ(P̄, Rⁱf_{y*}F)`, which is pure of weight `w + i` by purity
for lisse coefficients (`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_cohomology_of_isLisse`,
Deligne–Laumon and Poincaré duality on `X_y`); the stalk eigenvalues at the closed point of `P` are
powers of those of `Γ(P̄, -)`, and the stalk at `y` has the same local Frobenius. -/
theorem isPunctuallyPureOfWeight_higherLowerStar {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    ((higherLowerStar f i).obj F).IsPunctuallyPureOfWeight ι (w + i) := by
  intro y
  -- the closed point `y` as the finite étale `k₀`-scheme `P = Spec κ(y)`
  let P := Spec (Y.residueField y.1)
  let iy : P ⟶ Y := Y.fromSpecResidueField y.1
  let : P.Over (Spec (CommRingCat.of k₀)) :=
    ⟨Spec.map (CommRingCat.ofHom ((Y ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap y.1))⟩
  have hiy : iy ≫ (Y ↘ Spec (CommRingCat.of k₀)) = P ↘ Spec (CommRingCat.of k₀) :=
    ((Y ↘ Spec (CommRingCat.of k₀)).specMap_residueFieldAlgebraMap y.1).symm
  have : iy.IsOver (Spec (CommRingCat.of k₀)) := ⟨hiy⟩
  obtain ⟨hPf, hPe⟩ := isFinite_and_etale_specMap_residueFieldAlgebraMap
    (Y ↘ Spec (CommRingCat.of k₀)) y.2
  have : IsFinite (P ↘ Spec (CommRingCat.of k₀)) := hPf
  have : Etale (P ↘ Spec (CommRingCat.of k₀)) := hPe
  have : LocallyOfFiniteType (P ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (P ↘ Spec (CommRingCat.of k₀)) := inferInstance
  -- the fibre `X_y = X ×_Y P`
  let Xy := pullback f iy
  let fy : Xy ⟶ P := pullback.snd f iy
  let g : Xy ⟶ X := pullback.fst f iy
  let : Xy.Over (Spec (CommRingCat.of k₀)) := ⟨fy ≫ (P ↘ Spec (CommRingCat.of k₀))⟩
  have : fy.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : g.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change g ≫ (X ↘ Spec (CommRingCat.of k₀)) = fy ≫ (P ↘ Spec (CommRingCat.of k₀))
    rw [← comp_over f (Spec (CommRingCat.of k₀)), ← hiy, ← Category.assoc, pullback.condition,
      Category.assoc]⟩
  have hfyP : IsProper fy := inferInstance
  have : QuasiCompact fy := inferInstance
  have : QuasiSeparated fy := inferInstance
  have : LocallyOfFiniteType fy := inferInstance
  have : SmoothOfRelativeDimension d fy := inferInstance
  have : SmoothOfRelativeDimension d (Xy ↘ Spec (CommRingCat.of k₀)) := by
    have := smoothOfRelativeDimension_comp (n := d) (m := 0) fy (P ↘ Spec (CommRingCat.of k₀))
    simpa using this
  have : IsProper (Xy ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (IsProper (fy ≫ (P ↘ Spec (CommRingCat.of k₀))))
  have : IsSeparated (Xy ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (Xy ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiSeparated (Xy ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : LocallyOfFiniteType (Xy ↘ Spec (CommRingCat.of k₀)) := inferInstance
  -- purity of the cohomology of the fibre, of `Rⁱf_{y*}`, and of the base change
  have hF' := hF.upperStar g
  have hw' := hw.upperStar g
  obtain ⟨e⟩ := nonempty_equiv_cohomology_globalSections_higherLowerStar fy ((upperStar g).obj F) i
  have h1 := isPureOfWeightOver_cohomology_of_isLisse d hF' hw' i
  have h2 := h1.of_equiv e.symm
  have hG : ((higherLowerStar fy i).obj ((upperStar g).obj F)).IsPunctuallyPureOfWeight ι
      (w + ((i : ℤ) : ℝ)) := isPunctuallyPureOfWeight_of_isPureOfWeightOver_globalSections h2
  obtain ⟨e'⟩ := nonempty_upperStar_higherLowerStar_iso_of_isProper (X' := Xy) (f' := fy)
    (g' := g) ‹IsProper f›
    (IsPullback.of_hasPullback f iy) F i
  -- the closed point of `P` over `y`
  have hK : Finite (Y.residueField y.1) := y.2
  let p : P.finitePoints := ⟨_, closedPoint_mem_finitePoints
    (K := Y.residueField y.1)⟩
  have hp : iy.base p.1 = y.1 := Y.fromSpecResidueField_apply y.1 _
  obtain ⟨E⟩ := nonempty_equiv_stalk_of_iso e' p
  have h3 := (hG p).of_equiv E
  have h4 := (isPureOfWeight_stalk_upperStar_iff iy ((higherLowerStar f i).obj F) p).1 h3
  have hy : (⟨iy.base p.1, Scheme.Hom.map_mem_finitePoints iy p.2⟩ : Y.finitePoints) = y :=
    Subtype.ext hp
  rw [hy, hp, Int.cast_natCast] at h4
  exact h4


omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
include d in
/-- **Relative smooth-proper purity** (blueprint `theorem-purity-higher-direct-images-under`, and
the relative clauses (a), (b) of `theorem-purity-higher-direct-images-under`): let `f : X₀ ⟶ Y₀` be
a smooth proper morphism of pure relative dimension `d` between separated `k₀`-schemes of finite
type and `F` a lisse Weil sheaf on `X₀`, punctually `ι`-pure of weight `w`. Then for every `i`:

- (a) the canonical map `Rⁱf₀!F ⟶ Rⁱf₀*F` is an isomorphism of Weil sheaves, namely
  `(higherLowerShriekObjIsoOfIsProper f i F).hom`, and this sheaf is lisse;
- (b) it is punctually `ι`-pure of weight `w + i`. -/
theorem smooth_proper_relative_purity {F : WeilSheaf k₀ l X} (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (i : ℕ) :
    IsIso (higherLowerShriekObjIsoOfIsProper f i F).hom ∧
      ((higherLowerStar f i).obj F).IsLisse ∧
      ((higherLowerStar f i).obj F).IsPunctuallyPureOfWeight ι (w + i) :=
  ⟨inferInstance, isLisse_higherLowerStar_of_smooth_of_isProper f
    (hs := SmoothOfRelativeDimension.smooth d f) hF i,
    isPunctuallyPureOfWeight_higherLowerStar f d hF hw i⟩

omit [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
include d in
/-- The case of the constant sheaf (relative form of
`corollary-purity-cohomology-smooth-proper-variety--1`): for a smooth proper morphism `f` of
separated `k₀`-schemes of finite type, `Rⁱf₀*ℚ̄_ℓ` is punctually `ι`-pure of weight `i`, the
constant sheaf being lisse and punctually pure of weight `0`. -/
theorem isPunctuallyPureOfWeight_higherLowerStar_adicConstant (i : ℕ) :
    ((higherLowerStar f i).obj (adicConstant k₀ l X)).IsPunctuallyPureOfWeight ι i := by
  simpa using isPunctuallyPureOfWeight_higherLowerStar f d (isLisse_adicConstant k₀ l X)
    (isPunctuallyPureOfWeight_adicConstant (k₀ := k₀) (l := l) (X := X) (ι := ι)) i

end Relative

end WeilSheaf

end AlgebraicGeometry
