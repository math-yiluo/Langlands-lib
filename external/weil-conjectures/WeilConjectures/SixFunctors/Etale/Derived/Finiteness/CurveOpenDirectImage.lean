/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.OneDimensionalAffineOpens
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageLocalVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.OpenComplement

/-!
# Open direct images on curves

Let `T` be a scheme of finite type and of dimension at most one over a field `k`, `j : U ⟶ T` an
open immersion and `Λ` a torsion ring. Then `R^q j_* M = 0` for `q > 1` and every étale sheaf
`M` of `Λ`-modules on `U` (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isOpenImmersion`,
blueprint `thm-exc-curve-open-dimension-general`), and for `Λ` finite of exponent invertible in
`k` every `R^q j_*` preserves constructibility
(`AlgebraicGeometry.Etale.isConstructibleSheaf_higherDirectImage_of_isOpenImmersion`, blueprint
`corollary-open-direct-image-over-field--1`). So `(U, T)` satisfies the open-complement condition
with constant `1` (`AlgebraicGeometry.Etale.openComplementCondition_one`).

The blueprint proves the vanishing on the geometric stalks, which are the cohomology of the
punctured strict localization: a finite union of spectra of fraction fields of strictly henselian
discrete valuation rings, whose Galois groups have `ℓ`-cohomological dimension one. We argue
instead with affine opens, which avoids the local Galois theory:

* by the limit argument `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isSepClosed`
  it suffices to treat the composite `U_L ⟶ U ⟶ T` for a separably closed field `L` over `k`;
* every point of an étale `T`-scheme `W` has an affine open neighbourhood `V` with `V ×_T U`
  affine (`AlgebraicGeometry.Scheme.exists_isAffineOpen_inf_isAffineOpen`), so `V ×_T U_L` is an
  affine `L`-scheme of finite type and of dimension at most one; by the affine Artin vanishing
  theorem (`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine`, blueprint
  `lemma-uniform-bounds-pro-etale-affines`) its torsion cohomological dimension is at most one;
* the local criterion `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_exists`
  concludes.

The constructibility is the finite-type constructibility theorem
`AlgebraicGeometry.Etale.isConstructibleSheaf_higherDirectImage`
(`proposition-six-operations-dctf--2`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The separably closed case of
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isOpenImmersion`:
let `T` be locally of finite type and of dimension at most one over a field `k`, `j : U ⟶ T` an
open immersion, `L` a separably closed field over `k` and `p₁ : U_L ⟶ U` the base change. Then
`R^q (p₁ ≫ j)_* M = 0` for `q > 1` and every étale sheaf `M` of `Λ`-modules on `U_L`, `Λ` being
torsion. -/
theorem isZero_higherDirectImage_comp_of_isSepClosed (hΛ : IsAddTorsion Λ) {k L : Type u}
    [Field k] [Field L] [IsSepClosed L] {T U P : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] (hT : topologicalKrullDim T ≤ 1) (j : U ⟶ T) [IsOpenImmersion j]
    (s : Spec (.of L) ⟶ Spec (.of k)) (p₁ : P ⟶ U) (p₂ : P ⟶ Spec (.of L))
    (hP : IsPullback p₁ p₂ (j ≫ aT) s) (M : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℤ) (hq : 1 < q) : IsZero (Etale.higherDirectImage Λ (p₁ ≫ j) q M) := by
  refine Etale.isZero_higherDirectImage_of_forall_exists hΛ (p₁ ≫ j) M 1 (fun W y ↦ ?_) q
    (by exact_mod_cast hq)
  have hWe : Etale W.hom := W.prop
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian (W.hom ≫ aT)
  have hW : topologicalKrullDim W.left ≤ 1 := W.hom.topologicalKrullDim_le_of_etale.trans hT
  obtain ⟨V', hV', hyV', hVO⟩ :=
    Scheme.exists_isAffineOpen_inf_isAffineOpen hW (W.hom ⁻¹ᵁ j.opensRange) y
  let V : T.Etale := MorphismProperty.Over.mk ⊤ (V'.ι ≫ W.hom)
    (MorphismProperty.comp_mem _ _ _ inferInstance W.prop)
  let g : V ⟶ W := MorphismProperty.Over.homMk V'.ι rfl trivial
  refine ⟨V, g, ⟨⟨y, hyV'⟩, rfl⟩, ?_⟩
  change (pullback (V'.ι ≫ W.hom) (p₁ ≫ j)).HasTorsionCohomologicalDimensionLE 1
  have : IsAffine (pullback (V'.ι ≫ W.hom) j) :=
    isAffine_pullback_of_isAffineOpen_inf j W.hom V' hVO
  let ℓ : pullback (V'.ι ≫ W.hom) (p₁ ≫ j) ⟶ pullback (V'.ι ≫ W.hom) j :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p₁) (by simp [pullback.condition])
  have hsq : IsPullback (pullback.snd (V'.ι ≫ W.hom) (p₁ ≫ j)) ℓ p₁
      (pullback.snd (V'.ι ≫ W.hom) j) :=
    IsPullback.of_bot (by simpa [ℓ] using (IsPullback.of_hasPullback (V'.ι ≫ W.hom) (p₁ ≫ j)).flip)
      (by simp [ℓ]) (IsPullback.of_hasPullback (V'.ι ≫ W.hom) j).flip
  have : IsAffineHom p₁ := MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance
  have : IsAffineHom ℓ := MorphismProperty.of_isPullback (P := @IsAffineHom) hsq this
  have : IsAffine (pullback (V'.ι ≫ W.hom) (p₁ ≫ j)) := isAffine_of_isAffineHom ℓ
  have hsnd : Etale (pullback.snd (V'.ι ≫ W.hom) (p₁ ≫ j)) := inferInstance
  have : LocallyOfFiniteType p₂ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hP inferInstance
  have hU : topologicalKrullDim U ≤ 1 := j.topologicalKrullDim_le_of_etale.trans hT
  have hPd : topologicalKrullDim P ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ hP.isoPullback.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_pullback_le (j ≫ aT) s).trans hU
  have := Scheme.hasTorsionCohomologicalDimensionLE_of_isAffine
    (Scheme.hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed L)
    (pullback.snd (V'.ι ≫ W.hom) (p₁ ≫ j) ≫ p₂) (d := 1)
    ((pullback.snd (V'.ι ≫ W.hom) (p₁ ≫ j)).topologicalKrullDim_le_of_etale.trans hPd)
  simpa using this

/-- Blueprint `thm-exc-curve-open-dimension-general`: Open direct-image dimension on arbitrary
curves.

Let `T` be a scheme of finite type and of dimension at most one over a field `k`, let
`j : U ⟶ T` be an open immersion and let `Λ` be a ring which is torsion as an additive group.
Then `R^q j_* M = 0` for every `q > 1` and every étale sheaf `M` of `Λ`-modules on `U`. The
blueprint takes for `k` a finite field or its algebraic closure, and `Λ` finite and killed by a
power of a prime invertible on `T`; none of this is needed.

By the limit argument `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_forall_isSepClosed`
this reduces to the separably closed case
`AlgebraicGeometry.Etale.isZero_higherDirectImage_comp_of_isSepClosed`, where the higher direct
images are computed locally on affine opens `V` of étale `T`-schemes with `V ×_T U` affine, of
cohomological dimension at most one by affine Artin vanishing. -/
theorem isZero_higherDirectImage_of_isOpenImmersion (hΛ : IsAddTorsion Λ) {k : Type u} [Field k]
    {T U : Scheme.{u}} (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (hT : topologicalKrullDim T ≤ 1) (j : U ⟶ T) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 1 < q) :
    IsZero (higherDirectImage Λ j q M) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  refine isZero_higherDirectImage_of_forall_isSepClosed Λ (j ≫ aT) aT j rfl M q
    fun L _ _ s P p₁ p₂ hP ↦ ?_
  exact isZero_higherDirectImage_comp_of_isSepClosed hΛ aT hT j s p₁ p₂ hP _ q
    (by exact_mod_cast hq)

variable [Finite Λ]

/-- Blueprint `corollary-open-direct-image-over-field--1`: Open direct-image constructibility on
arbitrary curves.

Let `T` be a scheme of finite type and of dimension at most one over a field `k`, let
`j : U ⟶ T` be an open immersion and let `Λ` be a finite ring whose exponent is invertible in
`k`. For a constructible étale sheaf `F` of `Λ`-modules on `U`, every `R^q j_* F` is
constructible. The blueprint takes for `k` a finite field or its algebraic closure.

This is the finite-type constructibility theorem
`AlgebraicGeometry.Etale.isConstructibleSheaf_higherDirectImage`
(`proposition-six-operations-dctf--2`); the dimension hypothesis is not needed. The blueprint
argues instead with the degree-zero case `thm-fin-open-degree-zero`, the vanishing
`thm-exc-curve-open-dimension-general` above degree one and the finiteness of the degree-one
stalks at the boundary points. -/
theorem isConstructibleSheaf_higherDirectImage_of_isOpenImmersion {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {T U : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] (_hT : topologicalKrullDim T ≤ 1) (j : U ⟶ T)
    [IsOpenImmersion j] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] (q : ℕ) : IsConstructibleSheaf (higherDirectImage Λ j q F) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := ⟨⟩
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact isConstructibleSheaf_higherDirectImage (j ≫ aT) aT j rfl F q

/-- The open-complement condition with constant `1` on curves: for `T` of finite type and of
dimension at most one over a field `k`, an open immersion `j : U ⟶ T` and a finite ring `Λ`
whose exponent is invertible in `k`, `(U, T)` satisfies the open-complement condition of
`theorem-f-shriek-finite-coefficients--1` with `c = 1`. This is the case `d = 1` of
`theorem-f-shriek-finite-coefficients--1` with the sharper constant of
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isOpenImmersion`
(`thm-exc-curve-open-dimension-general`) and
`AlgebraicGeometry.Etale.isConstructibleSheaf_higherDirectImage_of_isOpenImmersion`
(`corollary-open-direct-image-over-field--1`). -/
theorem openComplementCondition_one {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))] {T U : Scheme.{u}} (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] (hT : topologicalKrullDim T ≤ 1) (j : U ⟶ T)
    [IsOpenImmersion j] : OpenComplementCondition Λ j 1 :=
  ⟨fun M q hq ↦ isZero_higherDirectImage_of_isOpenImmersion isAddTorsion_of_finite aT hT j M q hq,
    fun F _ q ↦ isConstructibleSheaf_higherDirectImage_of_isOpenImmersion aT hT j F q⟩

end Etale

end AlgebraicGeometry
