/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.FieldExtension.DirectImageBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.ClosedSupport
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChangeCharts
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.BaseChange
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart

/-!
# Exceptional inverse images and dualizing complexes under field extensions

Let `L/K` be a field extension, `Λ` a finite ring whose exponent is invertible in `K`, and
`f : X ⟶ Spec K` separated and of finite type, with base change `f' : X_L ⟶ Spec L` and
`g' : X_L ⟶ X`. This file proves that the canonical base change map of the exceptional inverse
image `Lg'^* Rf^! Λ ⟶ Rf'^! Λ` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_unit_of_fieldExtension`),
that is, **the dualizing complex commutes with base change along field extensions**:
`Lg'^* ω_{X/K} ≅ ω_{X_L/L}` by the canonical map
(`AlgebraicGeometry.Etale.isIso_dualizingComplexBaseChangeMap_of_fieldExtension`). The extension
may be transcendental and inseparable.

## Proof

* **Closed immersions**
  (`isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion_of_fieldExtension`):
  for a closed immersion `i : Z ⟶ P` into a `K`-scheme of finite type with open complement
  `j`, the base change map of `Ri^!` is invertible at `M` as soon as the derived base change map
  of `Rj_*` is invertible at `j^* M`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso`); for
  bounded below `M` this is Stacks 0F1C
  (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_fieldExtension`).
* **Affine space**: the base change map of the projection `𝔸ⁿ_K ⟶ Spec K` is invertible for
  every base change (`AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange`, smooth purity
  for affine space, an input of the smooth duality section).
* **Affine `X`**: `X ⟶ Spec K` factors as a closed immersion into `𝔸ⁿ_K` followed by the
  projection, and base change maps compose
  (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`); `Rp^! Λ` is
  bounded constructible.
* **General `X`**: base change maps descend along the cover of `X` by its affine opens
  (`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {K L : Type u} [Field K] [Field L]
  [Algebra K L] [HasInvertibleExponent Λ (Spec (.of K))]

/-- **Closed exceptional inverse images commute with base change along field extensions.** Let
`P` be a `K`-scheme of finite type with base change `P' = P ×_K L`, and `i : Z ⟶ P` a closed
immersion with base change `i' : Z' ⟶ P'`. For bounded below `M`, the base change map
`g_Z^* Ri^! M ⟶ Ri'^! g^* M` is an isomorphism: by the closed-support criterion
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso`) it suffices
that `Rj_*` of the open complement commutes with the base change at `j^* M`, which is Stacks
0F1C (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_fieldExtension`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion_of_fieldExtension
    {P P' Z Z' : Scheme.{u}} (σ : P ⟶ Spec (.of K)) [LocallyOfFiniteType σ] [QuasiCompact σ]
    {g : P' ⟶ P} (σ' : P' ⟶ Spec (.of L))
    (hP : IsPullback g σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    {i : Z ⟶ P} {i' : Z' ⟶ P'} {gZ : Z' ⟶ Z} [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : IsPullback gZ i' i g)
    (M : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [M.IsGE n] :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app M) := by
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace σ
  have : IsNoetherian P := { __ := LocallyOfFiniteType.isLocallyNoetherian σ }
  let U := openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have sqU := IsPullback.of_hasPullback U.ι g
  have hij : Set.range i.base = (Set.range U.ι.base)ᶜ := by
    simp [U, openComplementOfIsClosedImmersion]
  have hij' : Disjoint (Set.range i'.base) (Set.range (pullback.snd U.ι g).base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have h₁ : i.base (gZ.base x) = g.base (i'.base x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]
    have h₂ : U.ι.base ((pullback.fst U.ι g).base y) =
        g.base ((pullback.snd U.ι g).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sqU.w]
    have hm : i.base (gZ.base x) ∈ Set.range i.base := ⟨_, rfl⟩
    rw [hij, h₁, ← hy, ← h₂] at hm
    exact hm ⟨_, rfl⟩
  obtain ⟨N, hN₀, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of K))
  have : ((L((U.ι)^*[ModuleCat.{u + 1} Λ])).obj M).IsGE n :=
    isGE_leftDerivedUpperStar_obj _ U.ι M n
  exact isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso Λ sq sqU hij hij' M
    (isIso_derivedBaseChangeMap_app_of_fieldExtension Λ σ σ' hP sqU N hN₀.ne' hΛ hu _ n)

omit [Finite Λ] in
/-- The unit `Λ` of the derived category of a scheme is bounded constructible. -/
lemma boundedConstructible_unit (X : Scheme.{u}) :
    boundedConstructible (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  (boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
    (boundedConstructible_singleFunctor_obj _ 0)

/-- **The dualizing complex of an affine scheme commutes with base change along field
extensions.** For an affine `X` of finite type over `K` with base change `X' = X ×_K L`, the
base change map `Lg'^* Rf^! Λ ⟶ Rf'^! Λ` is an isomorphism. Factor `f` as a closed immersion
`c : X ⟶ 𝔸ⁿ_K` followed by the projection `p`: the base change map of `p` is invertible
(smooth purity for affine space, `affineSpaceAdjunction_baseChange`), that of
`c` is invertible at the bounded constructible `Rp^! Λ`
(`isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion_of_fieldExtension`),
and base change maps compose
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_unit_of_isAffine_of_fieldExtension
    {X X' : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    {f' : X' ⟶ Spec (.of L)} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f'] :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)) := by
  obtain ⟨n, c, hc, _⟩ := exists_isClosedImmersion_affineSpace_of_isAffine f
  let P := 𝔸(ULift.{u} (Fin n); Spec (.of K))
  let p : P ⟶ Spec (.of K) := 𝔸(ULift.{u} (Fin n); Spec (.of K)) ↘ Spec (.of K)
  let πs := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have sqp := IsPullback.of_hasPullback p πs
  let c' : X' ⟶ pullback p πs := sqp.lift (g' ≫ c) f' (by rw [Category.assoc, hc, sq.w])
  have hc'₁ : c' ≫ pullback.fst p πs = g' ≫ c := sqp.lift_fst _ _ _
  have hc'₂ : c' ≫ pullback.snd p πs = f' := sqp.lift_snd _ _ _
  have sqc : IsPullback g' c' c (pullback.fst p πs) := by
    refine IsPullback.of_bot ?_ hc'₁.symm sqp
    have hcp : c ≫ p = f := hc
    rw [hc'₂, hcp]
    exact sq
  have : IsClosedImmersion c' := MorphismProperty.of_isPullback sqc inferInstance
  have : QuasiCompact (pullback.snd p πs) := MorphismProperty.of_isPullback sqp inferInstance
  have : SmoothOfRelativeDimension (Nat.card (ULift.{u} (Fin n))) p :=
    AffineSpace.smoothOfRelativeDimension_over _ _
  have : HasInvertibleExponent Λ P := .of_hom p
  have hpb := boundedConstructible_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ p
    (Nat.card (ULift.{u} (Fin n))) (boundedConstructible_unit Λ (Spec (.of K)))
  obtain ⟨m, hm⟩ := hpb.1.1
  have : ((R(p)^![Λ]).obj (𝟙_ _)).IsGE m := hm
  have hcβ := isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isClosedImmersion_of_fieldExtension
    Λ p (pullback.snd p πs) sqp sqc ((R(p)^![Λ]).obj (𝟙_ _)) m
  have hpβ := (affineSpaceAdjunction_baseChange Λ n (Spec (.of K))).2 sqp
  exact (isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff sqc sqp sq hc hc'₂ (𝟙_ _) hcβ).2
    inferInstance

/-- **The exceptional inverse image of the unit commutes with base change along field
extensions.** For `f : X ⟶ Spec K` separated and of finite type, with base change
`f' : X' ⟶ Spec L` along a field extension `L/K`, the base change map
`Lg'^* Rf^! Λ ⟶ Rf'^! Λ` is an isomorphism. The extension may be transcendental and
inseparable. By the affine case
(`isIso_rightDerivedUpperShriekBaseChangeMap_app_unit_of_isAffine_of_fieldExtension`)
on the affine opens of `X`, whose preimages cover `X'`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_unit_of_fieldExtension
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] {f' : X' ⟶ Spec (.of L)} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f'] :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)) := by
  have : IsSeparated f' := MorphismProperty.of_isPullback sq inferInstance
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let v : ∀ V : X.affineOpens, (V : X.Opens).toScheme ⟶ X := fun V ↦ V.1.ι
  let v' : ∀ V : X.affineOpens, (g' ⁻¹ᵁ (V : X.Opens)).toScheme ⟶ X' := fun V ↦
    (g' ⁻¹ᵁ (V : X.Opens)).ι
  let a : ∀ V : X.affineOpens, (g' ⁻¹ᵁ (V : X.Opens)).toScheme ⟶ (V : X.Opens).toScheme :=
    fun V ↦ g' ∣_ (V : X.Opens)
  have sqv : ∀ V : X.affineOpens, IsPullback (a V) (v' V) (v V) g' := fun V ↦
    isPullback_morphismRestrict g' V.1
  have : ∀ V : X.affineOpens, QuasiCompact (v V) := fun V ↦ by
    have : IsAffine (V : X.Opens).toScheme := V.2
    infer_instance
  have : ∀ V : X.affineOpens, QuasiCompact (v' V) := fun V ↦
    MorphismProperty.of_isPullback (sqv V) inferInstance
  have hS : ∀ V : X.affineOpens, IsPullback (a V) (v' V ≫ f') (v V ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := fun V ↦ (sqv V).paste_vert sq
  have : ∀ V : X.affineOpens, HasCompactification (v V ≫ f) := fun V ↦
    (NagataCompactification (v V ≫ f)).hasCompactification
  have : ∀ V : X.affineOpens, HasCompactification (v' V ≫ f') := fun V ↦
    (NagataCompactification (v' V ≫ f')).hasCompactification
  refine isIso_rightDerivedUpperShriekBaseChangeMap_app_of_cover sq v v' a sqv (fun x ↦ ?_) _
    fun V ↦ ?_
  · obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g'.base x)) isOpen_univ
    exact ⟨⟨V, hV⟩, ⟨x, hx⟩, rfl⟩
  · have : IsAffine (V : X.Opens).toScheme := V.2
    have : QuasiCompact (v' V ≫ f') := inferInstance
    exact isIso_rightDerivedUpperShriekBaseChangeMap_app_unit_of_isAffine_of_fieldExtension Λ
      (v V ≫ f) (hS V)

/-- **The dualizing complex commutes with base change along field extensions**: for
`f : X ⟶ Spec K` separated and of finite type, with base change `f' : X_L ⟶ Spec L` along a
field extension `L/K` (possibly transcendental and inseparable), the canonical base change map
`Lg'^* ω_{X/K} ⟶ ω_{X_L/L}` is an isomorphism. -/
theorem isIso_dualizingComplexBaseChangeMap_of_fieldExtension
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] {f' : X' ⟶ Spec (.of L)} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f'] :
    IsIso (dualizingComplexBaseChangeMap Λ sq) :=
  (isIso_dualizingComplexBaseChangeMap_iff Λ sq).2
    (isIso_rightDerivedUpperShriekBaseChangeMap_app_unit_of_fieldExtension Λ f sq)

end AlgebraicGeometry.Etale
