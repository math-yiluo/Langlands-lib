/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Stability of `Dctf`: the exceptional inverse image

For torsion coefficients `Λ` with invertible exponent and schemes of finite type over a field,
this file proves that the exceptional inverse image `Rf^!` preserves `Dctf`, with the shifts
of `theorem-f-shriek-finite-coefficients`, and constructs the descended functors `Rf_*`, `Rf_!`
and `Rf^!`.

This file is part of `WeilConjectures.SixFunctors.Etale.Derived.Stability`, whose module
documentation records the implementation notes.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]

/-! #### The exceptional inverse image -/

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for the exceptional inverse
image.

Clause (ii): for a closed immersion `i : Z ⟶ T` into a finite-type `k`-scheme of dimension
`≤ d`, and a finite `Λ` whose exponent is invertible on `T`, the exceptional inverse image widens
the upper end of the interval by `2d + 1`, that is, `D_c^[a, b] ↦ D_c^[a, b + 2d + 1]`. The bound
is in terms of the dimension of the target, and comes from the localization triangle for the
open complement, the vanishing of étale cohomology above twice the dimension giving the `2d`
and the triangle the extra `+1`. No bound in terms of the codimension alone holds: for
`Z = V(y) ⊂ T = Spec k[x, y]/(xy)`, `H²(Ri^!Λ)` is nonzero at the origin, coming from the
punctured `y`-axis, although `Z` has codimension `0`. For `Z` regular of pure codimension `c` in
a regular `T`, the sharp `Ri^!Λ_T ≅ Λ_Z(-c)[-2c]` is `lemma-class-of-point--1`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion
    {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [HasInvertibleExponent Λ T] (i : Z ⟶ T) [IsClosedImmersion i] [HasCompactification i]
    (d : ℕ) (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + 2 * d + 1)
      ((R(i)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace aT
  have : IsNoetherian T := { __ := LocallyOfFiniteType.isLocallyNoetherian aT }
  let V := openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace V := V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hij : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    simp [V, openComplementOfIsClosedImmersion]
  obtain ⟨⟨hbc, hc⟩, ht⟩ := hK
  -- the restriction of `K` to the open complement
  have hbc' := boundedConstructible_leftDerivedUpperStar _ V.ι hbc
  have ht' := torAmplitudeIn_leftDerivedUpperStar _ V.ι a b ht
  obtain ⟨N, hN0, hNΛ, hNT⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := T)
  have : NeZero N := ⟨hN0.ne'⟩
  have hN := nsmul_id_eq_zero_of_natCast_eq_zero hNΛ ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj K)
  have hdV : topologicalKrullDim V ≤ (d : WithBot ℕ∞) :=
    (V.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd
  have hMt := torAmplitudeIn_rightDerivedLowerStar _ (V.ι ≫ aT) aT V.ι rfl d hdV a b N hN hNT
    hbc' ht'
  have hM : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) T a (b + 2 * d)
      ((R((V.ι)_*[ModuleCat.{u + 1} Λ])).obj ((L((V.ι)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
    ⟨⟨boundedConstructible_rightDerivedLowerStar_of_finite Λ (V.ι ≫ aT) aT V.ι rfl hbc',
      _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hMt⟩, hMt⟩
  have := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion_of_lowerStar
    Λ i V.ι hij (by omega : b ≤ b + 2 * d) ⟨⟨hbc, hc⟩, ht⟩ hM
    (fun L ↦ hasProjectionFormula_of_finite Λ i _ L)
  rwa [show b + 2 * (d : ℤ) + 1 = b + 2 * d + 1 by ring] at this

omit [Finite Λ] in
/-- A locally constant sheaf of free rank-one `Λ`-modules, for a finite `Λ`, is constructible and
flat. -/
lemma isConstructibleSheaf_and_flat_of_sheafFiber_iso {X : Scheme.{u}}
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) :
    IsConstructibleSheaf L ∧ ObjectProperty.flat L := by
  have : IsFiniteSheaf L := ⟨fun Ω _ _ s ↦
    (ConcreteCategory.isFinitelyGenerated_iff_of_iso (hL Ω s).some).2
      ((ModuleCat.isFinitelyGenerated_iff _).2 inferInstance)⟩
  have : IsFiniteLocallyConstantSheaf L := {}
  refine ⟨IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›,
    (flat_iff_forall_flat_sheafFiber_obj L).2 fun {Ω} _ _ s ↦ ?_⟩
  exact ObjectProperty.prop_of_iso _ ((GrothendieckTopology.Point.uliftSheafFiberIso _ _).app L ≪≫
    (hL Ω s).some).symm (ObjectProperty.prop_unit (ObjectProperty.flat (A := ModuleCat.{u + 1} Λ)))

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for the exceptional inverse
image.

Clause (iii): for `f` smooth of pure relative dimension `d` and a finite `Λ` whose exponent is
invertible on `Y`, the exceptional inverse image shifts both intervals by `-2d`,
`D_c^[a, b] ↦ D_c^[a - 2d, b - 2d]`, by purity `Rf^! ≅ Lf^*(-)(d)[2d]`. Without choosing an
orientation, `Rf^! K ≅ Lf^* K ⊗ᴸ L[2d]` for a locally constant sheaf `L` of free rank-one
`Λ`-modules (`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`,
`proposition-exceptional-inverse-image-smooth-morphism`), and tensoring with the flat constructible
`L` changes neither the constructible interval nor the Tor amplitude. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * d) (b - 2 * d)
      ((R(f)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : HasInvertibleExponent Λ X := .of_hom f
  obtain ⟨L, _, hLs, ⟨eω⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ f d
  obtain ⟨et⟩ := nonempty_iso_derivedTensor_leftDerivedUpperStar_obj_dualizingComplex Λ f d K
  obtain ⟨_, hLf⟩ := isConstructibleSheaf_and_flat_of_sheafFiber_iso Λ L hLs
  obtain ⟨⟨hbc, -⟩, hta⟩ := hK
  have hL₀ := torAmplitudeIn_singleFunctor_zero_of_flat _ L hLf
  have hMbc := boundedConstructible_tensor Λ X (boundedConstructible_leftDerivedUpperStar _ f hbc)
    (DerivedCategory.boundedConstructible_singleFunctor_obj L 0) ⟨0, 0, hL₀⟩
  exact constructibleTorAmplitudeIn_of_iso_tensor_shift _ et.symm eω
    (torAmplitudeIn_leftDerivedUpperStar _ f a b hta) hL₀
    ((boundedConstructible _ X).le_shift _ _ hMbc)

omit [Finite Λ] in
/-- Membership in `D_c^[a, b]` with Tor amplitude in `[a, b]` is local for a finite open cover
of a scheme with noetherian underlying space. -/
theorem constructibleTorAmplitudeIn_of_openCover {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ x, ∃ i, x ∈ U i)
    (R : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) {a b : ℤ}
    (h : ∀ i, constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) (U i)
      a b (D(((U i).ι)^*[ModuleCat.{u + 1} Λ]).obj R)) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X a b R :=
  ⟨⟨boundedConstructible_of_openCover Λ U hU R fun i ↦ (h i).1.1,
    homologyConcentratedIn_of_openCover _ U hU R fun i ↦ (h i).1.2⟩,
    torAmplitudeIn_of_openCover _ U hU R fun i ↦ (h i).2⟩

/-- The chart step of clause (iv): for an immersion `c : U ⟶ 𝔸ⁿ_V` over an affine open
`v : V ⟶ Y`, `R(c ≫ π ≫ v)^!` sends `D_c^[a, b]` to `D_c^[a - 2n, b + 2d + 1]` when
`dim Y ≤ d`. -/
theorem constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart {U V Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (v : V ⟶ Y) [IsOpenImmersion v] [IsAffine V] {n : ℕ}
    (c : U ⟶ 𝔸(ULift.{u} (Fin n); V)) [IsImmersion c] [IsAffine U]
    [HasCompactification (c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)]
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K) :
    constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) U (a - 2 * n) (b + 2 * d + 1)
      ((R(c ≫ 𝔸(ULift.{u} (Fin n); V) ↘ V ≫ v)^![Λ]).obj K) := by
  have : IsNoetherianRing Λ := inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let π := 𝔸(ULift.{u} (Fin n); V) ↘ V
  let W := c.coborderRange
  let ι := c.liftCoborder
  have : TopologicalSpace.NoetherianSpace V := v.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : IsNoetherian V := {}
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); V) := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian 𝔸(ULift.{u} (Fin n); V) := {}
  have : TopologicalSpace.NoetherianSpace W := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact W.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification v := (Compactification.ofIsOpenImmersion v).hasCompactification
  have : HasCompactification W.ι := (Compactification.ofIsOpenImmersion W.ι).hasCompactification
  have : HasCompactification ι := (Compactification.ofIsProper ι).hasCompactification
  have : HasInvertibleExponent Λ V := HasInvertibleExponent.of_hom v
  have : HasInvertibleExponent Λ W := HasInvertibleExponent.of_hom (W.ι ≫ π ≫ v)
  have : SmoothOfRelativeDimension n π := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V
  have hdW : topologicalKrullDim W ≤ ((d + n : ℕ) : WithBot ℕ∞) := by
    refine (W.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans ?_
    rw [topologicalKrullDim_affineSpace_of_isAffine]
    have hV := (v.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hd
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_fin, Nat.cast_add]
    exact add_le_add hV le_rfl
  have h₁ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion Λ v a b hK
  have h₂ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_smoothOfRelativeDimension Λ π
    n a b h₁
  have h₃ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isOpenImmersion Λ W.ι _ _ h₂
  have h₄ := constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_isClosedImmersion Λ
    (W.ι ≫ π ≫ v ≫ aY) ι (d + n) hdW _ _ h₃
  have hc : c ≫ π ≫ v = ι ≫ W.ι ≫ π ≫ v := by
    rw [← Category.assoc ι, c.liftCoborder_ι]
  have heq : ∀ {g₁ g₂ : U ⟶ Y} [HasCompactification g₁] [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![Λ] ≅ R(g₂)^![Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₀⟩ := heq hc
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ ι (W.ι ≫ π ≫ v)
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ W.ι (π ≫ v)
  obtain ⟨e₃⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ π v
  refine constructibleTorAmplitudeIn_of_iso _ ((e₀ ≪≫ e₁ ≪≫ Functor.isoWhiskerRight e₂ _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight e₃ _) _).app K).symm ?_
  have hb : b - 2 * (n : ℤ) + 2 * ((d + n : ℕ) : ℤ) + 1 = b + 2 * d + 1 := by push_cast; ring
  rw [hb] at h₄
  exact h₄

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for the exceptional inverse
image.

Clause (iv), with its constants: let `f : X ⟶ Y` be a separated finite-type morphism admitting
a compactification, with `Y` of finite type over `k`, and let `Λ` be finite with exponent
invertible on `Y`. There is a `D`, depending only on `f`, such that whenever `dim Y ≤ d`, `Rf^!`
sends `D_c^[a, b]` into `D_c^[a - 2D, b + 2d + 1]`. Here `D` is the maximal embedding dimension
of the affine charts `U ↪ 𝔸^{d_U}_V` of `f`.

The proof has three steps.
1. Localise: the amplitudes are Zariski-local on `X` and `Rj^! = j^*` for an open immersion
   `j`, so it suffices to treat finitely many affine charts `U ↪ 𝔸^{n}_V ⟶ V` with `n ≤ D`;
   finitely many suffice because `Y` is quasi-compact.
2. Compose: the smooth clause (iii) for `𝔸^n_V ⟶ V` sends `[a, b]` to `[a - 2n, b - 2n]`, and
   the closed-immersion clause (ii) into `𝔸^n_V` then sends it to
   `[a - 2n, b - 2n + 2(d + n) + 1]`.
3. Count dimensions: `dim 𝔸^n_V = dim V + n ≤ d + n`, so the upper end is `b + 2d + 1`. -/
theorem exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ D : ℕ, ∀ (d : ℕ), topologicalKrullDim Y ≤ (d : WithBot ℕ∞) →
      ∀ (a b : ℤ) (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
          constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - 2 * D) (b + 2 * d + 1)
            ((R(f)^![Λ]).obj K) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  -- affine charts `U ⊆ f⁻¹ V`
  have hchart (x : X) : ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ (U : X.Opens) ∧ (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens) := by
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
      (show f.base x ∈ (⊤ : Y.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ V from hxV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV⟩
  choose U V hxU hUV using hchart
  -- immersions of the charts into affine spaces over the `V`
  have hemb (x : X) : ∃ (n : ℕ) (c : ((U x : X.Opens) : Scheme.{u}) ⟶
      𝔸(ULift.{u} (Fin n); (V x : Y.Opens))), IsImmersion c ∧
      c ≫ 𝔸(ULift.{u} (Fin n); (V x : Y.Opens)) ↘ _ ≫ (V x : Y.Opens).ι =
        (U x : X.Opens).ι ≫ f := by
    have hr : Set.range ((U x : X.Opens).ι ≫ f).base ⊆ Set.range (V x : Y.Opens).ι.base := by
      rintro - ⟨y, rfl⟩
      simpa using hUV x y.2
    let g := IsOpenImmersion.lift (V x : Y.Opens).ι ((U x : X.Opens).ι ≫ f) hr
    have hg : g ≫ (V x : Y.Opens).ι = (U x : X.Opens).ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have : LocallyOfFiniteType (g ≫ (V x : Y.Opens).ι) := by rw [hg]; infer_instance
    have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (V x : Y.Opens).ι
    have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
    obtain ⟨n, c, hc, himm⟩ := exists_immersion_affineSpace_of_quasiAffine g
    exact ⟨n, c, himm, by rw [← Category.assoc, hc, hg]⟩
  choose n c hc hcf using hemb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((U x : X.Opens) : Set X))
    (fun x ↦ (U x : X.Opens).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨t.sup n, fun d hd a b K hK ↦ ?_⟩
  let Uc : Fin t.card → X.Opens := fun i ↦ (U (t.equivFin.symm i)).1
  refine constructibleTorAmplitudeIn_of_openCover Λ Uc (fun x ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa [Uc] using hx⟩
  set x := (t.equivFin.symm i).1
  have hxt : x ∈ t := (t.equivFin.symm i).2
  have : IsAffine ((U x : X.Opens) : Scheme.{u}) := (U x).2
  have : IsAffine ((V x : Y.Opens) : Scheme.{u}) := (V x).2
  have := hc x
  have : TopologicalSpace.NoetherianSpace (U x : X.Opens) :=
    (U x : X.Opens).ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (U x : X.Opens).ι :=
    ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : HasCompactification (U x : X.Opens).ι :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have hK' := constructibleTorAmplitudeIn_rightDerivedUpperShriek_chart Λ aY (V x : Y.Opens).ι
    (c x) d hd a b hK
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (U x : X.Opens).ι f
  have heq : ∀ {g₁ g₂ : ((U x : X.Opens) : Scheme.{u}) ⟶ Y} [HasCompactification g₁]
      [HasCompactification g₂], g₁ = g₂ →
      Nonempty (R(g₁)^![Λ] ≅ R(g₂)^![Λ]) := by
    intro g₁ g₂ _ _ h
    subst h
    exact ⟨Iso.refl _⟩
  obtain ⟨e₂⟩ := heq (hcf x)
  have hmono := hK'
  refine constructibleTorAmplitudeIn_of_iso _ (((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ
    (U x : X.Opens).ι).app _).symm ≪≫ (e₁.app K).symm ≪≫ (e₂.app K).symm).symm ?_
  obtain ⟨⟨hbc, hc₁, hc₂⟩, hta⟩ := hK'
  have hn : n x ≤ t.sup n := Finset.le_sup hxt
  exact ⟨⟨hbc, _root_.DerivedCategory.TStructure.t.isGE_of_ge _ _ (a - 2 * n x) (by omega),
    hc₂⟩, hta.mono (by omega) le_rfl⟩

/-- Blueprint `theorem-f-shriek-finite-coefficients`: Preservation for the exceptional inverse
image.

Clause (iv), dimension-free form with the shift forgotten: every separated finite-type `f`
admitting a compactification, over a finite-type `k`-scheme `Y`, preserves the constructible
intervals up to a single shift `c`, depending only on `f`, widening every interval `[a, b]` to
`[a - c, b + c]`. Since `Y` is finite dimensional, say `dim Y ≤ d`, this is the preceding
theorem with `c = 2D + 2d + 1`. -/
theorem exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] :
    ∃ c : ℤ, ∀ (a b : ℤ)
      (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) Y a b K →
        constructibleTorAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - c) (b + c)
          ((R(f)^![Λ]).obj K) := by
  obtain ⟨D, hD⟩ :=
    exists_constructibleTorAmplitudeIn_rightDerivedUpperShriek_of_topologicalKrullDim_le Λ aY f
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aY
  refine ⟨2 * D + 2 * d + 1, fun a b K hK ↦ ?_⟩
  obtain ⟨⟨hbc, hconc⟩, hta⟩ := hD d hd a b K hK
  exact ⟨⟨hbc, hconc.mono (by omega) (by omega)⟩, hta.mono (by omega) (by omega)⟩

/-- Blueprint `proposition-six-operations-dctf`: Stability of the constructible finite-Tor
subcategories.

Clause (v): `Rf^! : Dctf(Y, Λ) ⥤ Dctf(X, Λ)` is defined for every separated finite-type `f`
admitting a compactification, over a finite-type `k`-scheme `Y`, for a finite `Λ` whose exponent
is invertible on `Y`. This is
`AlgebraicGeometry.Etale.exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek`
with the shift forgotten. -/
theorem constructibleFiniteTor_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K) := by
  obtain ⟨c, hc⟩ := exists_shift_constructibleTorAmplitudeIn_rightDerivedUpperShriek Λ aY f
  obtain ⟨a, b, hab⟩ :=
    (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor K).2 hK
  exact (exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).1
    ⟨a - c, b + c, hc a b K hab⟩

/-- The dualizing complex `ω_Y = Ra_Y^! Λ_S` lies in `Dctf(Y, Λ)` when the unit `Λ_S` does,
for `S` of finite type over a field `k` and a finite `Λ` whose exponent is invertible on `S`, by
the stability of `Dctf` under `Ra_Y^!`. In the blueprint's setting (`S` the spectrum of a
field) the unit is in `Dctf`. -/
theorem constructibleFiniteTor_dualizingComplex {Y S : Scheme.{u}} (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [HasInvertibleExponent Λ S] (aY : Y ⟶ S)
    [HasCompactification aY] [QuasiCompact aY]
    (hΛ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) S (𝟙_ _)) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (dualizingComplex _ aY) :=
  constructibleFiniteTor_rightDerivedUpperShriek Λ aS aY hΛ

/-! #### The descended functors -/

section Functors

variable {X Y : Scheme.{u}}

/-- Blueprint `proposition-six-operations-dctf`, clause (iii): the restriction
`Rf_* : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` of the derived direct image to the small categories, for a
separated morphism of finite-type `k`-schemes and a finite `Λ` whose exponent is invertible on
`Y`. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerStar (aX : X ⟶ Spec (.of k))
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) [IsSeparated f]
    [HasInvertibleExponent Λ Y] :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙ R((f)_*[ModuleCat.{u + 1} Λ]))
    fun K ↦ constructibleFiniteTor_rightDerivedLowerStar Λ aX aY f hf K.property

/-- Blueprint `proposition-six-operations-dctf`, clause (iv): the restriction
`Rf_! : Dctf(X, Λ) ⥤ Dctf(Y, Λ)` of the compactly supported direct image to the small
categories, for a separated finite-type `f` over a finite-type `k`-scheme `Y` and a finite `Λ`
whose exponent is invertible on `Y`. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedLowerShriek (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙ R(f)_![ModuleCat.{u + 1} Λ])
    fun K ↦ constructibleFiniteTor_rightDerivedLowerShriek Λ aY f K.property

/-- Blueprint `proposition-six-operations-dctf`, clause (v): the restriction
`Rf^! : Dctf(Y, Λ) ⥤ Dctf(X, Λ)` of the exceptional inverse image to the small categories, for
a separated finite-type `f` over a finite-type `k`-scheme `Y` and a finite `Λ` whose exponent
is invertible on `Y`. -/
noncomputable def DerivedCategoryFiniteTor.rightDerivedUpperShriek (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [HasInvertibleExponent Λ Y] (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] :
    DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y ⥤
      DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) Y ⋙ R(f)^![Λ])
    fun K ↦ constructibleFiniteTor_rightDerivedUpperShriek Λ aY f K.property

end Functors

end Torsion

end Etale

end AlgebraicGeometry
