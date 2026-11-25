/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.GenericPointProjection
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationGeneric
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.Derived.AffineDirectImageVanishing
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionOverMap
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionSplit

/-!
# Relative affine vanishing

Let `f : X ⟶ Y` be an affine morphism locally of finite type, where `Y` is separated and locally
of finite type over a field `k`, and let `G` be an étale sheaf of `Λ`-modules on `X`, for a finite
ring `Λ` of exponent invertible in `k`. If `dim X ≤ N`, then the stalk of `R^q f_* G` at a point
`y` with `dim {y}⁻ = r` vanishes for `q + r > N`
(`AlgebraicGeometry.Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom`). This is the stalk
form of Stacks, Lemma 59.95.8 (Tag `0F0X`): `R^q f_*` carries sheaves supported in dimension `≤ N`
to sheaves supported in dimension `≤ N - q`.

## Proof

We may replace `Y` by an affine open neighbourhood `U` of `y`. Choose a morphism `p : U ⟶ 𝔸ʳ_k`
over `k` sending `y` to the generic point `η` of `𝔸ʳ_k`
(`AlgebraicGeometry.Scheme.exists_hom_mvPolynomial_apply_eq_bot`), and let `s` be the geometric
point of `𝔸ʳ_k` under `ȳ`. The strict localization of `𝔸ʳ_k` at `s` is the spectrum of a
separably closed field `K` (`AlgebraicGeometry.Scheme.exists_isSepClosed_strictLocalization_iso`),
and `T = X_U ×_{𝔸ʳ} Spec K` is a `K`-scheme of finite type of dimension at most that of the
generic fibre of `X_U ⟶ 𝔸ʳ`, hence at most `N - r`, affine over `Y`. So `R^q (T ⟶ Y)_*` vanishes
for `q > N - r` (`AlgebraicGeometry.Etale.hasUniformDirectImageVanishingLE_of_isAffineHom`).
Writing `T` as the limit of the `X_U ×_{𝔸ʳ} V` over the affine étale neighbourhoods `V` of `s`
(`AlgebraicGeometry.Etale.higherDirectImage_limit`), every element of the stalk of `R^q f_* G` at
`ȳ` dies in the stalk of some `R^q (X_U ×_{𝔸ʳ} V ⟶ Y)_*`. But `X_U ×_{𝔸ʳ} V` is the base change
of `X` along the étale map `U ×_{𝔸ʳ} V ⟶ Y` through which `ȳ` lifts, so the transition map is
injective on the stalk at `ȳ`
(`AlgebraicGeometry.Etale.injective_sheafFiber_map_higherDirectImageTransition`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- Base change along `pullback.snd w p` followed by an open immersion, pasted with a pullback
square `fU, ιX, ιU, f`: the projection `W ×_A XU ⟶ X` is the base change of `f` along
`W ×_A U ⟶ U ⟶ Y`. -/
lemma CategoryTheory.IsPullback.pullback_map_of_isPullback {C : Type*} [Category* C]
    [HasPullbacks C] {XU U X Y W A : C} {fU : XU ⟶ U} {ιX : XU ⟶ X} {ιU : U ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback fU ιX ιU f) (p : U ⟶ A) (w : W ⟶ A) :
    IsPullback (pullback.snd w (fU ≫ p) ≫ ιX)
      (pullback.map w (fU ≫ p) w p (𝟙 _) fU (𝟙 _) (by simp) (by simp)) f
      (pullback.snd w p ≫ ιU) := by
  have sq : IsPullback (pullback.map w (fU ≫ p) w p (𝟙 _) fU (𝟙 _) (by simp) (by simp))
      (pullback.snd w (fU ≫ p)) (pullback.snd w p) fU :=
    IsPullback.of_right (by simpa using IsPullback.of_hasPullback w (fU ≫ p)) (by simp)
      (IsPullback.of_hasPullback w p)
  exact (sq.paste_vert h).flip

/-- If `d + r ≤ N` in `WithBot ℕ∞`, then `d ≤ N - r`. -/
lemma WithBot.ENat.le_natCast_sub_of_add_le {d : WithBot ℕ∞} {r N : ℕ}
    (h : d + r ≤ N) : d ≤ ((N - r : ℕ) : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      norm_cast at h
    | coe d =>
      have h' : d + r ≤ N := by exact_mod_cast h
      exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : d ≤ N - r))

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- A higher direct image from the empty scheme vanishes. -/
lemma Etale.isZero_higherDirectImage_of_isEmpty {X Y : Scheme.{u}} [IsEmpty Y] (h : Y ⟶ X)
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsZero (Etale.higherDirectImage Λ h q F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map_isZero ((R+((h)_*[ModuleCat.{u + 1} Λ])).map_isZero
    ((DerivedCategory.Plus.singleFunctor _ 0).map_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty F)))

variable [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

open Scheme in
/-- The case of `Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom` for a point `y` of an
affine open `U ⊆ Y`, with the dimension of the closure of `y` computed in `U`. -/
theorem Etale.isZero_sheafFiber_higherDirectImage_of_isAffineOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (N : ℕ)
    (hX : topologicalKrullDim X ≤ N) (U : Y.Opens) (hU : IsAffineOpen U) (y : U) (r : ℕ)
    (hr : topologicalKrullDim (closure ({y} : Set U)) = r) (q : ℤ) (hq : (N : ℤ) < q + r) :
    IsZero ((Y.uliftPointSmallEtale y.1).sheafFiber.obj (Etale.higherDirectImage Λ f q G)) := by
  have : IsAffine U := hU
  have : HasInvertibleExponent Λ Y := HasInvertibleExponent.of_hom aY
  obtain ⟨p, hp, hpy⟩ := exists_hom_mvPolynomial_apply_eq_bot (U.ι ≫ aY) y r hr
  have : LocallyOfFiniteType (p ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)) := by
    rw [hp]
    infer_instance
  have : LocallyOfFiniteType p :=
    locallyOfFiniteType_of_comp p (Spec.map (CommRingCat.ofHom MvPolynomial.C))
  let fU : (f ⁻¹ᵁ U : Scheme.{u}) ⟶ U := f ∣_ U
  let f₀ : (f ⁻¹ᵁ U : Scheme.{u}) ⟶ Spec (.of (MvPolynomial (Fin r) k)) := fU ≫ p
  -- the geometric point and its lift to `U`
  let yb := Y.algClosurePoint y.1
  have hyb : Set.range yb.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [algClosurePoint_base]
    exact ⟨y, rfl⟩
  let yU := IsOpenImmersion.lift U.ι yb hyb
  have hyU : yU ≫ U.ι = yb := IsOpenImmersion.lift_fac _ _ _
  let sA := yU ≫ p
  have hyU' (z : Spec (.of (AlgebraicClosure (Y.residueField y.1)))) : yU z = y := by
    refine Subtype.ext ?_
    have := congr($hyU z)
    rw [Scheme.Hom.comp_apply] at this
    rw [← Scheme.Opens.ι_apply, this]
    exact algClosurePoint_base _ _ _
  have hsA : (sA.base (IsLocalRing.closedPoint _)).asIdeal = ⊥ := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hyU']
    exact hpy
  -- the system of the `XU ×_{𝔸ʳ} V` over the affine pointed étale neighbourhoods of `sA`
  have : LocallySmall.{u} (AffinePointedEtaleNeighborhood sA) := ⟨fun _ _ ↦ small_self _⟩
  let I := InitiallySmall.CofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood sA)
  let ιI := InitiallySmall.fromCofilteredInitialModel.{u} (AffinePointedEtaleNeighborhood sA)
  let D : I ⥤ Over X := ιI ⋙ affineNeighborhoodDiagramOver sA ⋙ Over.pullback f₀ ⋙
    Over.map (f ⁻¹ᵁ U).ι
  let c : Cone D := ((Over.map (f ⁻¹ᵁ U).ι).mapCone
    ((Over.pullback f₀).mapCone (strictLocalizationConeOver sA))).whisker ιI
  have hc : IsLimit ((Over.forget X).mapCone c) :=
    (Functor.Initial.isLimitWhiskerEquiv ιI _).symm (isLimitStrictLocalizationConePullback sA f₀)
  have : IsAffine (f ⁻¹ᵁ U) := hU.preimage f
  have : IsAffine c.pt.left :=
    inferInstanceAs (IsAffine (pullback (strictLocalizationToBase sA) f₀))
  have : IsAffineHom (c.pt.hom ≫ f) := IsAffineHom.of_comp _ aY
  -- the limit `c.pt` is a scheme of finite type over a separably closed field
  have hlim : IsZero ((Y.uliftPointSmallEtale y.1).sheafFiber.obj (Etale.higherDirectImage Λ
      (c.pt.hom ≫ f) q ((c.pt.hom)^*[ModuleCat.{u + 1} Λ].obj G))) := by
    obtain ⟨K, _, _, ⟨eK⟩⟩ := exists_isSepClosed_strictLocalization_iso (s := sA) hsA
    let s' := eK.inv ≫ strictLocalizationToBase sA
    have hs' : (s'.base (IsLocalRing.closedPoint K)).asIdeal = ⊥ := by
      have : Subsingleton (strictLocalization sA) :=
        eK.hom.homeomorph.injective.subsingleton
      have hpt : eK.inv.base (IsLocalRing.closedPoint K) =
          (Spec.map (strictHenselizationEval sA)).base (IsLocalRing.closedPoint _) :=
        Subsingleton.elim _ _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hpt,
        ← Function.comp_apply (f := (strictLocalizationToBase sA).base), ← TopCat.coe_comp,
        ← Scheme.Hom.comp_base, spec_map_strictHenselizationEval_comp_strictLocalizationToBase]
      exact hsA
    have hdim : topologicalKrullDim c.pt.left + r ≤ N := by
      have e₁ : topologicalKrullDim c.pt.left = topologicalKrullDim (pullback f₀ s' : Scheme.{u}) :=
        IsHomeomorph.topologicalKrullDim_eq _ ((pullbackSymmetry _ _ ≪≫
          asIso (pullback.map f₀ (strictLocalizationToBase sA) f₀ s' (𝟙 _) eK.hom (𝟙 _)
            (by simp) (by simp [s']))).hom.homeomorph.isHomeomorph)
      rw [e₁]
      calc topologicalKrullDim (pullback f₀ s' : Scheme.{u}) + r
          ≤ topologicalKrullDim (f₀ ⁻¹' {s'.base (IsLocalRing.closedPoint K)}) + r :=
            add_le_add_left (topologicalKrullDim_pullback_le_preimage f₀ s') _
        _ ≤ topologicalKrullDim (f ⁻¹ᵁ U : Scheme.{u}) :=
            Scheme.Hom.topologicalKrullDim_preimage_add_le_of_asIdeal_eq_bot r f₀ _ hs'
        _ ≤ topologicalKrullDim X := (f ⁻¹ᵁ U).ι.isOpenEmbedding.isInducing.topologicalKrullDim_le
        _ ≤ N := hX
    refine Functor.map_isZero _ ?_
    rcases le_or_gt q 0 with hq0 | hq0
    · have : IsEmpty c.pt.left := by
        rw [← not_nonempty_iff]
        intro hne
        have h₀ := add_le_add_left (topologicalKrullDim_nonneg (X := c.pt.left)) (r : WithBot ℕ∞)
        rw [zero_add] at h₀
        have : r ≤ N := by exact_mod_cast h₀.trans hdim
        omega
      exact Etale.isZero_higherDirectImage_of_isEmpty Λ _ q _
    · exact Etale.hasUniformDirectImageVanishingLE_of_isAffineHom Λ (c.pt.hom ≫ f)
        (pullback.fst (strictLocalizationToBase sA) f₀ ≫ eK.hom) (N - r)
        (WithBot.ENat.le_natCast_sub_of_add_le hdim) _ q (by omega)
  have hDaff (i : I) : IsAffine (D.obj i).left := by
    have : IsAffine ((affineNeighborhoodDiagramOver sA).obj (ιI.obj i)).left := (ιI.obj i).2
    dsimp [D]
    infer_instance
  have (i : I) : IsAffineHom ((D.obj i).hom ≫ f) :=
    IsAffineHom.of_comp _ aY
  have : ∀ {i j : I} (φ : i ⟶ j), IsAffineHom (D.map φ).left := fun _ ↦ inferInstance
  have lim := Etale.higherDirectImage_limit Λ f G D c hc q y.1
  rw [ModuleCat.isZero_iff_subsingleton]
  suffices H : ∀ m : ((Y.uliftPointSmallEtale y.1).sheafFiber.obj
      (Etale.higherDirectImage Λ f q G) : ModuleCat.{u + 1} Λ), m = 0 from
    ⟨fun a b ↦ (H a).trans (H b).symm⟩
  intro m
  obtain ⟨j₀⟩ : Nonempty I := IsCofiltered.nonempty
  obtain ⟨j, φ, hφ⟩ := lim.2 j₀ (((Y.uliftPointSmallEtale y.1).sheafFiber.map
    (Etale.higherDirectImageTransition Λ (D.obj j₀).hom f _ rfl q G)).hom m)
    ((ModuleCat.isZero_iff_subsingleton.1 hlim).elim _ _)
  have hcomp := Etale.higherDirectImageTransition_comp_higherDirectImageOverMap Λ f G q
    (D.map φ)
  have h0 : ((Y.uliftPointSmallEtale y.1).sheafFiber.map
      (Etale.higherDirectImageTransition Λ (D.obj j).hom f _ rfl q G)).hom m = 0 := by
    rw [← hcomp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact hφ
  let W := (affineNeighborhoodDiagramOver sA).obj (ιI.obj j)
  have : Etale W.hom := (ιI.obj j).obj.1.prop
  let e : pullback W.hom p ⟶ Y := pullback.snd W.hom p ≫ U.ι
  have hsq := (isPullback_morphismRestrict f U).pullback_map_of_isPullback p W.hom
  let wb : Spec (.of (AlgebraicClosure (Y.residueField y.1))) ⟶ W.left := (ιI.obj j).obj.2.left
  have hw : wb ≫ W.hom = sA := Over.w (ιI.obj j).obj.2
  let t := pullback.lift wb yU hw
  have hte : t ≫ e = Y.algClosurePoint y.1 := by simp [t, e, hyU, yb]
  have hinj := Etale.injective_sheafFiber_map_higherDirectImageTransition Λ f e
    (pullback.snd W.hom f₀ ≫ (f ⁻¹ᵁ U).ι) _ hsq G t q
  rw [hte] at hinj
  exact hinj (h0.trans (map_zero _).symm)

/-- **Relative affine vanishing on stalks.** Let `f : X ⟶ Y` be an affine morphism locally of
finite type, where `Y` is separated and locally of finite type over a field `k`, let `Λ` be a
finite ring of exponent invertible in `k` and `G` an étale sheaf of `Λ`-modules on `X`. If
`dim X ≤ N` and `y ∈ Y` has `dim {y}⁻ = r`, then the stalk of `R^q f_* G` at `y` vanishes for
`q + r > N`.

This is the stalk form of Stacks, Lemma 59.95.8 (Tag `0F0X`): `R^q f_*` carries sheaves supported
in dimension `≤ N` to sheaves supported in dimension `≤ N - q`. It is the input to the cosupport
side of Artin–Gabber (blueprint `lem-per-artin-gabber-affine-curve`, Step 3). -/
@[stacks 0F0X]
theorem Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [IsSeparated aY]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (N : ℕ)
    (hX : topologicalKrullDim X ≤ N) (y : Y) (r : ℕ)
    (hr : topologicalKrullDim (closure ({y} : Set Y)) = r) (q : ℤ) (hq : (N : ℤ) < q + r) :
    IsZero ((Y.uliftPointSmallEtale y).sheafFiber.obj (Etale.higherDirectImage Λ f q G)) := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  refine Etale.isZero_sheafFiber_higherDirectImage_of_isAffineOpen Λ f aY G N hX U hU ⟨y, hyU⟩ r
    (le_antisymm ?_ ?_) q hq
  · have h := U.ι.isOpenEmbedding.topologicalKrullDim_closure_singleton_inter_range ⟨y, hyU⟩
    rw [Scheme.Opens.ι_apply] at h
    rw [← h, ← hr]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le
  · rw [← hr]
    exact Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le aY U.ι ⟨y, hyU⟩

end AlgebraicGeometry
