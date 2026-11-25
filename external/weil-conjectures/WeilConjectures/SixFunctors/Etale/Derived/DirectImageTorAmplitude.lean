/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.IsoOfSyzygies
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# The direct image of a complex of finite Tor amplitude

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and
`Λ` a finite ring. This file proves that `Rf_*` carries complexes of Tor amplitude in `[a, b]` to
complexes of Tor amplitude in `[a, b + 2d]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_finite`, blueprint
`proposition-six-operations-dctf--2` and `sk-thm-sf-direct-image-tor-amplitude`), following the
blueprint:

* the projection map `Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y)` is an isomorphism for every bounded
  above `K` and every finitely generated `Λ`-module `M`
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`,
  blueprint `proposition-open-direct-image-preserves-finite--1`). It is an isomorphism for `M = Λ`,
  hence for `M` free of finite rank, and the way-out argument
  `DerivedCategory.isIso_app_of_exists_distTriang` along the first syzygies of `M` concludes,
  using only that `Rf_*` raises degrees by at most `2d`
  (`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj`);
* for `κ = Λ ⧸ J`, `J` the Jacobson radical, `Rf_* K ⊗ᴸ κ_Y ≅ Rf_*(K ⊗ᴸ κ_X)` has homology in
  `[a, b + 2d]`, `K ⊗ᴸ κ_X` having homology in `[a, b]`;
* the residue test
  `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn`
  (blueprint `theorem-f-shriek-finite-coefficients--1`) turns this into Tor amplitude in
  `[a, b + 2d]`.

Neither separatedness of `f`, nor constructibility of `K`, nor the invertibility of the exponent
of `Λ` on `Y` is needed.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]
  [Etale.UpperStarPreservesFlat A]

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- The derived tensor product of an object vanishing above `b` and one vanishing above `d`
vanishes above `b + d`, stated with `AlgebraicGeometry.Etale.derivedTensor`. -/
lemma isLE_derivedTensor_obj (X : Scheme.{u})
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (b d : ℤ) [K.IsLE b]
    [M.IsLE d] : (((-⊗ᴸ-(X)[A]).obj K).obj M).IsLE (b + d) :=
  _root_.DerivedCategory.isLE_tensor K M b d

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- Tor amplitude in `[a, b]` of an object `K` of `D(X_ét)`, written with
`AlgebraicGeometry.Etale.derivedTensor`. -/
lemma torAmplitudeIn_iff_forall_derivedTensor (X : Scheme.{u}) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    torAmplitudeIn A X a b K ↔ ∀ F : Sheaf X.smallEtaleTopology A,
      _root_.DerivedCategory.homologyConcentratedIn a b
        (((-⊗ᴸ-(X)[A]).obj K).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  Iff.rfl

omit [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A] in
/-- The test condition of Tor amplitude at a single sheaf `F`, written with
`AlgebraicGeometry.Etale.derivedTensor`. -/
lemma tensorSingleConcentratedIn_iff_derivedTensor (X : Scheme.{u}) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (F : Sheaf X.smallEtaleTopology A) :
    _root_.DerivedCategory.TensorSingleConcentratedIn _ a b K F ↔
      _root_.DerivedCategory.homologyConcentratedIn a b
        (((-⊗ᴸ-(X)[A]).obj K).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  Iff.rfl

omit [HasSmallSiteSheafify A] in
/-- If the projection map `Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y)` is an isomorphism, then
`Rf_* K ⊗ᴸ M_Y` has homology concentrated in `[a, b]` as soon as `Rf_*(K ⊗ᴸ M_X)` has. -/
lemma tensorSingleConcentratedIn_rightDerivedLowerStar_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) (M : A)
    [IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app (constantSingle A Y M))]
    {a b : ℤ} (h : _root_.DerivedCategory.homologyConcentratedIn a b
      ((R((f)_*[A])).obj (((-⊗ᴸ-(X)[A]).obj K).obj (constantSingle A X M)))) :
    _root_.DerivedCategory.TensorSingleConcentratedIn _ a b ((R((f)_*[A])).obj K)
      ((constantSheaf Y.smallEtaleTopology A).obj M) :=
  (tensorSingleConcentratedIn_iff_derivedTensor A Y a b _ _).2 <|
    (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (asIso (((rightDerivedLowerStarProjectionMap A f).app K).app (constantSingle A Y M)) ≪≫
        (R((f)_*[A])).mapIso
          (((-⊗ᴸ-(X)[A]).obj K).mapIso (leftDerivedUpperStarSingleConstantSheafIso A f M))).symm h

end General

variable (Λ : Type (u + 1)) [CommRing Λ]

section Projection

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- The projection map `Rf_* K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^* L)`, as a natural transformation in `L`. -/
noncomputable abbrev rightDerivedLowerStarProjectionMapApp :
    (-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      (L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ]) :=
  (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K

variable {Λ f K} in
/-- The projection map at `L` is an isomorphism as soon as it is one at an object isomorphic to
`L`. -/
lemma isIso_rightDerivedLowerStarProjectionMapApp_of_iso
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : L ≅ L') (h : IsIso ((rightDerivedLowerStarProjectionMapApp Λ f K).app L)) :
    IsIso ((rightDerivedLowerStarProjectionMapApp Λ f K).app L') :=
  (NatTrans.isIso_app_iff_of_iso _ e).1 h

/-- The projection map is an isomorphism at the constant complex `Λ_Y`. -/
lemma isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_self :
    IsIso ((rightDerivedLowerStarProjectionMapApp Λ f K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ Λ))) :=
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit (ModuleCat.{u + 1} Λ) f K
  isIso_rightDerivedLowerStarProjectionMapApp_of_iso
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) Y).symm this

/-- The projection map is an isomorphism at the constant complex on a zero module. -/
lemma isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_of_isZero
    {M : ModuleCat.{u + 1} Λ} (hM : IsZero M) :
    IsIso ((rightDerivedLowerStarProjectionMapApp Λ f K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y M)) := by
  have h : IsZero (constantSingle (ModuleCat.{u + 1} Λ) Y M) :=
    (_root_.DerivedCategory.singleFunctor _ 0).map_isZero
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map_isZero hM)
  exact isIso_of_source_target_iso_zero _
    (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj (R((f)_*[ModuleCat.{u + 1} Λ]).obj K)).map_isZero
      h).isoZero
    (((L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ (-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K) ⋙
        R((f)_*[ModuleCat.{u + 1} Λ])).map_isZero h).isoZero

/-- The short exact sequence `0 ⟶ Λ ⟶ Λⁿ⁺¹ ⟶ Λⁿ ⟶ 0` of the first coordinate and the last `n`
coordinates. -/
noncomputable abbrev finSuccShortComplex (n : ℕ) : ShortComplex (ModuleCat.{u + 1} Λ) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.single Λ (fun _ : Fin (n + 1) ↦ Λ) 0)
    (LinearMap.funLeft Λ Λ Fin.succ) (by
      ext x
      simp [LinearMap.funLeft, Fin.succ_ne_zero])

lemma finSuccShortComplex_shortExact (n : ℕ) : (finSuccShortComplex Λ n).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ (fun v ↦ ⟨fun hv ↦ ⟨v 0, ?_⟩, ?_⟩)
    (fun x y h ↦ by simpa using congr_fun h 0) (fun w ↦ ⟨Fin.cons 0 w, ?_⟩)
  · ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · have := congr_fun hv j
      simp only [ModuleCat.hom_ofHom, LinearMap.funLeft_apply] at this
      simp [this, Fin.succ_ne_zero]
      rfl
  · rintro ⟨x, rfl⟩
    ext j
    simp [LinearMap.funLeft, Fin.succ_ne_zero]
    rfl
  · ext j
    simp [LinearMap.funLeft]

/-- The projection map is an isomorphism at the constant complex on a free module of finite
rank. -/
lemma isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_pi (n : ℕ) :
    IsIso ((rightDerivedLowerStarProjectionMapApp Λ f K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ (Fin n → Λ)))) := by
  induction n with
  | zero =>
    refine isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_of_isZero Λ f K ?_
    rw [IsZero.iff_id_eq_zero]
    ext x i
    exact i.elim0
  | succ n ih =>
    exact NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ _
      (((finSuccShortComplex_shortExact Λ n).map_of_exact
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).singleTriangle_distinguished)
      (isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_self Λ f K) ih

end Projection

variable [Finite Λ] {k : Type u} [Field k] {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k))
  (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY]
  [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ)
  (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

include hf hd in
/-- Blueprint `proposition-open-direct-image-preserves-finite--1`: The projection formula with a
finitely presented constant coefficient.

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, `Λ` a
finite ring, `K ∈ D(X_ét, Λ)` bounded above and `M` a finitely generated `Λ`-module. Then the
projection map `Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y)` is an isomorphism.

It is an isomorphism for `M = Λ`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit`), hence
for `M` free of finite rank, both sides being triangulated in `M_Y`. For general `M`, both sides
vanish above `b + 2d` if `K` vanishes above `b`, `Rf_*` raising degrees by at most `2d`
(`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj`), and `M` is the cokernel of a map from
its first syzygy, again finitely generated, to a free module of finite rank; the way-out argument
`DerivedCategory.isIso_app_of_exists_distTriang` concludes. -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ)
    [K.IsLE b] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y M)) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  refine _root_.DerivedCategory.isIso_app_of_exists_distTriang
    (rightDerivedLowerStarProjectionMapApp Λ f K)
    (fun Z ↦ ∃ (M : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ M),
      Z = constantSingle (ModuleCat.{u + 1} Λ) Y M)
    (b + 2 * d) ?_ ?_ _ ⟨M, inferInstance, rfl⟩
  · rintro _ ⟨M, _, rfl⟩
    have : (R((f)_*[ModuleCat.{u + 1} Λ]).obj K).IsLE (b + 2 * d) :=
      isLE_rightDerivedLowerStar_obj Λ hΛ aX aY f hf d hd K b
    have hM : (L((f)^*[ModuleCat.{u + 1} Λ]).obj
        (constantSingle (ModuleCat.{u + 1} Λ) Y M)).IsLE 0 :=
      _root_.DerivedCategory.TStructure.t.isLE_of_iso
        (leftDerivedUpperStarSingleConstantSheafIso _ f M).symm 0
    have h₁ := isLE_derivedTensor_obj (ModuleCat.{u + 1} Λ) Y
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj K) (constantSingle (ModuleCat.{u + 1} Λ) Y M)
      (b + 2 * d) 0
    have h₂ := isLE_derivedTensor_obj (ModuleCat.{u + 1} Λ) X K
      (L((f)^*[ModuleCat.{u + 1} Λ]).obj (constantSingle (ModuleCat.{u + 1} Λ) Y M)) b 0
    rw [add_zero] at h₁ h₂
    exact ⟨h₁, @isLE_rightDerivedLowerStar_obj Λ _ hΛ k _ X Y aX aY _ _ _ _ f hf d hd _ b h₂⟩
  · rintro _ ⟨M, _, rfl⟩
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Λ M
    let S := ModuleCat.shortComplexOfCompEqZero (LinearMap.ker p).subtype p (by ext; simp)
    have hS : S.ShortExact :=
      ModuleCat.shortComplex_shortExact S p.exact_subtype_ker_map Subtype.val_injective hp
    exact ⟨_, (hS.map_of_exact
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).singleTriangle_distinguished,
      rfl, ⟨ModuleCat.of Λ (LinearMap.ker p), inferInstance, rfl⟩,
      isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_pi Λ f K n⟩

include hf hd in
/-- Blueprint `proposition-six-operations-dctf--2`: Direct image and finite Tor amplitude.

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and `Λ`
a finite ring. If `K ∈ D(X_ét, Λ)` has Tor amplitude in `[a, b]`, then `Rf_* K` has Tor amplitude
in `[a, b + 2d]`.

Let `κ = Λ ⧸ J`, `J` the Jacobson radical. By the projection formula
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`),
`Rf_* K ⊗ᴸ κ_Y ≅ Rf_*(K ⊗ᴸ κ_X)`; the complex `K ⊗ᴸ κ_X` has homology in `[a, b]`, so its
direct image has homology in `[a, b + 2d]`, `Rf_*` being left t-exact and raising degrees by at
most `2d`. The residue test
(`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn`)
concludes. The blueprint also assumes `f` separated, `K` bounded constructible and the exponent
of `Λ` invertible; none of this is needed. -/
theorem torAmplitudeIn_rightDerivedLowerStar_of_finite (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  rw [torAmplitudeIn_iff_tensorSingleConcentratedIn]
  have : K.IsLE b := (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta).2
  let κ := ModuleCat.of Λ (Λ ⧸ Ring.jacobson Λ)
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle Λ aX aY f hf d hd K b κ
  refine tensorSingleConcentratedIn_rightDerivedLowerStar_of_isIso _ f K κ ?_
  obtain ⟨h₁, h₂⟩ := (torAmplitudeIn_iff_forall_derivedTensor _ X a b K).1 hta
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj κ)
  exact ⟨@isGE_rightDerivedLowerStar_obj Λ _ X Y f _ a h₁,
    @isLE_rightDerivedLowerStar_obj Λ _ hΛ k _ X Y aX aY _ _ _ _ f hf d hd _ b h₂⟩

end Etale

end AlgebraicGeometry
