/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SepClosedPoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# Compactly supported cohomology is perfect

Compactly supported cohomology of a bounded constructible complex of finite Tor amplitude over
a separably closed field is a perfect complex of `Λ`-modules, and so are the derived geometric
stalks of such a complex (`lemma-perfect-complexes-geometric-point`).

## Implementation notes

`lemma-perfect-complexes-geometric-point` concludes that `RΓ_c(X, K)` is *perfect*: bounded, with
finite cohomology modules, and of finite Tor amplitude. The three are proved separately below,
finite Tor amplitude in the sense of `DerivedCategory.finiteTorAmplitude` for `D(ModuleCat Λ)`; they
are assembled into perfectness in `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`
(`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`). The geometric
stalk `RΓ(Spec Ω, Lx̄^* K)` is perfect because `Lx̄^*` preserves `Dctf` and `RΓ` on a separably
closed point carries `Dctf` into perfect complexes.

## Main statements

- `AlgebraicGeometry.Etale.isPerfect_geometricStalk`
- `AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`
- `AlgebraicGeometry.Etale.finite_compactlySupportedCohomology`
- `AlgebraicGeometry.Etale.finiteTorAmplitude_compactlySupportedGlobalSections`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
section TorAmplitude

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Tor amplitude in `[a, b]` of an object `K` of `D(X_ét)`, written with
`AlgebraicGeometry.Etale.derivedTensor`: `K ⊗ᴸ F` has homology concentrated in `[a, b]` for
every sheaf `F` placed in degree `0`. -/
lemma DerivedCategory.torAmplitudeIn_iff_derivedTensor (X : Scheme.{u}) (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.torAmplitudeIn A X a b K ↔
      ∀ F : Sheaf X.smallEtaleTopology A, _root_.DerivedCategory.homologyConcentratedIn a b
        (((derivedTensor A X).obj K).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) :=
  Iff.rfl

end TorAmplitude

/-- The compactly supported direct image `Rf_!` of a sheaf placed in degree `0` is concentrated in
degrees `≥ 0`: it is `Rg_*` of the extension by zero `i_! F` placed in degree `0`, for the chosen
compactification `X ⟶[i] Z ⟶[g] Y` of `f`. -/
lemma isGE_rightDerivedLowerShriek_obj_singleFunctor (f : X ⟶ Y) [HasCompactification f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).IsGE
      0 := by
  let c := HasCompactification.compactification f
  have : ((R((c.g)_*[ModuleCat.{u + 1} Λ])).obj
      ((((c.i)_!open[ModuleCat.{u + 1} Λ]) ⋙ _root_.DerivedCategory.singleFunctor _ 0).obj
        F)).IsGE 0 :=
    ((c.g)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor
      (((c.i)_!open[ModuleCat.{u + 1} Λ]).obj F)
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((R((c.g)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((((c.i)_!open[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F).symm) 0

/-- `Rf_!` carries a bounded object concentrated in degrees `≥ a` into degrees `≥ a`. -/
lemma isGE_rightDerivedLowerShriek_obj (f : X ⟶ Y) [HasCompactification f]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : _root_.DerivedCategory.TStructure.t.bounded M) (a : ℤ) [M.IsGE a] :
    ((R(f)_![ModuleCat.{u + 1} Λ]).obj M).IsGE a := by
  simpa using _root_.DerivedCategory.isGE_obj_of_isGE (R(f)_![ModuleCat.{u + 1} Λ]) 0
    (isGE_rightDerivedLowerShriek_obj_singleFunctor Λ f) M hM a

/-- The projection formula at finite coefficients against a sheaf placed in degree `0`:
`Rf_! K ⊗ᴸ G ≅ Rf_!(K ⊗ᴸ f^* G)`. -/
lemma nonempty_iso_tensor_singleFunctor_obj_rightDerivedLowerShriek [Finite Λ] (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((f)^*[ModuleCat.{u + 1} Λ].obj G)))) := by
  obtain ⟨e⟩ := nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f
    K (hasProjectionFormula_of_finite Λ f K)
  exact ⟨e.app _ ≪≫ (R(f)_![ModuleCat.{u + 1} Λ]).mapIso
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory _ f).app _ ≪≫
        (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app G))⟩

section Perfectness

variable [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] [HasCompactification aX]
  [HasInvertibleExponent Λ X]

omit [IsSeparated aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Perfectness of compact cohomology and of
geometric stalks

**Boundedness of compactly supported cohomology.** Let `Λ` be a finite coefficient ring, `k`
separably closed, `X` separated of finite type over `k` with structure morphism `a_X`, and
`K ∈ D^b_{ctf}(X, Λ)`. Then `RΓ_c(X, K) = Ra_{X!} K` vanishes in all but finitely many
degrees. Separable closedness of the base is essential: over `Spec ℚ` already
`H¹_c(Spec ℚ, ℤ/n) = Hom(G_ℚ, ℤ/n)` is infinite. -/
theorem isZero_compactlySupportedCohomology_of_lt
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := boundedConstructible_rightDerivedLowerShriek Λ aX aX (𝟙 _)
    (Category.comp_id aX) K hK.1
  refine ⟨a, b, fun q hq ↦ IsZero.of_iso ((Sheaf.Γ _ _).map_isZero ?_)
    ((homologyRightDerivedGlobalSectionsIsoOfIsSepClosed q).app _)⟩
  rcases hq with hq | hq
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha q hq
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb q hq

omit [IsSeparated aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Perfectness of compact cohomology and of
geometric stalks

**Finiteness of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, every compactly supported
cohomology module `H^q_c(X, K)` is a finite `Λ`-module. Together with boundedness and finite
Tor amplitude these are exactly perfectness over the Artinian local ring `A_{E,n}`. -/
theorem finite_compactlySupportedCohomology
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (q : ℤ) :
    Module.Finite Λ ((H_c(aX)[ModuleCat.{u + 1} Λ](q)).obj K) := by
  let L := (_root_.DerivedCategory.homologyFunctor _ q).obj ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)
  have : IsConstructibleSheaf L := (boundedConstructible_rightDerivedLowerShriek Λ aX aX (𝟙 _)
    (Category.comp_id aX) K hK.1).2 q
  have := finite_Γ_of_isConstructibleSheaf L
  have : Module.Finite Λ ((_root_.DerivedCategory.homologyFunctor _ q ⋙
      Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)) := this
  exact Module.Finite.equiv ((homologyRightDerivedGlobalSectionsIsoOfIsSepClosed q).app
    ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K)).symm.toLinearEquiv

omit [IsSeparated aX] in
/-- Blueprint `lemma-perfect-complexes-geometric-point`: Perfectness of compact cohomology and of
geometric stalks

**Finite Tor amplitude of compactly supported cohomology.** In the situation of
`AlgebraicGeometry.Etale.isZero_compactlySupportedCohomology_of_lt`, the complex of
`Λ`-modules `RΓ_c(X, K)` has finite Tor amplitude. If `K` has Tor amplitude in `[a, b]` and
the geometric fibres of `a_X` have dimension `≤ d`, then for every sheaf `F` on `Spec k` the
projection formula gives `Ra_{X!} K ⊗ᴸ F ≅ Ra_{X!}(K ⊗ᴸ a_X^* F)`, which is concentrated in
degrees `[a, b + 2d]` (`Ra_{X!}` is left t-exact and has cohomological amplitude `2d`). So
`Ra_{X!} K` has Tor amplitude in `[a, b + 2d]`, and so has `RΓ_c(X, K)`, global sections over
the separably closed `k` being a stalk. -/
theorem finiteTorAmplitude_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    _root_.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ)
      ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K) := by
  obtain ⟨-, a, b, hab⟩ := hK
  have := noetherianSpace_of_hasCompactification aX (𝟙 (Spec (.of k)))
  have : QuasiCompact aX := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_isPullback aX
  refine ⟨a, b + 2 * d, torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed
    ((DerivedCategory.torAmplitudeIn_iff_derivedTensor _ _ a (b + 2 * d) _).2 fun F ↦ ?_)⟩
  replace hab := (DerivedCategory.torAmplitudeIn_iff_derivedTensor _ _ a b K).1 hab
  obtain ⟨e⟩ := nonempty_iso_tensor_singleFunctor_obj_rightDerivedLowerShriek Λ aX K F
  -- `M = K ⊗ᴸ a^* F` is concentrated in degrees `[a, b]`
  let M := ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj ((aX)^*[ModuleCat.{u + 1} Λ].obj F))
  obtain ⟨hMa, hMb⟩ := hab ((aX)^*[ModuleCat.{u + 1} Λ].obj F)
  have : M.IsGE a := hMa
  have : M.IsLE b := hMb
  have hM : _root_.DerivedCategory.TStructure.t.bounded M := ⟨⟨a, hMa⟩, ⟨b, hMb⟩⟩
  have := isGE_rightDerivedLowerShriek_obj Λ aX M hM a
  -- `Ra_!` sends `M` into degrees `≤ b + 2d`
  have : ((R(aX)_![ModuleCat.{u + 1} Λ]).obj M).IsLE (b + 2 * d) := by
    by_cases hX : IsEmpty X
    · exact _root_.DerivedCategory.TStructure.t.isLE_of_isZero
        (Functor.map_isZero _ (isZero_derivedCategory_of_isEmpty (ModuleCat.{u + 1} Λ) X M)) _
    have : Nonempty X := not_isEmpty_iff.1 hX
    have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aX
    refine _root_.DerivedCategory.isLE_obj_of_isLE (R(aX)_![ModuleCat.{u + 1} Λ]) (2 * d)
      (fun F ↦ ?_) M hM b
    rw [_root_.DerivedCategory.isLE_iff]
    exact fun i hi ↦ isZero_homology_rightDerivedLowerShriek_singleFunctor Λ aX aX (𝟙 _)
      (Category.comp_id _) d (fun Ω _ _ s ↦ hd Ω s _ _ (IsPullback.of_hasPullback aX s)) F i
      (by lia)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm (b + 2 * d)⟩

end Perfectness

section Stalk

variable [Finite Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Compact-support perfectness (geometric
stalks).

Also blueprint `lemma-perfect-complexes-geometric-point`: Perfectness of compact cohomology and of
geometric stalks.

For a finite coefficient ring `Λ`, `K ∈ D^b_{ctf}(X, Λ)` and a geometric point
`x̄ : Spec Ω ⟶ X` (`Ω` separably closed), the derived geometric stalk
`K_x̄ = RΓ(Spec Ω, Lx̄^* K)` is a perfect complex of `Λ`-modules: `Lx̄^*` preserves `Dctf`, and
`RΓ(Spec Ω, -)` carries `Dctf(Spec Ω, Λ)` into perfect complexes. -/
theorem isPerfect_geometricStalk (x : Spec (.of Ω) ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of Ω))).obj
      ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K)).IsPerfect :=
  isPerfect_rightDerivedGlobalSections_of_isSepClosed _
    (constructibleFiniteTor_leftDerivedUpperStar _ x hK)

end Stalk

end Etale

end AlgebraicGeometry
