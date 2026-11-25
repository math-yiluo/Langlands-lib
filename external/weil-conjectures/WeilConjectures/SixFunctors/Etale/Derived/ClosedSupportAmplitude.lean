/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.OpenComplement
public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# Amplitude of the exceptional inverse image along a closed immersion

Let `i : Z ⟶ T` be a closed immersion with open complement `j : U ⟶ T` and `Λ` a finite ring.
If `R^q j_* M = 0` for every sheaf `M` of `Λ`-modules and every `q > c`, then the exceptional
inverse image `Ri^!` (the right adjoint of `Ri_! = Ri_*` on `D(T_ét, Λ)`) carries complexes with
homology in `[a, b]` to complexes with homology in `[a, b + c + 1]`
(`AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedUpperShriek`), and under the full
open-complement condition `D_c^{[a, b]}(T, Λ)` into `D_c^{[a, b + c + 1]}(Z, Λ)`
(`AlgebraicGeometry.Etale.constructibleIn_rightDerivedUpperShriek`). Together these are blueprint
`theorem-f-shriek-finite-coefficients--1`.

The proof uses the supported localization triangle
`Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (Ri_! Ri^! K)[1]`
(`AlgebraicGeometry.Etale.supportedLocalizationTriangle_mem_distTriang`): `Rj_* j^* K` has
homology in `[a, b + c]`, so `Ri_! Ri^! K` has homology in `[a, b + c + 1]`, and
`Ri^! K ≅ i^* Ri_! Ri^! K` since `Ri_!` is fully faithful
(`AlgebraicGeometry.Etale.mapDerivedUpperStarRightDerivedLowerShriekIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Z T U : Scheme.{u}}

/-- For a closed immersion `i`, the pullback `i^*` is left inverse to `Ri_!`:
`i^* Ri_! N ≅ N`. Indeed `Ri_!` is fully faithful
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`) and isomorphic to
`Ri_*`, so the counit of `i^* ⊣ Ri_*` is an isomorphism. -/
noncomputable def mapDerivedUpperStarRightDerivedLowerShriekIso (i : Z ⟶ T) [IsClosedImmersion i]
    [HasCompactification i]
    (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D((i)^*[ModuleCat.{u + 1} Λ]).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj N) ≅ N :=
  have := isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i
  have : IsIso (rightDerivedUpperShriekAdjunction Λ i).unit :=
    NatIso.isIso_of_isIso_app _
  let hff := (rightDerivedUpperShriekAdjunction Λ i).fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  let e := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i
  have : (R((i)_*[ModuleCat.{u + 1} Λ])).Full := Functor.Full.of_iso e
  have : (R((i)_*[ModuleCat.{u + 1} Λ])).Faithful := Functor.Faithful.of_iso e
  have : IsIso (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit :=
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      i).counit_isIso_of_R_fully_faithful
  D((i)^*[ModuleCat.{u + 1} Λ]).mapIso (e.app N) ≪≫
    asIso ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit.app N)

variable (i : Z ⟶ T) (j : U ⟶ T) [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
/-- The supported term `Ri_! Ri^! K` of the supported localization triangle has homology in
`[a, b + c + 1]` if `K` has homology in `[a, b]` and `R^q j_*` vanishes above `c`. -/
lemma homologyConcentratedIn_rightDerivedLowerShriek_rightDerivedUpperShriek {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj K)) := by
  obtain ⟨hKa, hKb⟩ := hK
  let T' := (supportedLocalizationTriangle Λ i j K (supportedLocalizationBoundary Λ i j hij K))
  have hT : T'.invRotate ∈ distTriang _ :=
    inv_rot_of_distTriang _ (supportedLocalizationTriangle_mem_distTriang Λ i j hij K)
  -- the third term `Rj_* j^* K` has homology in `[a, b + c]`
  let C := (R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)
  have e := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K
  have : K.IsGE a := hKa
  have : K.IsLE b := hKb
  have : (D((j)^*[ModuleCat.{u + 1} Λ]).obj K).IsGE a := Functor.isGE_mapDerivedCategory_obj _ K a
  have : (D((j)^*[ModuleCat.{u + 1} Λ]).obj K).IsLE b := Functor.isLE_mapDerivedCategory_obj _ K b
  have : ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K).IsGE a :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have : ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K).IsLE b :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have : C.IsGE a := isGE_rightDerivedLowerStar_obj Λ j _ a
  have : C.IsLE (b + c) := isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage hc _ b
  have h₁ : (T'.invRotate.obj₁).IsGE (a + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift C a (-1) (a + 1)
  have h₁' : (T'.invRotate.obj₁).IsLE (b + c + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift C (b + c) (-1) (b + c + 1)
  have h₃ : (T'.invRotate.obj₃).IsGE a := hKa
  have h₃' : (T'.invRotate.obj₃).IsLE (b + c + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_le K b (b + c + 1) (by lia)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ hT a
      (_root_.DerivedCategory.TStructure.t.isGE_of_ge _ a (a + 1) (by lia)) h₃,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ hT (b + c + 1) h₁' h₃'⟩

include hij in
/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Closed-support amplitude.

Let `i : Z ⟶ T` be a closed immersion with open complement `j : U ⟶ T`, and `Λ` a finite ring.
Suppose that `R^q j_* M = 0` for every sheaf `M` of `Λ`-modules on `U_ét` and every `q > c`. Then
the exceptional inverse image `Ri^!` carries `D^{[a, b]}(T_ét, Λ)` into
`D^{[a, b + c + 1]}(Z_ét, Λ)`. The constructible version is
`AlgebraicGeometry.Etale.constructibleIn_rightDerivedUpperShriek`.

The supported localization triangle `Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` puts `Ri_! Ri^! K` in
`[a, b + c + 1]`, as `Rj_* j^* K` lies in `[a, b + c]`
(`AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedLowerShriek_rightDerivedUpperShriek`),
and the exact `i^*` recovers `Ri^! K ≅ i^* Ri_! Ri^! K`
(`AlgebraicGeometry.Etale.mapDerivedUpperStarRightDerivedLowerShriekIso`). -/
theorem homologyConcentratedIn_rightDerivedUpperShriek {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b K) :
    _root_.DerivedCategory.homologyConcentratedIn a (b + c + 1)
      ((R(i)^![Λ]).obj K) := by
  obtain ⟨h₁, h₂⟩ :=
    homologyConcentratedIn_rightDerivedLowerShriek_rightDerivedUpperShriek i j hij hc hK
  have := h₁
  have := h₂
  have : (D((i)^*[ModuleCat.{u + 1} Λ]).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj K))).IsGE a := Functor.isGE_mapDerivedCategory_obj _ _ a
  have : (D((i)^*[ModuleCat.{u + 1} Λ]).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj K))).IsLE (b + c + 1) :=
    Functor.isLE_mapDerivedCategory_obj _ _ _
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i _) a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i _) (b + c + 1)⟩

include hij in
/-- Under the open-complement condition with constant `c`, the supported term `Ri_! Ri^! K` of
the supported localization triangle of a bounded constructible `K` is bounded constructible:
`K` and `Rj_* j^* K` are, by dévissage of `Rj_*` to constructible sheaves
(`AlgebraicGeometry.Etale.boundedConstructible_obj_of_forall_singleFunctor`). -/
lemma boundedConstructible_rightDerivedLowerShriek_rightDerivedUpperShriek {c : ℕ}
    (h : OpenComplementCondition Λ j c)
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj K)) := by
  let P := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
  have hjK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U ((L((j)^*[ModuleCat.{u +
      1} Λ])).obj K) :=
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U).prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K).symm
      (hK.mapDerivedCategory_upperStar j)
  have hC : P ((R((j)_*[ModuleCat.{u + 1} Λ])).obj ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
    refine boundedConstructible_obj_of_forall_singleFunctor Λ (R((j)_*[ModuleCat.{u + 1} Λ])) (fun F
        hF ↦ ?_) hjK
    refine ⟨⟨⟨0, isGE_rightDerivedLowerStar_obj Λ j _ 0⟩, ⟨c, ?_⟩⟩,
      fun q ↦ h.isConstructibleSheaf_homology F q⟩
    simpa using isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage h.1
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) 0
  exact P.ext_of_isTriangulatedClosed₁ _
    (supportedLocalizationTriangle_mem_distTriang Λ i j hij K) hK hC

include hij in
/-- Blueprint `theorem-f-shriek-finite-coefficients--1`: Closed-support amplitude, constructible
version.

Let `i : Z ⟶ T` be a closed immersion with open complement `j : U ⟶ T`, and `Λ` a finite ring.
If `(U, T)` satisfies the open-complement condition with constant `c`
(`AlgebraicGeometry.Etale.OpenComplementCondition`: `R^q j_*` vanishes above `c` and preserves
constructibility), then `Ri^!` carries `D_c^{[a, b]}(T, Λ)` into `D_c^{[a, b + c + 1]}(Z, Λ)`.

The amplitude is `AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedUpperShriek`. For
constructibility, the supported term `Ri_! Ri^! K` of the supported localization triangle is
bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek_rightDerivedUpperShriek`),
and so is its pullback `i^* Ri_! Ri^! K ≅ Ri^! K`. -/
theorem constructibleIn_rightDerivedUpperShriek {c : ℕ} (h : OpenComplementCondition Λ j c)
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b K) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) Z a (b + c + 1)
      ((R(i)^![Λ]).obj K) :=
  ⟨(DerivedCategory.boundedConstructible _ Z).prop_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i _)
      ((boundedConstructible_rightDerivedLowerShriek_rightDerivedUpperShriek i j hij h
        hK.1).mapDerivedCategory_upperStar i),
    homologyConcentratedIn_rightDerivedUpperShriek i j hij h.1 hK.2⟩

end Etale

end AlgebraicGeometry
