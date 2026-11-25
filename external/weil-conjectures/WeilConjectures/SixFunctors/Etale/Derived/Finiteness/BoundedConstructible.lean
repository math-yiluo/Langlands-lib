/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.ConstructibleSheaf.FiniteMorphism

/-!
# Elementary operations preserving bounded constructibility

Exact functors which preserve constructible sheaves preserve bounded constructible complexes:
this applies to the extension by zero along a quasi-compact open immersion and to the direct
image along a finite morphism with Noetherian target.

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructible_of_isZero`
- `AlgebraicGeometry.Etale.boundedConstructible_mapDerivedCategory_openImmersionLowerShriek`
- `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar_of_isFinite`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- A zero object of the derived category of étale sheaves is bounded constructible. -/
lemma boundedConstructible_of_isZero
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsZero K) : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K := by
  have h (i : ℤ) := (_root_.DerivedCategory.homologyFunctor _ i).map_isZero hK
  exact ⟨⟨⟨0, (_root_.DerivedCategory.isGE_iff K 0).2 fun i _ ↦ h i⟩,
    ⟨0, (_root_.DerivedCategory.isLE_iff K 0).2 fun i _ ↦ h i⟩⟩,
    fun n ↦ IsConstructibleSheaf.of_isZero (h n)⟩

/-- Extension by zero along a quasi-compact open immersion `j` preserves bounded
constructibility: `j_!` is exact, and the extension by zero of a constructible sheaf is
constructible. -/
lemma boundedConstructible_mapDerivedCategory_openImmersionLowerShriek (j : X ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      (D((j)_!open[ModuleCat.{u + 1} Λ]).obj K) := by
  let F := (j)_!open[ModuleCat.{u + 1} Λ]
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  have := hK.2 n
  have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ n ⋙ F).obj K) :=
    IsConstructibleSheaf.openImmersionLowerShriek j j.closedComplement
      j.range_closedComplement ((_root_.DerivedCategory.homologyFunctor _ n).obj K)
  exact IsConstructibleSheaf.of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)

variable [Finite Λ]

/-- The derived direct image along a finite morphism `p : X ⟶ Y` with Noetherian target
preserves bounded constructibility: `p_*` is exact, so `Rp_*` commutes with the homology sheaves,
and it preserves constructible sheaves. -/
lemma boundedConstructible_rightDerivedLowerStar_of_isFinite [IsNoetherian Y] (p : X ⟶ Y)
    [IsFinite p] {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  let e (q : ℤ) : (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
        (p)_*[ModuleCat.{u + 1} Λ].obj ((_root_.DerivedCategory.homologyFunctor _ q).obj K) :=
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory _ p).app K) ≪≫
      (((p)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).symm.app K
  have hz (q : ℤ) (h : IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K)) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R((p)_*[ModuleCat.{u + 1} Λ])).obj K)) :=
    (((p)_*[ModuleCat.{u + 1} Λ]).map_isZero h).of_iso (e q)
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
  · exact (_root_.DerivedCategory.isGE_iff _ a).2
      fun q hq ↦ hz q ((_root_.DerivedCategory.isGE_iff _ a).1 ha q hq)
  · exact (_root_.DerivedCategory.isLE_iff _ b).2
      fun q hq ↦ hz q ((_root_.DerivedCategory.isLE_iff _ b).1 hb q hq)
  · have : IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj K) := hc q
    have := Scheme.IsConstructibleSheaf.lowerStar_of_isFinite p
      ((_root_.DerivedCategory.homologyFunctor _ q).obj K)
    exact IsConstructibleSheaf.of_iso (e q).symm

open _root_.DerivedCategory in
/-- **Dévissage for bounded constructible complexes.** A triangulated functor
`Φ : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` which carries every constructible sheaf placed in degree `0` into
`Dᵇc(Y, Λ)` carries `Dᵇc(X, Λ)` into `Dᵇc(Y, Λ)`: by induction on the length of the range of a
bounded complex `K`, along the truncation triangle `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` whose third
term is `Hᵇ K` placed in degree `b`. -/
lemma boundedConstructible_obj_of_forall_singleFunctor
    (Φ : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (h : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsConstructibleSheaf F →
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
        (Φ.obj ((singleFunctor _ 0).obj F)))
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y (Φ.obj K) := by
  let P := DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
  suffices H : ∀ (m : ℕ) (a : ℤ)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      K.IsGE a → K.IsLE (a + m - 1) →
      (∀ q, IsConstructibleSheaf ((homologyFunctor _ q).obj K)) → P (Φ.obj K) by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact H (b - a + 1).toNat a K ha (TStructure.t.isLE_of_le K b _ (by lia)) hc
  intro m
  induction m with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact boundedConstructible_of_isZero Λ
      (Φ.map_isZero (TStructure.t.isZero K (a - 1) a (by lia)))
  | succ m ih =>
    intro a K _ _ hK
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    -- the third term is `Hᵇ K` placed in degree `b`
    have : T.obj₃.IsLE b := by
      have : K.IsLE b := TStructure.t.isLE_of_le K (a + ↑(m + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b)
    have : T.obj₃.IsGE b := inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b)
    obtain ⟨G, ⟨eG⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃ b
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl (isZero_of_isLE _ (b - 1) _ (by lia))
      (isZero_of_isLE _ (b - 1) _ (by lia))
    have hG : IsConstructibleSheaf G := by
      have : IsConstructibleSheaf ((homologyFunctor _ b).obj T.obj₂) := hK b
      exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ b).map T.mor₂) ≪≫
        (homologyFunctor _ b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G)
    have h₃ : P (Φ.obj T.obj₃) :=
      P.prop_of_iso (((Φ.commShiftIso (-b)).app _).symm ≪≫
        Φ.mapIso ((((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G) ≪≫ eG.symm))
        (P.le_shift (-b) _ (h G hG))
    -- the first term is handled by induction
    have h₁ : P (Φ.obj T.obj₁) := by
      refine ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) fun q ↦ ?_
      by_cases hq : q < b
      · have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        have : IsConstructibleSheaf ((homologyFunctor _ q).obj T.obj₂) := hK q
        exact IsConstructibleSheaf.of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
      · have : T.obj₁.IsLE (b - 1) := TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
        exact IsConstructibleSheaf.of_isZero (isZero_of_isLE _ (b - 1) _ (by lia))
    exact P.ext_of_isTriangulatedClosed₂ _ (Φ.map_distinguished _ hT) h₁ h₃

end Etale

end AlgebraicGeometry
