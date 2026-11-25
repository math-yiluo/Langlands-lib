/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!

# Dévissage of bounded constructible complexes of pro-étale module objects

A triangulated functor `Φ : D(X_proét, R) ⥤ D(Y_proét, R')` between derived categories of module
objects which carries every constructible module object placed in degree `0` into the bounded
constructible complexes carries all bounded constructible complexes into them, provided the bounded
constructible complexes on `Y` form a triangulated subcategory
(`AlgebraicGeometry.ProEtale.boundedConstructible_obj_of_forall_singleFunctor`). The proof is by
induction on the length of the range of a bounded complex `K`, along the truncation triangle
`τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` whose third term is `Hᵇ K` placed in degree `b`, as for étale
sheaves (`AlgebraicGeometry.Etale.boundedConstructible_obj_of_forall_singleFunctor`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X Y : Scheme.{u}}
  {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]
  {R' : Sheaf (Scheme.ProEt.topology Y) A} [MonObj R']

open _root_.DerivedCategory in
/-- **Dévissage for bounded constructible complexes of module objects.** Let the bounded
constructible complexes on `Y` form a triangulated subcategory. A triangulated functor
`Φ : D(X_proét, R) ⥤ D(Y_proét, R')` which carries every constructible module object placed in
degree `0` into `Dᵇc(Y, R')` carries `Dᵇc(X, R)` into `Dᵇc(Y, R')`: by induction on the length
of the range of a bounded complex `K`, along the truncation triangle
`τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` whose third term is `Hᵇ K` placed in degree `b`. -/
lemma boundedConstructible_obj_of_forall_singleFunctor
    [(boundedConstructible R').IsTriangulated]
    (Φ : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R) ⥤
      _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) A) R'))
    [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (h : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X) A) R, IsConstructibleModuleObject R F →
      boundedConstructible R' (Φ.obj ((singleFunctor _ 0).obj F)))
    {K : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)}
    (hK : boundedConstructible R K) : boundedConstructible R' (Φ.obj K) := by
  let P := boundedConstructible R'
  suffices H : ∀ (m : ℕ) (a : ℤ)
      (K : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)),
      K.IsGE a → K.IsLE (a + m - 1) →
      (∀ q, a ≤ q → q ≤ a + m - 1 → IsConstructibleModuleObject R ((homologyFunctor _ q).obj K)) →
      P (Φ.obj K) by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact H (b - a + 1).toNat a K ha (TStructure.t.isLE_of_le K b _ (by lia)) fun q _ _ ↦ hc q
  intro m
  induction m with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact P.prop_of_isZero (Φ.map_isZero (TStructure.t.isZero K (a - 1) a (by lia)))
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
    have hG : IsConstructibleModuleObject R G :=
      (hK b (by lia) (by lia)).of_iso (asIso ((homologyFunctor _ b).map T.mor₂) ≪≫
        (homologyFunctor _ b).mapIso eG ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G)
    have h₃ : P (Φ.obj T.obj₃) :=
      P.prop_of_iso (((Φ.commShiftIso (-b)).app _).symm ≪≫
        Φ.mapIso ((((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G) ≪≫ eG.symm))
        (P.le_shift (-b) _ (h G hG))
    -- the first term is handled by induction
    have h₁ : P (Φ.obj T.obj₁) := by
      refine ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) fun q hq₁ hq₂ ↦ ?_
      have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
        isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
          (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
      exact (hK q hq₁ (by lia)).of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
    exact P.ext_of_isTriangulatedClosed₂ _ (Φ.map_distinguished _ hT) h₁ h₃

end AlgebraicGeometry.ProEtale
