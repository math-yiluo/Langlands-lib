/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleDevissage

/-!

# Induction principle for bounded constructible complexes of module objects

A property of complexes of module objects on `X_proét` which holds for zero objects, is closed
under isomorphisms, shifts and extensions, and holds for every constructible module object placed
in degree `0`, holds for every bounded constructible complex
(`AlgebraicGeometry.ProEtale.prop_of_boundedConstructible`). The proof is by induction on the
length of the range of a bounded complex `K`, along the truncation triangle
`τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶` whose third term is `Hᵇ K` placed in degree `b`, as in
`AlgebraicGeometry.ProEtale.boundedConstructible_obj_of_forall_singleFunctor`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) A} [MonObj R]

open _root_.DerivedCategory in
/-- **Induction principle for bounded constructible complexes.** A property `P` of complexes of
`R`-module objects which holds for zero objects, is closed under isomorphisms, shifts and
extensions, and holds for every constructible module object placed in degree `0`, holds for every
bounded constructible complex. -/
lemma prop_of_boundedConstructible
    (P : ObjectProperty (_root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)))
    (h₀ : ∀ K, IsZero K → P K) (hiso : ∀ {K K'}, P K → (K ≅ K') → P K')
    (hshift : ∀ {K} (n : ℤ), P K → P (K⟦n⟧))
    (hext : ∀ T ∈ distTriang _, P T.obj₁ → P T.obj₃ → P T.obj₂)
    (h : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X) A) R, IsConstructibleModuleObject R F →
      P ((singleFunctor _ 0).obj F))
    {K : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)}
    (hK : boundedConstructible R K) : P K := by
  suffices H : ∀ (m : ℕ) (a : ℤ)
      (K : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)),
      K.IsGE a → K.IsLE (a + m - 1) →
      (∀ q, a ≤ q → q ≤ a + m - 1 → IsConstructibleModuleObject R ((homologyFunctor _ q).obj K)) →
      P K by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
    exact H (b - a + 1).toNat a K ha (TStructure.t.isLE_of_le K b _ (by lia)) fun q _ _ ↦ hc q
  intro m
  induction m with
  | zero =>
    intro a K _ _ _
    have : K.IsLE (a - 1) := by simpa using ‹K.IsLE (a + ↑(0 : ℕ) - 1)›
    exact h₀ _ (TStructure.t.isZero K (a - 1) a (by lia))
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
    have h₃ : P T.obj₃ :=
      hiso (hshift (-b) (h G hG)) ((((singleFunctors _).shiftIso (-b) b 0 (by lia)).app G) ≪≫
        eG.symm)
    -- the first term is handled by induction
    have h₁ : P T.obj₁ := by
      refine ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia)) fun q hq₁ hq₂ ↦ ?_
      have : IsIso ((homologyFunctor _ q).map T.mor₁) :=
        isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
          (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
      exact (hK q hq₁ (by lia)).of_iso (asIso ((homologyFunctor _ q).map T.mor₁)).symm
    exact hext T hT h₁ h₃

end AlgebraicGeometry.ProEtale
