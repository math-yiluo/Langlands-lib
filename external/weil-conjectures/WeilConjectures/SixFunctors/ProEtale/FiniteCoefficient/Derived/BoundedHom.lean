/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing

/-!
# Bounded morphisms out of `Dctf(X, Λ)` without generic finiteness

Every object of `Dctf(X_ét, Λ)` is compact with bounded morphisms
(`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor_of_generation`), and every
object of `Dctf(X_proét, Λ)` admits `N` with `Hom(C, L) = 0` for `L` of étale-origin cohomology in
degrees `≤ N`
(`ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor_of_generation`).

These restate `AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor` and
`AlgebraicGeometry.ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor`
with the same proofs, except that the reduction to the generators `Rg_* Rj_! L` uses only the
generation statement
`AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`
(`Dctf ⊆` thick envelope of the generators), and the invertibility of the exponent of `Λ` is not
assumed. The converse inclusion, that the generators lie in
`Dctf`, rests on Deligne's generic finiteness (`AlgebraicGeometry.Etale.smoothGenericDirectImage`)
and is not needed here.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme _root_.DerivedCategory

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `proposition-compactness-finite-coefficients`: on a finite-type scheme `X` over a
field `k` of finite cohomological dimension, every object of `Dctf(X_ét, Λ)` is compact in
`D(X_ét, Λ)` and has bounded morphisms, for a finite ring `Λ` whose exponent is invertible on `X`.
The reduction to the generators `Rg_* Rj_! L` only uses that they generate `Dctf(X_ét, Λ)`. -/
theorem compactBoundedHom_of_constructibleFiniteTor_of_generation [Finite Λ] {k : Type u}
    [Field k] (hk : HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    compactBoundedHom _ K := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  refine ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek Λ X _
    (fun str i Ubar j _ _ g _ _ _ L _ hL ↦ ?_) K hK
  have : TopologicalSpace.NoetherianSpace (str.domain i) :=
    (str.immersion i).isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have h₁ := compactBoundedHom_unit_of_finiteType Λ hΛ hk (j ≫ g ≫ aX)
  have h₂ := compactBoundedHom_singleFunctor_of_isFiniteLocallyConstantSheaf Λ h₁ L hL
  have h₃ := compactBoundedHom_mapDerivedCategory_openImmersionLowerShriek Λ j h₂
  exact compactBoundedHom_rightDerivedLowerStar_of_isClosedImmersion Λ hΛ aX g
    ((compactBoundedHom _).prop_of_iso
      ((rightDerivedLowerShriekIsoOfIsOpenImmersion Λ j).app _).symm h₃)

end Etale

namespace ProEtale.DerivedCategory

open _root_.DerivedCategory.TStructure

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]

include hk aX in
/-- An object of `Dctf(X, Λ)` is `ν^*` of an object of `Dctf(X_ét, Λ)` which is compact with
bounded morphisms in `D(X_ét, Λ)`. -/
lemma exists_compactBoundedHom_of_constructibleFiniteTor_of_generation
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) :
    ∃ C' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      _root_.DerivedCategory.compactBoundedHom _ C' ∧
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj C' ≅ C) := by
  obtain ⟨⟨C', hC', ⟨e⟩⟩, a, b, hab⟩ := hC
  have hC't : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C' :=
    ⟨hC', a, b, (torAmplitudeIn_mapDerivedCategory_iff a b C').1
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩
  exact ⟨C', Etale.compactBoundedHom_of_constructibleFiniteTor_of_generation Λ hk aX hC't, ⟨e⟩⟩

include hk aX in
/-- Blueprint `proposition-compactness-finite-coefficients--1`, the vanishing step: for `C` in
`Dctf(X, Λ)` there is `N` with `Hom(C, L) = 0` for every pro-étale complex `L` with cohomology
sheaves of étale origin in degrees `≤ N`. -/
lemma exists_forall_eq_zero_of_constructibleFiniteTor_of_generation
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) :
    ∃ N : ℤ, ∀ L, etaleOriginHomology Λ X L → L.IsLE N → ∀ f : C ⟶ L, f = 0 := by
  obtain ⟨C', hP, ⟨e⟩⟩ := exists_compactBoundedHom_of_constructibleFiniteTor_of_generation hk aX hC
  obtain ⟨-, n₁, hn₁⟩ := (_root_.DerivedCategory.compactBoundedHom _).le_shift (1 : ℤ) C' hP
  obtain ⟨-, n₀, hn₀⟩ := hP
  have := CountableAB4Star.ofShape
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℕ
  refine ⟨min n₀ n₁, fun L hL hLN f ↦ ?_⟩
  -- the bounded truncations of `L` are of étale origin
  have htr (n : ℕ) : ∃ G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)), t.plus G ∧ G.IsLE (min n₀ n₁) ∧
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G ≅ (t.truncGE (-(n : ℤ))).obj L) := by
    have hT := _root_.DerivedCategory.homologyProperty_truncGE hL (-(n : ℤ))
    obtain ⟨G, hG, ⟨eG⟩⟩ := plusEtaleOrigin_of_etaleOriginHomology Λ X hT
      ⟨⟨-(n : ℤ), inferInstance⟩, ⟨min n₀ n₁, inferInstance⟩⟩
    exact ⟨G, hG, isLE_of_isLE_mapDerivedCategory_comparisonUpperStar
      (t.isLE_of_iso eG.symm _), ⟨eG⟩⟩
  suffices h : ∀ g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj C' ⟶ L, g = 0 by
    rw [← cancel_epi e.hom, comp_zero]
    exact h _
  refine (_root_.DerivedCategory.isHomotopyLimit_truncGECone L).hom_ext_zero
    (fun n g ↦ ?_) (fun n g ↦ ?_)
  · obtain ⟨G, hG, hGN, ⟨eG⟩⟩ := htr n
    have : g ≫ eG.inv = 0 := eq_zero_of_comparisonUpperStar hG
      (fun φ ↦ hn₀ G (t.isLE_of_le G (min n₀ n₁) n₀ (min_le_left _ _)) φ) _
    rwa [← cancel_mono eG.inv, zero_comp]
  · obtain ⟨G, hG, hGN, ⟨eG⟩⟩ := htr n
    have : ((D(ν^*(X)[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app C' ≫ g ≫ eG.inv = 0 :=
      eq_zero_of_comparisonUpperStar hG
        (fun φ ↦ hn₁ G (t.isLE_of_le G (min n₀ n₁) n₁ (min_le_right _ _)) φ) _
    rwa [← cancel_epi (((D(ν^*(X)[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app C'),
      ← cancel_mono eG.inv, comp_zero, zero_comp, Category.assoc]

end ProEtale.DerivedCategory

end AlgebraicGeometry
