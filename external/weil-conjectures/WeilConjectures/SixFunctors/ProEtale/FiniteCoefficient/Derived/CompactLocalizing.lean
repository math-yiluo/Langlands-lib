/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.Triangulated.CompactFamily
public import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Objects of `Dctf(X, Λ)` are compact in `Loc(Dctf(X, Λ))`

Blueprint `proposition-compactness-finite-coefficients--1`. Let `k` be a field of finite
cohomological dimension for `Λ`-modules, `X` a finite-type `k`-scheme and `Λ` a finite ring whose
exponent is invertible on `X`. Every object `C` of `Dctf(X, Λ)` is compact in `Loc(Dctf(X, Λ))`
(`AlgebraicGeometry.ProEtale.DerivedCategory.isCompactObj_of_constructibleFiniteTor`).

Write `C = ν^* C'` with `C'` in `Dctf(X_ét, Λ)`, which is compact with bounded morphisms in
`D(X_ét, Λ)` (`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor`). Morphisms
from `C` to an object `Y` with cohomology sheaves of étale origin (a class containing
`Loc(Dctf(X, Λ))`) only depend on the truncation `τ_{[N, m]} Y` for suitable `N ≤ m`:

* `Hom(C, L) = 0` for `L` of étale-origin cohomology in degrees `≤ N`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.exists_forall_eq_zero_of_constructibleFiniteTor`):
  `L` is the homotopy limit of its bounded truncations (left completeness of `D(X_proét)`), and
  `Hom(ν^* C', ν^* G) = Hom(C', G)` for bounded `G`;
* `Hom(C, Z) = 0` for `Z` in degrees `> m`, since `C` is bounded above.

On uniformly bounded families of étale origin, `ν^*` identifies the morphisms out of `C` with the
étale ones, where `C'` is compact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme _root_.DerivedCategory.TStructure

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
  [HasInvertibleExponent Λ X]

namespace DerivedCategory

include hk aX in
/-- An object of `Dctf(X, Λ)` is `ν^*` of an object of `Dctf(X_ét, Λ)` which is compact with
bounded morphisms in `D(X_ét, Λ)`. -/
lemma exists_compactBoundedHom_of_constructibleFiniteTor
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) :
    ∃ C' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      _root_.DerivedCategory.compactBoundedHom _ C' ∧
        Nonempty (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj C' ≅ C) := by
  obtain ⟨⟨C', hC', ⟨e⟩⟩, a, b, hab⟩ := hC
  have hC't : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C' :=
    ⟨hC', a, b, (torAmplitudeIn_mapDerivedCategory_iff a b C').1
      ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩
  exact ⟨C', Etale.compactBoundedHom_of_constructibleFiniteTor Λ hk aX hC't, ⟨e⟩⟩

omit [Finite Λ] [HasInvertibleExponent Λ X] in
/-- A morphism `ν^* C' ⟶ ν^* G` with `G` bounded below and `Hom(C', G) = 0` vanishes. -/
lemma eq_zero_of_comparisonUpperStar
    {C' G : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hG : _root_.DerivedCategory.TStructure.t.plus G) (h : ∀ f : C' ⟶ G, f = 0)
    (g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj C' ⟶ D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) :
    g = 0 := by
  obtain ⟨φ, rfl⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map C' G hG).2 g
  simp [h φ]

include hk aX in
/-- Blueprint `proposition-compactness-finite-coefficients--1`, the vanishing step: for `C` in
`Dctf(X, Λ)` there is `N` with `Hom(C, L) = 0` for every pro-étale complex `L` with cohomology
sheaves of étale origin in degrees `≤ N`. -/
lemma exists_forall_eq_zero_of_constructibleFiniteTor
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) :
    ∃ N : ℤ, ∀ L, etaleOriginHomology Λ X L → L.IsLE N → ∀ f : C ⟶ L, f = 0 := by
  obtain ⟨C', hP, ⟨e⟩⟩ := exists_compactBoundedHom_of_constructibleFiniteTor hk aX hC
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

include hk aX in
/-- An object of `Dctf(X, Λ)` is compact for every family of pro-étale complexes with cohomology
sheaves of étale origin concentrated in a common interval `[a, b]`: such a family is `ν^*` of a
family of bounded below étale complexes, and `ν^*` preserves coproducts and is fully faithful on
bounded below complexes. -/
lemma compactFor_of_isGE_of_isLE
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) {J : Type (u + 1)}
    (T : J → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (a b : ℤ) (hT : ∀ j, etaleOriginHomology Λ X (T j) ∧ (T j).IsGE a ∧ (T j).IsLE b) :
    CompactFor C T := by
  obtain ⟨C', ⟨hC', -⟩, ⟨eC⟩⟩ := exists_compactBoundedHom_of_constructibleFiniteTor hk aX hC
  choose G hG e' using fun j ↦ plusEtaleOrigin_of_etaleOriginHomology Λ X (hT j).1
    ⟨⟨a, (hT j).2.1⟩, ⟨b, (hT j).2.2⟩⟩
  let e (j : J) := (e' j).some
  have hGa (j : J) : (G j).IsGE a := by
    have := (hT j).2.1
    exact isGE_of_isGE_mapDerivedCategory_comparisonUpperStar (t.isGE_of_iso (e j).symm a)
  have hS : (∐ G).IsGE a := _root_.DerivedCategory.isGE_sigma G a hGa
  have : PreservesColimitsOfShape (Discrete J) D(ν^*(X)[ModuleCat.{u + 1} Λ]) :=
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).leftAdjoint_preservesColimits.1
  let φ := sigmaComparison D(ν^*(X)[ModuleCat.{u + 1} Λ]) G
  let ψ := Limits.Sigma.map fun j ↦ (e j).inv
  intro f
  obtain ⟨f'', hf''⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map C' (∐ G)
    ⟨a, hS⟩).2 (eC.hom ≫ f ≫ ψ ≫ φ)
  obtain ⟨S, g, hg⟩ := hC' _ (coproductIsCoproduct G) f''
  refine ⟨S, fun j ↦ eC.inv ≫ D(ν^*(X)[ModuleCat.{u + 1} Λ]).map (g j) ≫ (e j).hom, ?_⟩
  rw [← cancel_epi eC.hom, ← cancel_mono (ψ ≫ φ), Category.assoc]
  dsimp only at hf''
  rw [← hf'', hg, Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [ψ, φ]

include hk aX in
/-- Blueprint `proposition-compactness-finite-coefficients--1`: an object `C` of `Dctf(X, Λ)` is
compact for every family of pro-étale complexes with cohomology sheaves of étale origin. Morphisms
out of `C` only see the truncations `τ_{≥ N} τ_{≤ m}`, on which `C` is compact
(`AlgebraicGeometry.ProEtale.DerivedCategory.compactFor_of_isGE_of_isLE`). -/
lemma compactFor_of_etaleOriginHomology
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) {J : Type (u + 1)}
    (Y : J → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hY : ∀ j, etaleOriginHomology Λ X (Y j)) : CompactFor C Y := by
  obtain ⟨N, hN⟩ := exists_forall_eq_zero_of_constructibleFiniteTor hk aX hC
  obtain ⟨b, hb⟩ := hC.1.bounded.2
  let m := max b N
  let A (j : J) := (t.truncLE m).obj (Y j)
  have hA (j : J) : etaleOriginHomology Λ X (A j) :=
    _root_.DerivedCategory.homologyProperty_truncLE (hY j) m
  -- `𝓔`-objects in degrees `< N` receive no morphisms from `C`
  have hN' (W : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
      (hW : etaleOriginHomology Λ X W) (hW' : W.IsLE (N - 1)) :
      (∀ f : C ⟶ W, f = 0) ∧ ∀ f : C ⟶ W⟦(1 : ℤ)⟧, f = 0 := by
    refine ⟨hN W hW (t.isLE_of_le W (N - 1) N (by lia)), hN _
      ((etaleOriginHomology Λ X).le_shift 1 W hW) ?_⟩
    have : (W⟦(1 : ℤ)⟧).IsLE (N - 2) := t.isLE_shift W (N - 1) 1 (N - 2) (by lia)
    exact t.isLE_of_le _ (N - 2) N (by lia)
  have hLT (j : J) : etaleOriginHomology Λ X ((t.truncLT N).obj (A j)) :=
    (etaleOriginHomology Λ X).prop_of_iso ((t.truncLEIsoTruncLT (N - 1) N (by lia)).app _)
      (_root_.DerivedCategory.homologyProperty_truncLE (hA j) (N - 1))
  -- the bounded truncations
  have hT : CompactFor C fun j ↦ (t.truncGE N).obj (A j) :=
    compactFor_of_isGE_of_isLE hk aX hC _ N m fun j ↦
      ⟨_root_.DerivedCategory.homologyProperty_truncGE (hA j) N, inferInstance, inferInstance⟩
  have hcA : CompactFor C A := by
    refine CompactFor.of_bijective (fun j ↦ (t.truncGEπ N).app (A j)) hT (fun j ↦ ?_) ?_
    · have h := hN' _ (hLT j) inferInstance
      exact (bijective_comp_mor₂ _ (t.triangleLTGE_distinguished N (A j)) C h.1 h.2).2
    · have h := hN' _ (etaleOriginHomology_sigma Λ X _ hLT)
        (_root_.DerivedCategory.isLE_sigma _ _ fun j ↦ inferInstance)
      exact (bijective_comp_mor₂ _ (coproductTriangle_distinguished _
        fun j ↦ t.triangleLTGE_distinguished N (A j)) C h.1 h.2).1
  refine CompactFor.of_surjective (fun j ↦ (t.truncLEι m).app (Y j)) hcA ?_
  have hGT : (∐ fun j ↦ (t.truncGT m).obj (Y j)).IsGE (m + 1) :=
    _root_.DerivedCategory.isGE_sigma _ _ fun j ↦ inferInstance
  have hGT' : ((∐ fun j ↦ (t.truncGT m).obj (Y j))⟦(-1 : ℤ)⟧).IsGE (m + 2) :=
    t.isGE_shift _ (m + 1) (-1) (m + 2) (by lia)
  have : C.IsLE m := t.isLE_of_le C b m (le_max_left _ _)
  exact (bijective_comp_mor₁ _ (coproductTriangle_distinguished _
    fun j ↦ t.triangleLEGT_distinguished m (Y j)) C
    (fun f ↦ t.zero_of_isLE_of_isGE f m (m + 1) (by lia) this hGT)
    (fun f ↦ t.zero_of_isLE_of_isGE f m (m + 2) (by lia) this hGT')).2

include hk aX in
/-- Blueprint `proposition-compactness-finite-coefficients--1`
(`proposition-compactness-finite-coefficients`): every object of `Dctf(X, Λ)` is compact in
`Loc(Dctf(X, Λ))`. -/
theorem isCompactObj_of_constructibleFiniteTor
    (C : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ)
      X).localizingClosure.FullSubcategory)
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C.obj) :
    BrownRepresentability.IsCompactObj C := by
  let L := (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure
  intro J Y c hc f
  have hc' : IsColimit (Cofan.mk c.pt.obj fun j ↦ (c.inj j).hom) :=
    isColimitCofanMkObjOfIsColimit L.ι Y c.inj
      (hc.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp)))
  obtain ⟨S, g, hg⟩ := (compactFor_of_etaleOriginHomology hk aX hC (fun j ↦ (Y j).obj)
    fun j ↦ localizingClosure_constructibleFiniteTor_le Λ X _ (Y j).property).of_isColimit hc' f.hom
  refine ⟨S, fun j ↦ ObjectProperty.homMk (g j), ?_⟩
  apply L.ι.map_injective
  rw [Functor.map_sum]
  simpa using hg

end DerivedCategory

end AlgebraicGeometry.ProEtale
