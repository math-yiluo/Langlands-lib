/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension

/-!
# Localization and finite global dimension

Source: Stacks Project, Algebra, Lemma 00O8
(blueprint: lem-weil-pbc-localization-finite-gl-dim).
-/

@[expose] public section

universe u v

namespace Ring

private theorem resolution_bound_of_iso
    {A : Type u} [CommRing A] {M N : ModuleCat.{max u v} A}
    (e : CategoryTheory.Iso M N) {n : ℕ} (h : ModuleCat.HasProjectiveResolutionLE M n) :
    ModuleCat.HasProjectiveResolutionLE N n := by
  obtain ⟨P, hP⟩ := h
  exact ⟨{ complex := P.complex
           projective := P.projective
           π := CategoryTheory.CategoryStruct.comp P.π
             ((ChainComplex.single₀ _).map e.hom) }, hP⟩

private theorem localized_resolution_bound
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ)
    (M : ModuleCat.{max u v} R) (h : ModuleCat.HasProjectiveResolutionLE M n) :
    ModuleCat.HasProjectiveResolutionLE
      (ModuleCat.of (Localization S) (LocalizedModule S M)) n := by
  obtain ⟨P, hP⟩ := h
  have hloc : ModuleCat.HasProjectiveResolutionLE (M.localizedModule S) n := by
    refine ⟨(ModuleCat.localizedModuleFunctor S).mapProjectiveResolution P, ?_⟩
    intro i hi
    exact (ModuleCat.localizedModuleFunctor S).map_isZero (hP i hi)
  exact resolution_bound_of_iso
    (Shrink.linearEquiv (Localization S) (LocalizedModule S M)).toModuleIso hloc

/-- Localization preserves bounds on projective resolution lengths and global dimension.
Source: Stacks Project, Algebra, Lemma 00O8
(blueprint: lem-weil-pbc-localization-finite-gl-dim).

Proof:
1. Localize a projective resolution term by term. Every three-term piece remains exact,
   including the end pieces, by `lem-weil-pbc-localization-module-exact` (Stacks 00CS).
2. Each localized term is projective by `lem-weil-pbc-localization-projective` (05A3).
   The resulting resolution has the same length, proving the first assertion.
3. Regard any module over the localized ring as an R-module and apply the first assertion.
   By `lem-weil-pbc-localization-module-over-localization`, its localization is isomorphic
   to itself. Composing the augmentation with this isomorphism gives the desired resolution,
   proving the uniform global dimension bound.
4. Apply that bound at the least bound for R. The least bound for the localization is no
   larger, proving finite global dimension and the inequality of global dimensions. -/
theorem localization_preserves_projective_and_global_dimension
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ) :
    (∀ M : ModuleCat.{max u v} R,
      ModuleCat.HasProjectiveResolutionLE M n →
        ModuleCat.HasProjectiveResolutionLE
          (ModuleCat.of (Localization S) (LocalizedModule S M)) n) ∧
    (HasGlobalDimensionLE.{u, max u v} R n →
      HasGlobalDimensionLE.{u, max u v} (Localization S) n) ∧
    (∀ h : HasFiniteGlobalDimension.{u, max u v} R,
      ∃ hS : HasFiniteGlobalDimension.{u, max u v} (Localization S),
        globalDimension.{u, max u v} (Localization S) hS ≤
          globalDimension.{u, max u v} R h) := by
  classical
  have hres := localized_resolution_bound R S n
  have hglobal (k : ℕ) (h : HasGlobalDimensionLE.{u, max u v} R k) :
      HasGlobalDimensionLE.{u, max u v} (Localization S) k := by
    intro M
    let : Module R M := Module.compHom M (algebraMap R (Localization S))
    let : IsScalarTower R (Localization S) M := IsScalarTower.of_algebraMap_smul
      (fun r m ↦ rfl)
    let MR := ModuleCat.of R M
    have hMR := localized_resolution_bound R S k MR
      ((ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE MR k).2 (h MR))
    let := isLocalizedModule_id S M (Localization S)
    exact (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE _ k).1
      (resolution_bound_of_iso
        ((IsLocalizedModule.iso S (LinearMap.id : M →ₗ[R] M)).extendScalarsOfIsLocalization
          S (Localization S)).toModuleIso hMR)
  refine ⟨hres, hglobal n, ?_⟩
  intro h
  have hb := hglobal (globalDimension R h) (Nat.find_spec h)
  let hS : HasFiniteGlobalDimension.{u, max u v} (Localization S) :=
    ⟨globalDimension R h, hb⟩
  exact ⟨hS, Nat.find_min' hS hb⟩

end Ring
