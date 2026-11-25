/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.LocalProperties.Projective
public import WeilConjectures.Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Localizations of modules of finite projective dimension over a local ring

Let `R` be a noetherian local ring and `M` a finitely generated `R`-module of finite projective
dimension. Then `M` has a finite resolution by finite free modules, and hence so does every
localization `S⁻¹M`. If moreover `S⁻¹M` is projective over `S⁻¹R`, splitting this resolution shows
that `S⁻¹M` is stably free.

## Main results

- `Module.isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE`: if `R` is a noetherian
  local ring, `M` a finite `R`-module of finite projective dimension and `N` a localization of `M`
  at `S` which is projective over `Localization S`, then `N` is stably free.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- Let `R` be a noetherian local ring and `M` a finite `R`-module of projective dimension at most
`n`. If `N` is a localization of `M` at `S` which is projective over `Localization S`, then `N` is
stably free. The proof is by induction on `n`, localizing a presentation of `M` by a finite free
module and splitting the resulting short exact sequence. -/
theorem isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n →
      ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module (Localization S) N]
        [IsScalarTower R (Localization S) N] (f : M →ₗ[R] N) [IsLocalizedModule S f]
        [Projective (Localization S) N], IsStablyFree (Localization S) N := by
  induction n with
  | zero =>
    intro M _ _ _ hM N _ _ _ _ f _ _
    have : Projective R M := by
      rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
      exact hM
    have : Free R M := free_of_flat_of_isLocalRing
    have : Free (Localization S) N := free_of_isLocalizedModule S f
    infer_instance
  | succ n ih =>
    intro M _ _ _ hM N _ _ _ _ f _ _
    obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hex := LinearMap.exact_subtype_ker_map π
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero K.subtype π hex.linearMap_comp_eq_zero) hex
      K.injective_subtype hπ
    have : CategoryTheory.Projective (ModuleCat.of R (Fin k → R)) := by
      rw [← IsProjective.iff_projective]
      infer_instance
    have hK : HasProjectiveDimensionLE (ModuleCat.of R K) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n this).1 hM
    let fK := LocalizedModule.mkLinearMap S K
    let fF := LocalizedModule.mkLinearMap S (Fin k → R)
    have : Free (Localization S) (LocalizedModule S (Fin k → R)) := free_of_isLocalizedModule S fF
    have : Module.Finite (Localization S) (LocalizedModule S (Fin k → R)) :=
      .of_isLocalizedModule S fF
    let i := (IsLocalizedModule.map S fK fF K.subtype).extendScalarsOfIsLocalization S
      (Localization S)
    let p := (IsLocalizedModule.map S fF f π).extendScalarsOfIsLocalization S (Localization S)
    have hi : Function.Injective i := IsLocalizedModule.map_injective S fK fF _ K.injective_subtype
    have hp : Function.Surjective p := IsLocalizedModule.map_surjective S fF f _ hπ
    have hip : Function.Exact i p := IsLocalizedModule.map_exact S fK fF f _ _ hex
    have : Projective (Localization S) (LocalizedModule S K) :=
      .of_exact_of_projective hi hp hip
    have := ih K hK (LocalizedModule S K) fK
    exact .of_exact hi hp hip

end Module
