/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Openness of a fixed projective-dimension bound

Source: Stacks Project, Algebra, Tag 00NX, and More on Algebra, Tag 068V.
(blueprint: lem-pc-projective-dimension-locus-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ModuleCat

/-- The locus of prime localizations of projective dimension at most n is open.
Source: Stacks Project, Algebra, Tag 00NX, and More on Algebra, Tag 068V.

Proof: Induct on n. At n = 0, projectivity is equivalent to freeness over the
local ring, so the locus is the free locus of a finitely presented module,
which is open. For n + 1 choose a finite free surjection onto M with finite
kernel K. Its localization is short exact at every prime. Since its middle
term is projective, dimension shifting identifies the projective-dimension
bound n + 1 for M with the bound n for K. The latter locus is open by the
induction hypothesis. No uniform dimension assumption on R is used, and
the zero module and zero ring satisfy the same induction.
(blueprint: lem-pc-projective-dimension-locus-open). -/
theorem isOpen_hasProjectiveDimensionLE_locus
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    IsOpen {p : PrimeSpectrum R |
      HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) n} := by
  induction n generalizing M with
  | zero =>
    have heq : {p : PrimeSpectrum R |
        HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) 0} =
        Module.freeLocus R M := by
      ext p
      rw [Module.mem_freeLocus_of_isLocalization p (Localization.AtPrime p.asIdeal)
        (M.localizedModule p.asIdeal.primeCompl) (M.localizedModuleMkLinearMap _)]
      change HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) 0 ↔ _
      rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective]
      have : Module.Finite (Localization.AtPrime p.asIdeal)
          (M.localizedModule p.asIdeal.primeCompl) :=
        Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
          (M.localizedModuleMkLinearMap _)
      exact ⟨fun h ↦ by
        have := h
        exact Module.free_of_flat_of_isLocalRing, fun h ↦ by
        let : Module.Free (Localization p.asIdeal.primeCompl)
            (M.localizedModule p.asIdeal.primeCompl) := h
        exact Module.Projective.of_free⟩
    rw [heq]
    have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    exact Module.isOpen_freeLocus
  | succ n ih =>
    rcases Module.exists_finite_presentation R M with ⟨P, _, _, _, _, f, hf⟩
    let S := f.shortComplexKer
    have hS := LinearMap.shortExact_shortComplexKer hf
    let Sp (p : PrimeSpectrum R) := S.map (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
    have hSp (p : PrimeSpectrum R) : (Sp p).ShortExact :=
      hS.map_of_exact (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl)
    have hproj (p : PrimeSpectrum R) : Projective (Sp p).X₂ :=
      (ModuleCat.localizedModuleFunctor p.asIdeal.primeCompl).projective_obj_of_projective
        (inferInstance : Projective S.X₂)
    have heq : {p : PrimeSpectrum R |
        HasProjectiveDimensionLE (M.localizedModule p.asIdeal.primeCompl) (n + 1)} =
        {p : PrimeSpectrum R |
          HasProjectiveDimensionLE ((ModuleCat.of R (LinearMap.ker f)).localizedModule
            p.asIdeal.primeCompl) n} := by
      ext p
      exact (hSp p).hasProjectiveDimensionLT_X₃_iff n (hproj p)
    rw [heq]
    exact ih (ModuleCat.of R (LinearMap.ker f))

end ModuleCat
