/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.FlatPointNoetherianModel
import WeilConjectures.RingTheory.FlatLocalizedModuleBaseChange
import WeilConjectures.Mathlib.RingTheory.Flat.Localization

/-!
# Openness of the flat locus of a finitely presented module

Source: Stacks Project, Algebra, Theorem 10.129.4 (Tag 00RC)
(blueprint: lem-weil-pbc-openness-of-flatness).
-/

@[expose] public section

universe u v w

namespace Module

/-- Stacks Project, Algebra, Theorem 10.129.4 (Tag 00RC)
(blueprint: lem-weil-pbc-openness-of-flatness). For a finitely presented algebra `S` over `R`
and a finitely presented `S`-module `M`, the primes where `M_q` is flat over `R` form an open
subset of the Zariski spectrum of `S`. The scalar tower identifies the `R`-action with
restriction along the ring map represented by `Algebra R S`.

Proof:
1. Fix a prime `q` in the flat locus and let `p` be its inverse image in `R`.
   By `lem-weil-pbc-limit-module-finite-presentation` (Stacks 00R1), express `(R,S,M)` as
   the directed limit of finite-type integer models `(R_i,S_i,M_i)` with the specified
   base-change isomorphisms. Their rings are Noetherian by
   `def-weil-pbc-noetherian-ring` and `lem-weil-pbc-finite-type-algebra-noetherian`.
   The prime localizations have local transition maps by
   `lemma-quasi-finite-coordinates--1`, and each localized module is finite.
2. The colimits of these prime localizations are `R_p`, `S_q`, and `M_q`.
   For the module, representatives of fractions come from a common stage, and a fraction
   that vanishes is killed at a later stage, using `def-weil-directed-colimit-abelian-groups`.
   The base-change isomorphisms, `lem-weil-pbc-localization-tensor-product`, and
   `lem-weil-pbc-localization-tensor-over-base` verify the hypotheses of
   `lem-weil-pbc-colimit-eventually-flat` (Stacks 00R6). Flatness over `R_p` is equivalent
   to flatness over `R` by `lem-weil-pbc-flat-over-localization`. Thus at some stage `i`,
   `(M_i)_{q_i}` is flat over `R_i`.
3. Apply `lem-weil-pbc-noetherian-flat-locus-neighborhood` to this Noetherian model.
   It gives `g_i` outside `q_i` such that every prime avoiding `g_i` has a localization
   flat over `R_i`. Its image `g` in `S` lies outside `q`.
4. For a prime `r` avoiding `g`, its inverse image `r_i` avoids `g_i`.
   Base change makes `(M_i)_{r_i}` tensor `R` flat over `R` by
   `lem-weil-pbc-flat-module-base-change`. The base-change isomorphisms and
   `lem-weil-pbc-localization-tensor-over-base` identify `M_r` with a further localization
   of this module. Localization preserves tensor-injectivity by
   `lem-weil-pbc-localization-module-exact`, so `M_r` is flat by
   `def-weil-pbc-flat-ring-map`. Hence the basic open `D(g)` lies in the flat locus.
   These neighborhoods cover it, and are open by `def-weil-affine-spectrum`. -/
theorem isOpen_setOf_flat_localizedModule {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S M] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q (hq : Module.Flat R _)
  obtain ⟨A, B, N, hA, hB, hAB, hAR, hBS, hAS, hABS, hARS,
    hN, hAN, hBN, hABN, hnoeth, hft, hfin, hpush, ⟨e⟩, hflat⟩ :=
    exists_noetherian_model_flat_at_prime q hq
  let p : Ideal B := q.asIdeal.comap (algebraMap B S)
  have hp : p.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨g, hg, hneighborhood⟩ :=
    Flat.exists_notMem_forall_flat_localizedModule (R := A) (M := N) p hflat
  refine ⟨PrimeSpectrum.basicOpen (algebraMap B S g), ?_,
    PrimeSpectrum.isOpen_basicOpen, hg⟩
  intro r hr
  exact Flat.localizedModule_of_isPushout e r
    (hneighborhood (r.asIdeal.comap (algebraMap B S)) hr)

end Module
