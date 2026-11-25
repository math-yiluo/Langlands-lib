/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.CompleteLocalMapRegularPresentation

/-!
# Flat presentations of maps of complete Noetherian local rings

Source: Stacks Project, More on Algebra, Lemma 15.40.3 (Tag 07NN), its flat-presentation
consequence (blueprint: lem-weil-pbc-complete-local-flat-presentation).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local map of complete Noetherian local rings admits a commutative square with
surjective vertical maps and a flat upper map between complete Noetherian local rings.
Source: Stacks Project, More on Algebra, Lemma 15.40.3 (Tag 07NN).
(blueprint: lem-weil-pbc-complete-local-flat-presentation)

Proof outline, following the six steps of the blueprint node:
1. The residue fields of `A` and `B` have the same characteristic. Choose Cohen power-series
   surjections `q : R → A` and `b : S₀ → B` using
   `lem-weil-pbc-cohen-structure-power-series-surjection`. The rings are Noetherian, regular,
   local and complete by `lem-weil-pbc-power-series-field-cohen-regular-complete`.
   Surjections between local rings are local and map maximal ideals onto maximal ideals.
2. The kernel of `b` is closed: its sums with powers of the maximal ideal are the inverse
   images of those powers in `B`, whose intersection is zero by completeness.
   Lift `f.comp q` to a local map `g : R → S₀` by
   `lem-weil-pbc-power-series-cohen-formally-smooth-adic` and
   `lem-weil-pbc-fs-adic-lift-into-complete` (over the rationals in residue characteristic
   zero, and over the integers otherwise).
3. Adjoin variables `yᵢ` to `S₀`, obtaining `S`, and send them to zero in `B`, using
   `lem-weil-pbc-power-series-quotient-variables`. Replace the image of each parameter `xᵢ`
   of `R` by `g(xᵢ) + yᵢ`, using
   `lem-weil-pbc-power-series-universal-property-complete`. This map is local; `S` is
   Noetherian and complete by `lem-weil-pbc-power-series-field-cohen-regular-complete`.
4. The square commutes on coefficients and parameters, hence on every series by the
   uniqueness in `lem-weil-pbc-power-series-universal-property-complete`.
5. The images of the parameters of `R`, together with the remaining parameters of `S₀`,
   generate the maximal ideal of `S` and form a regular sequence by
   `lem-weil-pbc-regular-local-generators-regular-sequence`. Their initial segment is still
   regular, so `lem-weil-pbc-flat-over-regular` makes the upper map flat.
6. Collect the Noetherian, local and completeness properties, the two surjections,
   the locality of all maps, flatness, and the equality of composites. -/
theorem exists_completeLocal_flat_presentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (R S : Type (max u v)) (rR : CommRing R) (rS : CommRing S),
      letI := rR
      letI := rS
      ∃ (lR : IsLocalRing R) (lS : IsLocalRing S),
        letI := lR
        letI := lS
        IsNoetherianRing R ∧ IsNoetherianRing S ∧
        IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
        IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
        ∃ (g : R →+* S) (q : R →+* A) (b : S →+* B),
          IsLocalHom g ∧ IsLocalHom q ∧ IsLocalHom b ∧
          Function.Surjective q ∧ Function.Surjective b ∧
          g.Flat ∧ b.comp g = f.comp q := by
  obtain ⟨R, S, rR, rS, hR, hS, hcR, hcS, q, b, g,
    hq, hlq, hb, hlb, hlg, hcomm, _, _, hflat, _⟩ :=
    exists_complete_local_map_regular_presentation f
  let := rR
  let := rS
  let := hR
  let := hS
  exact ⟨R, S, rR, rS, inferInstance, inferInstance,
    inferInstance, inferInstance, hcR, hcS, g, q, b,
    hlg, hlq, hlb, hq, hb, hflat, hcomm⟩

end RingHom
