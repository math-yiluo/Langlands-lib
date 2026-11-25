/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.AdjoinSingletonAssociatedContraction
import WeilConjectures.RingTheory.FractionalPrincipalQuotientAssociatedPrimesHeight
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Associated localizations of a fractional monogenic algebra

Source: Stacks Project, Algebra, Tag 0334, Step 5, the comparison with a height-one
localization of the normal base domain.
(blueprint: lem-weil-pbc-monogenic-associated-localization).
-/

@[expose] public section

universe u v

/-- An associated-prime localization of the principal quotient of a fractional monogenic
algebra is isomorphic to a height-one localization of the normal base domain.
No Nagata hypothesis is needed for this comparison.

Source: Stacks Project, Algebra, Tag 0334, Step 5, the paragraphs verifying (2) and (3)(a),
using Tags 00PQ, 031T and 00PD.
(blueprint: lem-weil-pbc-monogenic-associated-localization).

Proof:
1. Put `S = R[x]`, contract `p` to `qS` in `S`, and contract again to `q` in `R`.
   The associated-contraction theorem identifies `q` as associated to `R/J`,
   where `J = R ∩ xR`. Its proof identifies `S/xS ≃ R/J` by adjoin induction
   and the reversed-polynomial integrality argument.
2. Tag 031T gives `q.height = 1`. Normality localizes, so `B = R_q` is a
   one-dimensional normal Noetherian local domain, hence a DVR by Tag 00PD.
3. Put `C = S_qS`. There is a local map `f : B → C` from the contracted primes.
   Embed `C` into `Frac(R)` by extending the inclusion `S ⊆ K` along the
   canonical identification `K ≃ Frac(R)`. Every denominator is nonzero,
   so this extension `g` is injective; its composite with `f` is the fraction
   field inclusion of `B`. A valuation ring is maximal among local subrings
   of its fraction field dominating it. Mathlib's
   `bijective_rangeRestrict_comp_of_valuationRing` therefore makes the map
   `B → range(g)` bijective. Injectivity of `g` gives `B ≃ C`.
4. Since `qS ≤ m` and `p` is its extension to `S_m`, iterated localization gives
   `A_p ≃ S_qS`. Compose with the isomorphism in step 3.
   If `x` becomes a unit in `S_m`, the principal quotient is zero and there are
   no associated primes, so the assertion is vacuous. -/
theorem adjoin_singleton_associated_localization
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K) (hx0 : x ≠ 0)
    [IsNoetherianRing (Algebra.adjoin R ({x} : Set K))]
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hx : (⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩ :
      Algebra.adjoin R ({x} : Set K)) ∈ m)
    (p : associatedPrimes (Localization.AtPrime m)
      (Localization.AtPrime m ⧸ Ideal.span
        {algebraMap (Algebra.adjoin R ({x} : Set K)) (Localization.AtPrime m)
          ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩})) :
    ∃ (q : Ideal R) (_ : q.IsPrime), q.height = 1 ∧
      Nonempty (Localization.AtPrime p.1 ≃+* Localization.AtPrime q) := by
  let S := Algebra.adjoin R ({x} : Set K)
  let qS : Ideal S := p.1.under S
  let q : Ideal R := qS.under R
  have hqass := adjoin_singleton_associated_contraction R K x hx0 m hx p
  have hheight : q.height = 1 :=
    Ideal.associatedPrimes_fractionalPrincipalQuotient_height R K x hx0 q hqass
  let : qS.IsPrime := inferInstance
  let : q.IsPrime := inferInstance
  let B := Localization.AtPrime q
  let C := Localization.AtPrime qS
  have hdim : ringKrullDim B = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hheight]
    rfl
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsRegularLocalRing B := IsRegularLocalRing.of_isIntegrallyClosed B hdim.le
  let : IsDiscreteValuationRing B := IsRegularLocalRing.isDiscreteValuationRing B hdim
  let f : B →+* C := Localization.localRingHom q qS (algebraMap R S) rfl
  let eK : K ≃ₐ[R] FractionRing R :=
    IsLocalization.algEquiv (nonZeroDivisors R) K (FractionRing R)
  let gS : S →+* FractionRing R := eK.toRingHom.comp S.val.toRingHom
  have hgS : Function.Injective gS := eK.injective.comp Subtype.val_injective
  have hu (s : qS.primeCompl) : IsUnit (gS s) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hs : (s : S) = 0 := hgS (by simpa only [map_zero] using h)
    exact s.2 (hs ▸ qS.zero_mem)
  let g : C →+* FractionRing R := IsLocalization.lift hu
  have hg : Function.Injective g := by
    apply (IsLocalization.lift_injective_iff hu).mpr
    intro a b
    constructor
    · intro h
      have he := congrArg g h
      change (IsLocalization.lift hu) ((algebraMap S C) a) =
        (IsLocalization.lift hu) ((algebraMap S C) b) at he
      simpa only [IsLocalization.lift_eq] using he
    · intro h
      exact congrArg (algebraMap S C) (hgS h)
  have hcomp : g.comp f = algebraMap B (FractionRing R) := by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext r
    change (IsLocalization.lift hu)
      ((Localization.localRingHom q qS (algebraMap R S) rfl) ((algebraMap R B) r)) = _
    rw [Localization.localRingHom_to_map, IsLocalization.lift_eq]
    change eK (algebraMap R K r) = _
    rw [eK.commutes]
    exact congrArg (fun h : R →+* FractionRing R ↦ h r)
      (IsScalarTower.algebraMap_eq R B (FractionRing R))
  have hbij : Function.Bijective (g.rangeRestrict.comp f) :=
    bijective_rangeRestrict_comp_of_valuationRing f g hcomp
  have hfsurj : Function.Surjective f := by
    intro c
    obtain ⟨b, hb⟩ := hbij.2 (g.rangeRestrict c)
    exact ⟨b, hg (congrArg Subtype.val hb)⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    exact hbij.1 (congrArg g.rangeRestrict hab)
  let e : B ≃+* C := RingEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let ei := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    m.primeCompl p.1
  exact ⟨q, inferInstance, hheight, ⟨ei.toRingEquiv.symm.trans e.symm⟩⟩

