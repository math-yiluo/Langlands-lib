/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdjoinSingletonFiniteCoverCore
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# A finite cover of a maximal localization of a fractional monogenic algebra

Source: Stacks Project, Algebra, Tag 0334, Step 5, residue-polynomial splitting reduction.
(blueprint: lem-weil-pbc-monogenic-maximal-finite-cover).
-/

@[expose] public section

universe u v

/-- Transport analytic unramifiedness along a local ring isomorphism. -/
private theorem unramified_of_equiv {C D : Type*} [CommRing C] [CommRing D]
    [IsLocalRing C] [IsLocalRing D] [IsNoetherianRing C] [IsNoetherianRing D]
    (e : C ≃+* D) (h : IsAnalyticallyUnramified D) : IsAnalyticallyUnramified C := by
  obtain ⟨E, _⟩ := AdicCompletion.exists_ringEquiv
    (IsLocalRing.maximalIdeal C) (IsLocalRing.maximalIdeal D) e
    (IsLocalRing.map_ringEquiv_maximalIdeal e).symm
  have : IsReduced (AdicCompletion (IsLocalRing.maximalIdeal D) D) := h
  exact isReduced_of_injective E.toRingHom E.injective

/-- The generator-in-maximal local calculation produces a finite domain cover whose
maximal localizations are analytically unramified and which has a normal principal open.
Source: Stacks Project, Algebra, Tag 0334, Step 5, lines 46137--46173 and the descent setup.
(blueprint: lem-weil-pbc-monogenic-maximal-finite-cover).

Proof:
1. Contract `m` to `n` in `R`. The residue field at `m` is monogenic of finite type over
   the residue field at `n`, hence finite by Tag 00FV. Lift its monic minimal polynomial
   to `R_n[T]`, clear the finitely many coefficient denominators by one element outside
   `n`, and work over `R_s`. Its evaluation at `x` lies in `m`.
2. Take a finite splitting field of the lifted polynomial over `K` and let `R'` be the
   integral closure of `R_s` in that field. Tags 032U and 032R make `R'` finite over `R_s`;
   it is normal and Nagata by integral-closure normality and Tag 032T. All roots lie in
   `R'` because the polynomial is monic. The algebra `S' = R'[x]` is finite over `R_s[x]`,
   using the module generators of `R'`.
3. Set `A = R[x]_m` and `B = (R[x] ∖ m)⁻¹S'`. The element `s` is already invertible in
   `A`, so `B` is a finite injective `A`-algebra and a Noetherian domain. Every maximal
   ideal of `B` corresponds to a maximal ideal `m'` of `S'` over `m`, by integrality.
   Factoring the lifted polynomial gives a root `r ∈ R'` with `x - r ∈ m'`.
   Since `R'[x] = R'[x-r]`, the supplied local calculation makes `S'_{m'}`, and hence
   that maximal localization of `B`, analytically unramified.
4. Write the original fraction `x = b/a`, `a ≠ 0`. After inverting its image in `B`,
   `R'[x]` becomes `R'_a`; further localization remains normal. The image of `a` is
   nonzero since all maps are injective. This supplies the required normal principal open.
   No N-1 assertion or finite-extension descent is part of this lemma. -/
theorem exists_finite_cover_adjoin_singleton_atPrime
    (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : IsNagataRing R) (x : K)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hLocal : ∀ (R' K' : Type (max u v)) [CommRing R'] [IsDomain R']
      [IsIntegrallyClosed R'] [IsNoetherianRing R'] [Field K'] [Algebra R' K']
      [IsFractionRing R' K'], IsNagataRing R' → ∀ (y : K')
      [IsNoetherianRing (Algebra.adjoin R' ({y} : Set K'))]
      (q : Ideal (Algebra.adjoin R' ({y} : Set K'))) [q.IsMaximal],
      (⟨y, Algebra.subset_adjoin (Set.mem_singleton y)⟩ :
        Algebra.adjoin R' ({y} : Set K')) ∈ q →
      IsAnalyticallyUnramified (Localization.AtPrime q)) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : IsDomain B)
      (_ : Algebra (Localization.AtPrime m) B) (_ : IsNoetherianRing B),
      Function.Injective (algebraMap (Localization.AtPrime m) B) ∧
      Module.Finite (Localization.AtPrime m) B ∧
      (∃ f : B, f ≠ 0 ∧ ∀ (p : Ideal (Localization.Away f)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      (∀ (q : Ideal B) [q.IsMaximal],
        IsAnalyticallyUnramified (Localization.AtPrime q))  := by
  obtain ⟨B, hBCR, hBDom, hBAlg, hBNoeth, hinj, hfin, hnormalB, hpresent⟩ :=
    exists_finite_cover_adjoin_singleton_core R K hR x m
  let : CommRing B := hBCR
  let : IsDomain B := hBDom
  let : Algebra (Localization.AtPrime m) B := hBAlg
  let : IsNoetherianRing B := hBNoeth
  refine ⟨B, hBCR, hBDom, hBAlg, hBNoeth, hinj, hfin, hnormalB, ?_⟩
  intro q hq
  obtain ⟨R', K', hCR, hDom, hNormal, hNoeth, hField, hAlg, hFrac,
    hNagata, y, hSNoeth, n, hn, hy, ⟨e⟩⟩ := hpresent q
  let : CommRing R' := hCR
  let : IsDomain R' := hDom
  let : IsIntegrallyClosed R' := hNormal
  let : IsNoetherianRing R' := hNoeth
  let : Field K' := hField
  let : Algebra R' K' := hAlg
  let : IsFractionRing R' K' := hFrac
  let : IsNoetherianRing (Algebra.adjoin R' ({y} : Set K')) := hSNoeth
  let : n.IsMaximal := hn
  exact unramified_of_equiv e (hLocal R' K' hNagata y n hy)

