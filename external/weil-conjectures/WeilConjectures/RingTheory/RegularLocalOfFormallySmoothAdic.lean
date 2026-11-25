/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.FormallySmoothAdicCompletion
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.FormallySmoothAdicPowerSeriesMap

/-!
# Adically formally smooth local algebras over fields are regular

Source: Stacks Project, More on Algebra, Lemma Tag 07EI (lemma-fs-implies-regular)
(blueprint: lem-weil-pbc-fs-adic-field-regular-local).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A Noetherian local algebra over a field, formally smooth for the maximal-ideal-adic
 topology, is a regular local ring. Source: Stacks Project, More on Algebra, Tag 07EI
(blueprint: lem-weil-pbc-fs-adic-field-regular-local).

Proof (the six steps of the blueprint node):
1. Reduce to the prime field using lem-weil-pbc-char-zero-field-extension-formally-smooth
   or lem-weil-pbc-field-char-p-nilpotent-lifting. Lift the field map first and then the
   algebra map by theorem-finite-etale-covers-proper-henselian--2. If the original map kills m^q,
   the lift kills m^(2q), because the obstruction ideal is square-zero.
2. Pass to the maximal-ideal-adic completion using def-weil-pbc-adic-completion,
   lem-weil-pbc-adic-completion-noetherian and lem-weil-pbc-fs-adic-completion.
   Regularity descends by lem-weil-pbc-completion-regular-local.
3. Use lem-weil-pbc-cohen-coefficient-ring-exists to choose a coefficient field K.
   Choose a basis x_i of m/m^2, and form T = K[[X_1,...,X_n]] using
   def-weil-pbc-multivariate-power-series. The ring T is complete regular local of
   dimension n by lem-weil-pbc-power-series-field-cohen-regular-complete.
   Sending x_i to X_i identifies A/m^2 with T/n^2 as K-algebras.
4. Starting with A → T/n^2, lift successively through the square-zero kernels of
   T/n^(r+2) → T/n^(r+1) using theorem-finite-etale-covers-proper-henselian--2.
   Each map kills a power of m. Completeness of T gives a local prime-field-algebra
   map f : A → T; these lifts need not be K-linear.
5. By lem-weil-pbc-nakayama-local-generators, the f(x_i) generate n.
   Approximate every t in T degree by degree with polynomials in the f(x_i), lifting
   coefficients to A. The corrections in m^r converge in complete A. Separatedness
   of T gives f(a) = t, so f is surjective.
6. Pullback of prime chains gives dim A ≥ dim T = n. Nakayama says that the x_i
   generate m, so lem-weil-pbc-noetherian-local-dimension-le-generators gives dim A ≤ n.
   Therefore dim A = n, proving regularity by def-weil-regular-scheme. Step 2 then
   gives regularity of the original A. -/
theorem isRegularLocalRing_of_formallySmoothAdic (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] [IsLocalRing A]
    (h : FormallySmoothAdic k A (IsLocalRing.maximalIdeal A)) : IsRegularLocalRing A := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing _
  have hB : FormallySmoothAdic k B (IsLocalRing.maximalIdeal B) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact h.adicCompletion k A _ (Ideal.fg_of_isNoetherianRing _)
  apply (AdicCompletion.isRegularLocalRing_iff A).mpr
  obtain ⟨f, hmax, hres⟩ :=
    exists_powerSeries_comparison_of_formallySmoothAdic k B hB
  let K := IsLocalRing.ResidueField B
  let d := (IsLocalRing.maximalIdeal B).spanFinrank
  let T := MvPowerSeries (Fin d) K
  have hK : IsField K := Field.toIsField K
  rcases MvPowerSeries.power_series_field_cohen_regular_complete d (Or.inl hK) with
    ⟨_, hnoeth, hdomain, hlocal, hvars, e, he, hcomplete, _, hdim⟩ | ⟨p, hp, _⟩
  · let : IsNoetherianRing T := hnoeth
    let : IsLocalRing T := hlocal
    let : IsAdicComplete (IsLocalRing.maximalIdeal T) T := hcomplete
    have hmap : Ideal.map f (IsLocalRing.maximalIdeal B) =
        IsLocalRing.maximalIdeal T := hmax.trans hvars.symm
    have : IsHausdorff (Ideal.map f (IsLocalRing.maximalIdeal B)) T := by
      rw [hmap]
      infer_instance
    have hf : Function.Surjective f :=
      surjective_of_mk_map_comp_surjective (I := IsLocalRing.maximalIdeal B) f hres
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    calc
      ((IsLocalRing.maximalIdeal B).spanFinrank : WithBot ℕ∞) = ringKrullDim T :=
        hdim.symm
      _ ≤ ringKrullDim B := ringKrullDim_le_of_surjective f hf
  · obtain ⟨_, hdomain, hdvr, _⟩ := hp
    let := hdomain
    let := hdvr
    exact False.elim (IsDiscreteValuationRing.not_isField K hK)

end Algebra
