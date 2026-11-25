/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.StrictHenselizationCotangentDimension
import WeilConjectures.RingTheory.StrictHenselizationDimension
import WeilConjectures.RingTheory.StrictHenselizationNoetherian

/-!
# Regularity and strict henselization

Source: Stacks Project, More on Algebra, Lemma 15.46.10 (Tag 06LN), the equivalence
of its first and third conditions (blueprint: lem-sc-strict-henselization-regular).
-/

@[expose] public section

universe v

namespace Algebra

/-- A Noetherian local ring is regular exactly when its strict henselization is regular.
Here `C` is the strict henselization of `R` with respect to the separable closure `K` of
the residue field of `R`.
Source: Stacks Project, More on Algebra, Lemma 15.46.10 (Tag 06LN).

Proof: `lem-sc-strict-henselization-noetherian` makes the strict henselization Noetherian.
By `lem-sc-strict-henselization-dimension`, the two rings have equal Krull dimension.
By `lem-sc-strict-henselization-cotangent-dimension`, extension of the residue field
identifies the cotangent spaces and preserves their dimensions. Apply
`lem-weil-pbc-regular-local-cotangent-dimension` to both Noetherian local rings:
regularity is equality of cotangent-space dimension and Krull dimension. The two
comparisons therefore give the equivalence.
(blueprint: lem-sc-strict-henselization-regular). -/
theorem isRegularLocalRing_iff_strictHenselization
    (R K C : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    IsRegularLocalRing R ↔ IsRegularLocalRing C := by
  have : IsNoetherianRing C :=
    (isNoetherianRing_iff_isStrictHenselization R K C hC).mp inferInstance
  obtain ⟨hlocal, _, hcotangent⟩ :=
    finrank_cotangentSpace_eq_of_isStrictHenselization R K C hC
  have : IsLocalRing C := hlocal
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace R,
    IsRegularLocalRing.iff_finrank_cotangentSpace C, hcotangent,
    ringKrullDim_eq_of_isStrictHenselization R K C hC]

end Algebra
