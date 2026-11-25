/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.RingTheory.StrictHenselizationCompletionNoetherian
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity and strict henselization

Source: Stacks Project, More on Algebra, Lemma 15.46.3 (Tag 06LJ), conditions (1) and (3)
(blueprint: lem-sc-strict-henselization-noetherian).
-/

@[expose] public section

universe u

namespace Algebra

/-- For a local commutative ring, Noetherianity is equivalent to Noetherianity of its
strict henselization relative to a chosen separable closure of its residue field.
Source: Stacks Project, More on Algebra, Lemma 15.46.3 (Tag 06LJ), conditions (1) and (3).

Proof: The map from the base ring to its strict henselization is faithfully flat, so
Noetherianity descends. Conversely, when the base is Noetherian, the completion of the
strict henselization is Noetherian and faithfully flat over it; faithfully flat descent
then gives Noetherianity of the strict henselization. These are the three proof steps
recorded in the blueprint (lem-sc-strict-henselization-faithfully-flat,
lem-weil-pbc-faithfully-flat-descent-noetherian, and
lem-sc-strict-henselization-completion-noetherian).
(blueprint: lem-sc-strict-henselization-noetherian). -/
theorem isNoetherianRing_iff_isStrictHenselization
    (R K C : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C] (hC : IsStrictHenselization R K C) :
    IsNoetherianRing R ↔ IsNoetherianRing C := by
  constructor
  · intro hR
    have := hR
    obtain ⟨hn, _, hf⟩ := strictHenselization_completion_noetherian_faithfullyFlat R K C hC
    let D := AdicCompletion ((IsLocalRing.maximalIdeal R).map (algebraMap R C)) C
    have : IsNoetherianRing D := hn
    have : Module.FaithfullyFlat C D := hf
    exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := C) (A := D) (M := C)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid C D D).symm.toLinearEquiv)
  · intro hCnoeth
    have := hCnoeth
    obtain ⟨p, hp, a, hs, ι, ⟨hc⟩, hρ⟩ := hC.triples_presentation R K C
    let := a
    have := hs
    have hflat := AlgebraicGeometry.Scheme.strictHenselization_faithfullyFlat
      (CommRingCat.of R) p hp K (CategoryTheory.Limits.Cocone.mk (CommRingCat.of C) ι)
      hc (CommRingCat.ofHom (algebraMap R C)) hρ
    have : Module.FaithfullyFlat R C :=
      (RingHom.faithfullyFlat_algebraMap_iff).mp hflat
    exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := R) (A := C) (M := R)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R C C).symm.toLinearEquiv)

end Algebra
