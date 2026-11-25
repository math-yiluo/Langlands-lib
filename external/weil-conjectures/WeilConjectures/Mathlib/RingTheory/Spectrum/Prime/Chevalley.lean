/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Chevalley's theorem for finitely generated algebras over a field

A morphism between spectra of finitely generated algebras over a field is of finite presentation,
so it maps constructible sets to constructible sets.

## Main results

- `PrimeSpectrum.isConstructible_comap_image_of_finiteType`

## Blueprint

- `lem-wf-affine-constructible-open`, clause (1): Chevalley constructibility.
-/

@[expose] public section

open Topology

namespace PrimeSpectrum

/-- Blueprint `lem-wf-affine-constructible-open`, clause (1) (Chevalley): for a `k`-algebra map
`f : A →ₐ[k] B` between finitely generated algebras over a field `k`, the image of a constructible
subset of `Spec B` in `Spec A` is constructible.

The map `f` is of finite type, hence of finite presentation as `A` is Noetherian, and Chevalley's
theorem `PrimeSpectrum.isConstructible_comap_image` applies. -/
theorem isConstructible_comap_image_of_finiteType {k A B : Type*} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) {s : Set (PrimeSpectrum B)} (hs : IsConstructible s) :
    IsConstructible (comap f.toRingHom '' s) := by
  have := Algebra.FiniteType.isNoetherianRing k A
  have hB : (f.toRingHom.comp (algebraMap k A)).FiniteType := by
    rw [show f.toRingHom.comp (algebraMap k A) = algebraMap k B from f.comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact isConstructible_comap_image
    (RingHom.FinitePresentation.of_finiteType.mp (RingHom.FiniteType.of_comp_finiteType hB)) hs

end PrimeSpectrum
