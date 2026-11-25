/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.KrullDimension.GoingDown

/-!
# Faithfully flat local maps do not lower Krull dimension

Source: Stacks Project, Algebra, Tags 00OH, 00HS and 00HQ
(blueprint: lem-sc-faithfully-flat-local-dimension).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A faithfully flat local homomorphism of local commutative rings does not lower Krull
 dimension (Stacks Project, Algebra, Tags 00OH, 00HS and 00HQ).
(blueprint: lem-sc-faithfully-flat-local-dimension)

Proof:
1. Faithful flatness implies flatness, hence going down by Tag 00HS
   (`lem-sc-flat-going-down`).
2. Faithful flatness makes the map on prime spectra surjective by Tag 00HQ
   (`lem-weil-pbc-faithfully-flat-surjective-spectrum`).
3. Apply Tag 00OH (`lem-sc-going-down-surjective-dimension`): for any finite strict chain
   of primes in the source, lift its largest prime using surjectivity and lift each preceding
   prime using going down. The lifted inclusions are strict, since their contractions are
   strict. Taking the supremum of all chain lengths gives the dimension inequality, including
   the case of unbounded lengths. -/
theorem ringKrullDim_le_of_faithfullyFlat_of_isLocalHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : f.FaithfullyFlat) :
    ringKrullDim A ≤ ringKrullDim B := by
  let := f.toAlgebra
  have : Module.Flat A B := hf.flat
  exact ringKrullDim_le_of_goingDown_of_surjective f
    (Algebra.HasGoingDown.of_flat)
    (FaithfullyFlat.iff_flat_and_comap_surjective.mp hf).2

end RingHom
