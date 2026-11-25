/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.RingTheory.FlatUnderRegular

/-!
# Regularity descends along faithfully flat ring maps

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 07NG
(blueprint: lem-weil-pbc-regular-ring-faithfully-flat-descent).
-/

@[expose] public section

universe u v

namespace IsRegularRing

/--
If a homomorphism of commutative rings `R → S` (the structure map of `[Algebra R S]`) is
faithfully flat and its target is regular, then its source is regular, hence Noetherian.
Source: Stacks Project, Algebra, Lemma Tag 07NG
(blueprint: lem-weil-pbc-regular-ring-faithfully-flat-descent).

Proof, following the five steps of the blueprint node: (1) `S` is Noetherian by
`def-weil-regular-scheme`, and faithful-flat Noetherian descent is
`lem-weil-pbc-faithfully-flat-descent-noetherian`, so `R` is Noetherian. (2) For a
prime `p` of `R`, surjectivity of the spectrum map from faithful flatness gives a
prime `q` of `S` over `p`, by `lem-weil-pbc-faithfully-flat-surjective-spectrum`.
(3) The induced map `R_p → S_q` is a flat local map of Noetherian local rings by
`lem-weil-pbc-flat-local-ring-maps`, using `def-weil-pbc-localization-at-prime`.
(4) Since `S_q` is regular by `def-weil-regular-scheme`,
`theorem-finite-etale-covers-proper-henselian--2` gives that `R_p` is regular. (5) Since `p` was
arbitrary, `R` is regular by `def-weil-regular-scheme`; its Noetherianity is the
parent field of `IsRegularRing`.
-/
theorem of_faithfullyFlat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsRegularRing S] :
    IsRegularRing R := by
  have : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := R) (A := S) (M := R)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R S S).symm.toLinearEquiv)
  refine ⟨fun p hp ↦ ?_⟩
  obtain ⟨q, hq⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S) ⟨p, hp⟩
  have hpq : p = Ideal.comap (algebraMap R S) q.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  exact IsRegularLocalRing.of_ringHom_flat
    (Localization.localRingHom p q.asIdeal (algebraMap R S) hpq)
    ((RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).localRingHom
      q.asIdeal p hpq)

end IsRegularRing
