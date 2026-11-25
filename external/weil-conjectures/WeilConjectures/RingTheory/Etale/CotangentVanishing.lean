/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import Mathlib.RingTheory.Etale.Locus
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# An étale basic neighbourhood from vanishing of the naive cotangent complex

Source: Stacks Project, Algebra, Tags 07BU, 00TB, 00U1; Morphisms, Tag 02GJ;
More on Algebra, proof of Tag 07M7
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- For a finitely presented `A`-algebra `C`, vanishing at a prime `q` of both the first
homology of the naive cotangent complex and the Kähler differentials gives an étale
principal neighbourhood of `q` over `Spec A`.
Source: Stacks Project, Tags 07BU, 00TB, 00U1, 02GJ, and the proof of 07M7.
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem exists_etale_away_of_localization_cotangent_eq_zero
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.FinitePresentation A C] (q : Ideal C) [q.IsPrime]
    (hH : Subsingleton (LocalizedModule q.primeCompl (Algebra.H1Cotangent A C)))
    (hΩ : Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential A C))) :
    ∃ h : C, h ∉ q ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h)))) := by
  have hq : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈ Algebra.etaleLocus A C := by
    rw [Algebra.etaleLocus_eq_compl_support]
    exact ⟨Module.notMem_support_iff.mpr hΩ, Module.notMem_support_iff.mpr hH⟩
  have : Algebra.IsEtaleAt A q := hq
  obtain ⟨h, hh, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) q
  refine ⟨h, hh, ?_⟩
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact (RingHom.etale_algebraMap).mpr he

end AlgebraicGeometry
