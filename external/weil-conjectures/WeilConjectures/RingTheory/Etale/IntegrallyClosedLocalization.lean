/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.IntegrallyClosed
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Normality ascends along étale ring maps, pointwise

Let `A` be an étale `R`-algebra and `P` a prime of `A` lying over a prime `p` of `R` such that
`R_p` is an integrally closed domain. Then `A_P` is an integrally closed domain (Stacks `033C`,
étale case). No hypothesis on `R` itself is needed: `A_P` is a localization of the étale
`R_p`-algebra `R_p ⊗[R] A`, to which
`Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization` applies.
-/

@[expose] public section

universe u

open TensorProduct

/-- **Normality ascends along étale ring maps** (Stacks `033C`, étale case). Let `A` be an étale
`R`-algebra and `P` a prime of `A` such that the localization of `R` at `p = P ∩ R` is an
integrally closed domain. Then the localization `A_P` is an integrally closed domain. -/
theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_localization_of_comap {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A] (P : Ideal A) [P.IsPrime]
    (hP : IsDomain (Localization.AtPrime (P.comap (algebraMap R A))) ∧
      IsIntegrallyClosed (Localization.AtPrime (P.comap (algebraMap R A)))) :
    IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) := by
  set p := P.comap (algebraMap R A)
  obtain ⟨_, _⟩ := hP
  let Rp := Localization.AtPrime p
  let A' := Rp ⊗[R] A
  let : Algebra A A' := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid A p.primeCompl
  have : IsLocalization M A' := IsLocalization.tensorRight Rp p.primeCompl
  have hd : Disjoint (M : Set A) P := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨r, hr, rfl⟩ hrP
    exact hr hrP
  let P' := P.map (algebraMap A A')
  have : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A' P inferInstance hd
  have hc : P'.comap (algebraMap A A') = P :=
    IsLocalization.under_map_of_isPrime_disjoint M A' inferInstance hd
  have : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime P') P'
    convert this
    exact hc.symm
  obtain ⟨h₁, h₂⟩ := Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization (R := Rp)
    (B := A') P' (Localization.AtPrime P')
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (Localization.AtPrime P')
  exact ⟨e.toMulEquiv.isDomain _,
    .of_equiv e.toRingEquiv.symm⟩
