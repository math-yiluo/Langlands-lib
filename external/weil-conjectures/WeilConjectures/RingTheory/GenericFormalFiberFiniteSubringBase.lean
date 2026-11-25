/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FormalFibreQuasiFiniteAscent
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
@[expose] public section
universe u
/-- Generic formal-fibre regularity over the canonical generic residue field, obtained by
applying quasi-finite formal-fibre ascent to a finite subring.
Source: Stacks Project, More on Algebra, Proposition 07PS and Lemma 07PP.
(blueprint: lem-weil-pbc-generic-formal-fibre-finite-subring-base).
Proof: Apply the quasi-finite formal-fibre ascent theorem to the finite subring inclusion
and the zero prime contained in P. -/
theorem genericFormalFiber_bot_geometricallyRegular_of_finite_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (A₀ : Subring A) [IsNoetherianRing A₀] [Module.Finite A₀ A]
    (P : Ideal A) [P.IsPrime]
    (hbase :
      let P₀ := P.comap (algebraMap A₀ A)
      let C₀ := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P₀))
        (Localization.AtPrime P₀)
      Algebra.IsGeometricallyRegular (⊥ : Ideal A₀).ResidueField
        ((⊥ : Ideal A₀).Fiber C₀)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber C) := by
  obtain ⟨hft, hqf⟩ := Algebra.finiteType_and_isQuasiFiniteAtPrime_of_finite A₀ A
  let _ := hft
  have hinj : Function.Injective (algebraMap A₀ A) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hzero : (⊥ : Ideal A).comap (algebraMap A₀ A) = ⊥ :=
    Ideal.comap_bot_of_injective _ hinj
  have h := RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime
    (R := A₀) (R' := A) (q' := (⊥ : Ideal A)) (p' := P) bot_le
    (hqf ⟨P, inferInstance⟩) (by
      let C₀ := AdicCompletion (IsLocalRing.maximalIdeal
        (Localization.AtPrime (P.comap (algebraMap A₀ A))))
        (Localization.AtPrime (P.comap (algebraMap A₀ A)))
      let q : {I : Ideal A₀ // I.IsPrime} :=
        ⟨(⊥ : Ideal A).comap (algebraMap A₀ A), inferInstance⟩
      let q₀ : {I : Ideal A₀ // I.IsPrime} := ⟨⊥, inferInstance⟩
      have hq : q = q₀ := Subtype.ext hzero
      let F : {I : Ideal A₀ // I.IsPrime} → Prop := fun I ↦
        letI := I.2
        Algebra.IsGeometricallyRegular I.1.ResidueField (I.1.Fiber C₀)
      have hF : F q = F q₀ := congrArg F hq
      have hbaseF : F q₀ := by
        simpa [F, q₀, C₀] using hbase
      change F q
      exact hF ▸ hbaseF)
  simpa [hzero] using h
