/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.Algebra.PopescuLiftNilpotent
import WeilConjectures.RingTheory.PopescuParameterQuotientLocalFlatFiberData
import WeilConjectures.RingTheory.IndSmoothFinitePresentationFactorization
import WeilConjectures.RingTheory.PolynomialOriginRegularLocal
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.Algebra.Algebra.Shrink

@[expose] public section

universe u v w

namespace Algebra

-- In the powered polynomial quotient every prime is the nilradical. Its localized
-- maximal ideal is consequently nilpotent (Stacks 07FE, powered-parameter reduction).
private theorem powered_parameter_base_nilpotent
    (k : Type u) [Field k] (d c : ℕ) (hc : 1 ≤ c) :
    let J : Ideal (MvPolynomial (Fin d) k) :=
      Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
    ∀ (p : Ideal (MvPolynomial (Fin d) k ⧸ J)) [p.IsPrime],
      ∃ n : ℕ, 1 ≤ n ∧
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ n = ⊥ := by
  classical
  dsimp
  intro p hp
  let P := MvPolynomial (Fin d) k
  let J : Ideal P :=
    Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
  let Q := P ⧸ J
  let m : Ideal P := Ideal.span (Set.range (MvPolynomial.X : Fin d → P))
  obtain ⟨hm, _⟩ := MvPolynomial.polynomial_origin_regularLocal k d
  have : m.IsMaximal := hm
  have hJm : J ≤ m := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.pow_mem_of_mem _
      (Ideal.subset_span (Set.mem_range_self i)) c (by omega)) 8 (by omega)
  let mQ := m.map (Ideal.Quotient.mk J)
  have hmQ : mQ.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa only [Ideal.mk_ker] using hJm)
  have hmQnil : mQ ≤ nilradical Q := by
    dsimp only [mQ, m]
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change ∃ n, (Ideal.Quotient.mk J (MvPolynomial.X i)) ^ n ∈ (⊥ : Ideal Q)
    refine ⟨c * 8, ?_⟩
    rw [← map_pow, pow_mul, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self i))]
    exact Ideal.zero_mem _
  have hnilp : nilradical Q ≤ p := by
    exact hp.radical_le_iff.mpr bot_le
  have hpEq : p = mQ := (hmQ.eq_of_le hp.ne_top (hmQnil.trans hnilp)).symm
  have hpNil : IsNilpotent p :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian p)).mpr
      (hpEq ▸ hmQnil)
  obtain ⟨n, hn⟩ := hpNil
  refine ⟨n + 1, by omega, ?_⟩
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
    pow_succ, hn, zero_mul]
  exact Ideal.map_bot

/-- The quotient map has a Popescu resolution after localization at the quotient prime.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, steps 9--12
(blueprint: lem-weil-pbc-popescu-parameter-quotient-local-resolution).

Proof: Put R=k[x_i], e=8c and p=φ⁻¹(q). The parameter hypothesis implies p is the
origin maximal ideal. The d parameters are a regular sequence in the regular local ring
Λ_q of dimension d. The polynomial-origin regular-local theorem and flat-over-regular
criterion give flatness of R_p→Λ_q. Base change gives flatness after quotienting by the
powered parameters. The reduced base has nilpotent maximal ideal: a monomial of total
degree d(e-1)+1 is divisible by some x_i^e. Its residue field is k, and the closed fiber
of the reduced target is κ(q). Separability expresses that fiber as a filtered colimit
of smooth k-algebras; nilpotent lifting expresses the reduced local target as a filtered
colimit of smooth algebras over the reduced local base. Factor the finitely presented
localized source through a smooth stage. A finitely presented stage can be represented
in the universe of the source and base. Its singular ideal is the unit ideal, so the
factorization satisfies the domination and escape conditions of a Popescu resolution.
Canonical quotient/localization isomorphisms identify these maps with the displayed
ones, since their composites with the quotient maps agree. For d=0 the ideals vanish,
the localized base and target are fields, and the same separable smooth-colimit
factorization proves the assertion. No delocalization is asserted here. -/
theorem parameter_quotient_local_resolution
    {k : Type u} {C : Type v} {Λ : Type w}
    [Field k] [CommRing C] [CommRing Λ] [Algebra k Λ]
    (d c : ℕ) (hc : 1 ≤ c) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ)
    [Algebra (MvPolynomial (Fin d) k) C]
    [FinitePresentation (MvPolynomial (Fin d) k) C]
    (γ : letI := φ.toRingHom.toAlgebra; C →ₐ[MvPolynomial (Fin d) k] Λ)
    (q : PrimeSpectrum Λ) [IsNoetherianRing Λ]
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = (d : WithBot ℕ∞))
    (hgen : Ideal.span (Set.range (fun i : Fin d ↦
      algebraMap Λ (Localization.AtPrime q.asIdeal) (φ (MvPolynomial.X i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (hsep : IsSeparableExtension k q.asIdeal.ResidueField) :
    letI := φ.toRingHom.toAlgebra
    let J : Ideal (MvPolynomial (Fin d) k) :=
      Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
    let J_C := Ideal.map (algebraMap (MvPolynomial (Fin d) k) C) J
    let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
    ∀ (_ : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C))
      (γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ))
      (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
          (Ideal.Quotient.mk J_Λ).comp γ.toRingHom →
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q →
    letI := Localization.AtPrime.algebraOfLiesOver
      (q₀.asIdeal.under (MvPolynomial (Fin d) k ⧸ J)) q₀.asIdeal
    CanBePopescuResolved
      (Algebra.TensorProduct.lift
        (Algebra.ofId (Localization.AtPrime (q₀.asIdeal.under (MvPolynomial (Fin d) k ⧸ J)))
          (Localization.AtPrime q₀.asIdeal))
        ((IsScalarTower.toAlgHom (MvPolynomial (Fin d) k ⧸ J) (Λ ⧸ J_Λ)
          (Localization.AtPrime q₀.asIdeal)).comp γ₀)
        (fun _ _ => Commute.all _ _))
      ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q₀.asIdeal), inferInstance⟩ := by
  classical
  let := φ.toRingHom.toAlgebra
  dsimp
  intro hfp γ₀ q₀ _ hcomap
  let J : Ideal (MvPolynomial (Fin d) k) :=
    Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
  let R := Localization.AtPrime (q₀.asIdeal.under (MvPolynomial (Fin d) k ⧸ J))
  let L₀ := Localization.AtPrime q₀.asIdeal
  let : Algebra R L₀ := Localization.AtPrime.algebraOfLiesOver
    (q₀.asIdeal.under _) q₀.asIdeal
  let L := ULift.{max u v} L₀
  let I := IsLocalRing.maximalIdeal R
  obtain ⟨hflat, hfiber⟩ := parameter_quotient_local_flat_fiber_data
    d c hc φ q hdim hgen hsep q₀ hcomap
  have hI := powered_parameter_base_nilpotent k d c hc (q₀.asIdeal.under _)
  have hind := popescu_lift_nilpotent.{u, max v w} R L I hI hfiber hflat
  let f := Algebra.TensorProduct.lift (Algebra.ofId R L₀)
    ((IsScalarTower.toAlgHom _ _ L₀).comp γ₀) (fun _ _ ↦ Commute.all _ _)
  obtain ⟨B₀, instB₀, algB₀, hsmooth, β₀, δ₀, hcomp⟩ :=
    exists_smooth_factorization_of_ind_smooth
      (ULift.algEquiv.symm.toAlgHom.comp f) hind
  let := instB₀
  let := algB₀
  let := hsmooth
  obtain ⟨n, π, hπ⟩ := FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : FiniteType R B₀)
  have : Small.{max u v} B₀ := small_of_surjective hπ
  let B := Shrink.{max u v} B₀
  let e : B ≃ₐ[R] B₀ := Shrink.algEquiv R B₀
  have : Smooth R B := Smooth.of_equiv e.symm
  let β := e.symm.toAlgHom.comp β₀
  let δ := ULift.algEquiv.toAlgHom.comp (δ₀.comp e.toAlgHom)
  have hsing : singularIdeal R B = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.le_radical
    apply Ideal.subset_span
    change Smooth R (Localization.Away (1 : B))
    have : Smooth B (Localization.Away (1 : B)) := Smooth.of_isLocalization_Away 1
    exact Smooth.comp R B (Localization.Away (1 : B))
  have htop : popescuIdeal δ = ⊤ := by
    unfold popescuIdeal
    rw [hsing, Ideal.map_top, Ideal.radical_top]
  refine ⟨B, inferInstance, inferInstance, β, δ, inferInstance, ?_, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun hcomp x
    change (δ₀ (e (e.symm (β₀ x)))).down = f x
    rw [e.apply_symm_apply]
    exact congrArg ULift.down hx
  · rw [htop]
    exact le_top
  · rw [htop, top_le_iff]
    exact (IsLocalRing.maximalIdeal.isMaximal L₀).ne_top

end Algebra
