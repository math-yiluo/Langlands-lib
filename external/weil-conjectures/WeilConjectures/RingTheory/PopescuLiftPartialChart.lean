/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuLiftPresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.EquationCountFibreDimensionFlat
import WeilConjectures.RingTheory.PopescuPartialChartPolynomial
import WeilConjectures.RingTheory.KaehlerDifferentialsPolynomialExtension
import Mathlib.RingTheory.Kaehler.TensorProduct
import all WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension

/-! # The partial equation chart in Popescu lifting

Source: Stacks Project, Tag 07CP, the presentation and equation count for D_k.
(blueprint: lem-weil-pbc-popescu-lift-partial-chart-dimension).
-/

@[expose] public section

noncomputable section

universe a c

namespace Algebra.PopescuLiftPresentation

variable {R : Type a} {Cbar : Type c} [CommRing R] [CommRing Cbar] {π : R}
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]

/-- One equation per auxiliary variable: u_l on E_k, and p_kl on its complement. -/
def chartEquation (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (l : Fin d.m) : d.polynomial :=
  if l ∈ d.E k then d.equation (.inl l) else d.equation (.inr (k, l))

abbrev chartIdeal (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  Ideal.span (Set.range (d.chartEquation k))

/-- The partial chart is an explicit quotient, with no chosen existence witness. -/
abbrev chartAlgebra (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  ULift.{c} (d.polynomial ⧸ d.chartIdeal k)

/-- Each partial-chart relation is a relation of the full lifting algebra. -/
theorem chartIdeal_le (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :
    d.chartIdeal k ≤ d.definingIdeal := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨l, rfl⟩
  unfold chartEquation
  split <;> exact Ideal.subset_span ⟨_, rfl⟩

/-- The canonical quotient map from the partial chart to the lifting algebra. -/
def chartMap (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :
    d.chartAlgebra k →ₐ[R] d.liftingAlgebra :=
  (ULift.algEquiv (R := R)).symm.toAlgHom.comp
    ((Ideal.Quotient.liftₐ (d.chartIdeal k) (Ideal.Quotient.mkₐ R d.definingIdeal)
      (fun _ hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (d.chartIdeal_le k hx))).comp
        (ULift.algEquiv (R := R)).toAlgHom)

abbrev chartPrime (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (q : PrimeSpectrum d.liftingAlgebra) :=
  PrimeSpectrum.comap (d.chartMap k).toRingHom q

abbrev chartLocal (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (q : PrimeSpectrum d.liftingAlgebra) :=
  Localization.AtPrime (d.chartPrime k q).asIdeal

/-- The cleared relations give the key identity between the two types of equation. -/
theorem equation_key_identity [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (l : Fin d.m) :
    MvPolynomial.C π * d.equation (.inr (k, l)) =
      -d.includeX (d.a k) * d.equation (.inl l) +
        ∑ j ∈ d.E k, d.includeX (d.h k l j) * d.equation (.inl j) := by
  have hrel := congrArg d.includeX (hd.relation k l)
  simp only [map_mul, map_add, map_sum] at hrel
  rw [show d.includeX (MvPolynomial.C (π ^ 2)) = (MvPolynomial.C π) ^ 2 by
    change (MvPolynomial.rename Sum.inl) (MvPolynomial.C (π ^ 2)) = _
    rw [MvPolynomial.rename_C, MvPolynomial.C_pow]] at hrel
  have hsum : (∑ j ∈ d.E k, d.includeX (d.h k l j) *
      (d.includeX (d.f j) - MvPolynomial.C π * MvPolynomial.X (.inr j))) =
    (∑ j ∈ d.E k, d.includeX (d.h k l j) * d.includeX (d.f j)) -
      MvPolynomial.C π *
        (∑ j ∈ d.E k, d.includeX (d.h k l j) * MvPolynomial.X (.inr j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [equation]
  rw [hsum]
  change MvPolynomial.C π * _ = _
  change d.includeX (d.a k) * d.includeX (d.f l) =
    (∑ j ∈ d.E k, d.includeX (d.h k l j) * d.includeX (d.f j)) +
      (MvPolynomial.C π) ^ 2 * d.includeX (d.g k l) at hrel
  linear_combination hrel

/-- Invertibility of a_k and the key identity kill every original equation locally. -/
theorem chart_original_equation_eq_zero [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    (l : Fin d.m) :
    algebraMap (d.chartAlgebra k) (d.chartLocal k q)
      (ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inl l)))) = 0 := by
  classical
  let T := d.chartLocal k q
  let ev : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  have hchart (j : Fin d.m) : ev (d.chartEquation k j) = 0 := by
    have hq : Ideal.Quotient.mk (d.chartIdeal k) (d.chartEquation k j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
    change algebraMap (d.chartAlgebra k) T
      ((ULift.algEquiv (R := R)).symm (Ideal.Quotient.mk _ (d.chartEquation k j))) = 0
    rw [hq, map_zero, map_zero]
  have hu (j : Fin d.m) (hj : j ∈ d.E k) : ev (d.equation (.inl j)) = 0 := by
    simpa only [chartEquation, ite_eq_left hj] using hchart j
  change ev (d.equation (.inl l)) = 0
  by_cases hl : l ∈ d.E k
  · exact hu l hl
  have hp : ev (d.equation (.inr (k, l))) = 0 := by
    simpa only [chartEquation, ite_eq_right hl] using hchart l
  have hid := congrArg ev (d.equation_key_identity hd k l)
  simp only [map_mul, map_add, map_neg, map_sum] at hid
  have hsum : (∑ j ∈ d.E k, ev (d.includeX (d.h k l j)) *
      ev (d.equation (.inl j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hu j hj, mul_zero]
  have hmul : ev (d.includeX (d.a k)) * ev (d.equation (.inl l)) = 0 := by
    apply neg_eq_zero.mp
    rw [← neg_mul]
    rw [hp, mul_zero, hsum, add_zero] at hid
    exact hid.symm
  have hunit : IsUnit (ev (d.includeX (d.a k))) :=
    IsLocalization.map_units T
      (⟨ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.includeX (d.a k))), by
        change (d.chartMap k) _ ∉ q.asIdeal
        exact hk⟩ : (d.chartPrime k q).asIdeal.primeCompl)
  exact hunit.mul_right_eq_zero.mp hmul

/-- Every other chart's equation is killed by pi in the partial chart local ring. -/
theorem chart_other_equation_pi_mul_eq_zero [Algebra R Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal)
    (k' : Fin d.r) (l : Fin d.m) :
    algebraMap R (d.chartLocal k q) π *
      algebraMap (d.chartAlgebra k) (d.chartLocal k q)
        (ULift.up (Ideal.Quotient.mk (d.chartIdeal k) (d.equation (.inr (k', l))))) = 0 := by
  let T := d.chartLocal k q
  let ev : d.polynomial →+* T :=
    (algebraMap (d.chartAlgebra k) T).comp
      ((ULift.algEquiv (R := R)).symm.toRingHom.comp (Ideal.Quotient.mk (d.chartIdeal k)))
  have hu (j : Fin d.m) : ev (d.equation (.inl j)) = 0 :=
    d.chart_original_equation_eq_zero hd k q hk j
  have hid := congrArg ev (d.equation_key_identity hd k' l)
  simp only [map_mul, map_add, map_neg, map_sum] at hid
  have hsum : (∑ j ∈ d.E k', ev (d.includeX (d.h k' l j)) *
      ev (d.equation (.inl j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hu j, mul_zero]
  rw [hu l, mul_zero, hsum, zero_add] at hid
  exact hid

/-- The same m chart equations, with the variables numbered by Fin(n+m). -/
def finiteChartEquation (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r)
    (l : Fin d.m) : MvPolynomial (Fin (d.n + d.m)) R :=
  MvPolynomial.rename finSumFinEquiv (d.chartEquation k l)

abbrev finiteChartAlgebra (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :=
  MvPolynomial (Fin (d.n + d.m)) R ⧸ Ideal.span (Set.range (d.finiteChartEquation k))

/-- Renumbering variables identifies the finite presentation with the partial chart. -/
def finiteChartEquiv (d : PopescuLiftPresentation R Cbar π) (k : Fin d.r) :
    d.finiteChartAlgebra k ≃ₐ[R] d.chartAlgebra k :=
  (Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R finSumFinEquiv).symm
    (by
      rw [Ideal.map_span]
      change Ideal.span (Set.range (d.chartEquation k)) = _
      apply congrArg Ideal.span
      rw [← Set.range_comp']
      apply congrArg Set.range
      funext l
      change d.chartEquation k l = (MvPolynomial.renameEquiv R finSumFinEquiv).symm
        ((MvPolynomial.renameEquiv R finSumFinEquiv) (d.chartEquation k l))
      exact ((MvPolynomial.renameEquiv R finSumFinEquiv).symm_apply_apply _).symm)).trans
    (ULift.algEquiv (R := R)).symm

/-- The smooth special fibre of the partial chart has dimension n at the chosen prime.

Source: Stacks Project, Tag 07CP (lemma-lifting), the calculation of D_k/pi D_k.
(blueprint: lem-weil-pbc-popescu-lift-partial-chart-dimension).

Proof: Pull the chosen prime back along finiteChartEquiv and chartMap. Its contraction
contains pi, so the residue field B is a compatible R/pi^2-algebra killing pi. The fibre
prime avoids the image t of a_k. The partial-chart polynomial-model theorem identifies
the localization at t with a polynomial algebra in card(E_k) variables over the base
change to B of the smooth reduced coefficient chart. Base change Prepared.differentials
using tensorKaehlerEquiv, and apply the polynomial differential decomposition. Transfer
the resulting basis through the polynomial model using differential base change for its
formally etale algebra equivalence. At a prime Q above the fibre point, base change this
basis to the residue field; its rank is (n-card(E_k))+card(E_k)=n by Prepared.card_le.
The smooth-over-field differential dimension theorem gives dimension n at Q. The spectrum
map of localization at t is an open embedding, which preserves dimension at a point,
so the original fibre point also has dimension n. No flatness or equality of annihilators
is used. -/
theorem partial_chart_fibre_dimension [Algebra R Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal) :
    let q' := PrimeSpectrum.comap (d.finiteChartEquiv k).toRingHom (d.chartPrime k q)
    let p := PrimeSpectrum.comap (algebraMap R (d.finiteChartAlgebra k)) q'
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R (d.finiteChartAlgebra k) p ⟨q', rfl⟩) =
        (d.n : WithBot ℕ∞) := by
  classical
  let S := d.finiteChartAlgebra k
  let e := d.finiteChartEquiv k
  let q' := PrimeSpectrum.comap e.toRingHom (d.chartPrime k q)
  let p := PrimeSpectrum.comap (algebraMap R S) q'
  let B := p.asIdeal.ResidueField
  let R₂ := R ⧸ Ideal.span ({π ^ 2} : Set R)
  let A := Localization.Away (d.reducedElement k)
  let s : S := Ideal.Quotient.mk _
    (MvPolynomial.rename finSumFinEquiv (d.includeX (d.a k)))
  have hπp : π ∈ p.asIdeal := by
    change d.chartMap k (e (algebraMap R S π)) ∈ q.asIdeal
    rw [e.commutes, (d.chartMap k).commutes]
    exact hπ
  have hπB : algebraMap R B π = 0 := Ideal.algebraMap_residueField_eq_zero.mpr hπp
  let base : R₂ →ₐ[R] B := Ideal.Quotient.liftₐ _ (Algebra.ofId R B) (by
    change Ideal.span ({π ^ 2} : Set R) ≤ RingHom.ker (algebraMap R B)
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change algebraMap R B (π ^ 2) = 0
    rw [map_pow, hπB, zero_pow (by decide)])
  let : Algebra R₂ B := base.toRingHom.toAlgebra
  have : IsScalarTower R R₂ B := IsScalarTower.of_algHom base
  have hs : s ∉ q'.asIdeal := by
    change d.chartMap k (e s) ∉ q.asIdeal
    change (ULift.algEquiv (R := R)).symm
      (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal at hk
    simpa [s, e, finiteChartEquiv, chartMap, includeX, Function.comp_def] using hk
  let T := p.asIdeal.Fiber S
  let qF : PrimeSpectrum T := PrimeSpectrum.preimageEquivFiber R S p ⟨q', rfl⟩
  let t : T := Algebra.TensorProduct.includeRight (R := R) (A := B) s
  have ht : t ∉ qF.asIdeal := by
    have he := congrArg (fun x ↦ x.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q', rfl⟩)
    change Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qF.asIdeal =
      q'.asIdeal at he
    intro h
    exact hs (he ▸ h)
  let C := TensorProduct R₂ B A
  let : Algebra A C := Algebra.TensorProduct.rightAlgebra
  let P := MvPolynomial (Fin (d.E k).card) C
  let L := Localization.Away t
  obtain ⟨model⟩ := popescu_partial_chart_polynomial R Cbar π d hd B hπB k
    (d.finiteChartEquation k) (fun _ ↦ rfl)
  have : Smooth R₂ A := hd.smooth k
  have : Smooth B C := inferInstance
  have : Smooth C P := ⟨inferInstance, inferInstance⟩
  have : Smooth B P := Smooth.comp B C P
  have : Smooth B L := Smooth.of_equiv model
  obtain ⟨bA⟩ := hd.differentials k
  let bC := (bA.baseChange C).map (KaehlerDifferential.tensorKaehlerEquiv R₂ B A C)
  obtain ⟨bP⟩ := (KaehlerDifferential.exists_polynomial_extension_equiv B C
    (d.E k).card).2 (d.n - (d.E k).card) ⟨bC⟩
  let : Algebra P L := model.toRingHom.toAlgebra
  have : IsScalarTower B P L := IsScalarTower.of_algHom model.toAlgHom
  let modelP : P ≃ₐ[P] L := AlgEquiv.ofRingEquiv (f := model.toRingEquiv) (fun _ ↦ rfl)
  have : FormallyEtale P L := FormallyEtale.of_equiv modelP
  let bL := (bP.baseChange L).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale B P L)
  have hQ : qF ∈ Set.range (PrimeSpectrum.comap (algebraMap T L)) := by
    rw [PrimeSpectrum.localization_away_comap_range L t]
    exact ht
  obtain ⟨Q, hQ⟩ := hQ
  let K := Q.asIdeal.ResidueField
  let bK := bL.baseChange K
  have hfin : Module.finrank K (TensorProduct L K (KaehlerDifferential B L)) = d.n := by
    rw [Module.finrank_eq_card_basis bK]
    simp only [Fintype.card_fin]
    exact Nat.sub_add_cancel (hd.card_le k)
  have hsm : IsSmoothAtPrime B Q := by
    have : Smooth L (Localization.Away (1 : L)) := Smooth.of_isLocalization_Away 1
    exact ⟨1, Q.asIdeal.one_notMem, Smooth.comp B L (Localization.Away (1 : L))⟩
  have hdim := (finiteDimensional_and_finrank_kaehlerDifferential_eq_of_isSmoothAtPrime
    Q hsm).2
  change topologicalKrullDimAt qF = _
  rw [← hQ, ← Algebra.dimAt_openEmbedding
    (PrimeSpectrum.localization_away_isOpenEmbedding L t) Q, ← hdim, hfin]

/-- Apply equation-count flatness to the finite presentation of the partial chart.

Source: Stacks Project, Tag 07CP, applying Tag 00ST to D_k.
(blueprint: lem-weil-pbc-popescu-lift-partial-chart-dimension). -/
theorem partial_chart_flat [Algebra R Cbar] [IsNoetherianRing R]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (k : Fin d.r) (q : PrimeSpectrum d.liftingAlgebra)
    (hπ : algebraMap R d.liftingAlgebra π ∈ q.asIdeal)
    (hk : ULift.up (Ideal.Quotient.mk d.definingIdeal (d.includeX (d.a k))) ∉ q.asIdeal) :
    Module.Flat R (d.chartLocal k q) := by
  let e := d.finiteChartEquiv k
  let q' := PrimeSpectrum.comap e.toRingHom (d.chartPrime k q)
  have hdim := d.partial_chart_fibre_dimension hd k q hπ hk
  have hflat : Module.Flat R (Localization.AtPrime q'.asIdeal) :=
    (MvPolynomial.exists_flat_away_of_fibre_dimension_eq R (d.n + d.m) d.m
      (Nat.le_add_left _ _) (d.finiteChartEquation k) q'
      (by simpa only [Nat.add_sub_cancel] using hdim)).2.1
  let el := IsLocalization.ringEquivOfRingEquiv (M := q'.asIdeal.primeCompl)
    (T := (d.chartPrime k q).asIdeal.primeCompl)
    (Localization.AtPrime q'.asIdeal) (d.chartLocal k q) e.toRingEquiv
    (e.toRingEquiv.map_primeCompl_comap_eq (d.chartPrime k q).asIdeal)
  let eA : Localization.AtPrime q'.asIdeal ≃ₐ[R] d.chartLocal k q :=
    AlgEquiv.ofRingEquiv (f := el) fun r ↦ by
      dsimp only [el]
      rw [IsScalarTower.algebraMap_apply R (d.finiteChartAlgebra k)
        (Localization.AtPrime q'.asIdeal), IsLocalization.ringEquivOfRingEquiv_eq]
      change algebraMap (d.chartAlgebra k) (d.chartLocal k q)
        (e (algebraMap R (d.finiteChartAlgebra k) r)) = _
      rw [e.commutes, ← IsScalarTower.algebraMap_apply R (d.chartAlgebra k)
        (d.chartLocal k q)]
  exact Module.Flat.of_linearEquiv eA.symm.toLinearEquiv

end Algebra.PopescuLiftPresentation
