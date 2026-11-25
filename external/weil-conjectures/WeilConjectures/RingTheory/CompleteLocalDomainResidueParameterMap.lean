/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Residue-preserving parameter maps for complete local domains

Source: Stacks Project, Algebra, Lemma Tag 032D, the parameter construction in Cases I and II.
(blueprint: lem-weil-pbc-complete-local-domain-residue-parameter-map)
-/

@[expose] public section

universe u
set_option autoImplicit false

namespace IsLocalRing

private theorem factor_of_bound {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ]
    (p : Λ) (hm : maximalIdeal Λ = Ideal.span {p}) (N : ℕ) :
    ∀ x : Λ, x ∉ maximalIdeal Λ ^ N → ∃ n : ℕ, ∃ y : Λ, IsUnit y ∧ x = p ^ n * y := by
  induction N with
  | zero => simp
  | succ N ih =>
    intro x hx
    by_cases hu : IsUnit x
    · exact ⟨0, x, hu, by simp⟩
    have hxmem : x ∈ maximalIdeal Λ := by simpa [mem_maximalIdeal] using hu
    rw [hm, Ideal.mem_span_singleton] at hxmem
    obtain ⟨y, hy⟩ := hxmem
    have hynot : y ∉ maximalIdeal Λ ^ N := by
      intro hyN
      apply hx
      rw [hy, pow_succ']
      exact Ideal.mul_mem_mul (by rw [hm]; exact Ideal.subset_span (by simp)) hyN
    obtain ⟨n, z, hz, hzy⟩ := ih y hynot
    refine ⟨n + 1, z, hz, ?_⟩
    rw [hy, hzy, pow_succ']
    ring

private theorem field_or_cohen {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (p : ℕ) (hp : Nat.Prime p ∨ p = 0)
    (hm : maximalIdeal Λ = Ideal.span {(p : Λ)}) :
    IsField Λ ∨ ∃ q : ℕ, IsCohenRing q Λ := by
  by_cases hfield : IsField Λ
  · exact Or.inl hfield
  have hmne : maximalIdeal Λ ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hfield
  have hp0 : (p : Λ) ≠ 0 := by
    intro h
    apply hmne
    simp [hm, h]
  have hprime : Nat.Prime p := hp.resolve_right (fun h ↦ hp0 (by simp [h]))
  have hirr : Irreducible (p : Λ) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (p : Λ) hp0 hm
  have hdvr : IsDiscreteValuationRing Λ := by
    apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    refine ⟨(p : Λ), hirr, ?_⟩
    intro x hx
    have hex : ∃ N : ℕ, x ∉ maximalIdeal Λ ^ N := by
      by_contra! h
      apply hx
      apply IsHausdorff.haus' (I := maximalIdeal Λ)
      intro N
      apply SModEq.zero.mpr
      simpa using h N
    obtain ⟨N, hN⟩ := hex
    obtain ⟨n, y, hy, hxy⟩ := factor_of_bound (p : Λ) hm N x hN
    obtain ⟨u, hu⟩ := hy
    refine ⟨n, u, ?_⟩
    simpa [hu, mul_comm] using hxy.symm
  exact Or.inr ⟨p, hprime, inferInstance, hdvr, hm, hm ▸ inferInstance⟩

private theorem parameters (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ∃ (n : ℕ) (t : Fin n → R),
      (n : WithBot ℕ∞) = ringKrullDim R ∧
      (∀ i, t i ∈ maximalIdeal R) ∧
      ∃ N : ℕ, maximalIdeal R ^ N ≤ Ideal.span (Set.range t) := by
  classical
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  let t : Fin s.card → R := fun i ↦ (s.equivFin.symm i).val
  have hrange : Set.range t = (s : Set R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).property
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [t]⟩
  have hle : Ideal.span (s : Set R) ≤ maximalIdeal R := hs.1.2
  have : IsArtinianRing (R ⧸ Ideal.span (s : Set R)) :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hs
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    (Ideal.span (s : Set R))
  refine ⟨s.card, t, ?_, ?_, N, ?_⟩
  · rw [← maximalIdeal_height_eq_ringKrullDim, ← hcard]
    rfl
  · intro i
    exact hle (Ideal.subset_span (hrange ▸ Set.mem_range_self i))
  · rwa [hrange]

private theorem residue_parameters {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R]
    (Λ : Subring R) [IsLocalRing Λ]
    (hm : maximalIdeal Λ = (maximalIdeal R).comap Λ.subtype)
    (hΛ : IsField Λ ∨ ∃ p : ℕ, IsCohenRing p Λ) :
    ∃ (n : ℕ) (t : Fin n → R),
      ringKrullDim (MvPowerSeries (Fin n) Λ) = ringKrullDim R ∧
      (∀ i, t i ∈ maximalIdeal R) ∧
      ∃ N : ℕ, maximalIdeal R ^ N ≤
        (maximalIdeal Λ).map Λ.subtype ⊔ Ideal.span (Set.range t) := by
  rcases hΛ with hf | ⟨p, hp⟩
  · obtain ⟨n, t, hdim, ht, N, hN⟩ := parameters R
    obtain h | h := MvPowerSeries.power_series_field_cohen_regular_complete n (Or.inl hf)
    · obtain ⟨_, _, _, _, _, _, _, _, _, hsource⟩ := h
      exact ⟨n, t, hsource.trans hdim, ht, N, hN.trans le_sup_right⟩
    · obtain ⟨p, hp, _⟩ := h
      obtain ⟨_, _, hdvr, _, _⟩ := hp
      exact (IsDiscreteValuationRing.not_isField Λ hf).elim
  · have hcohen := hp
    obtain ⟨hprime, hdom, hdvr, hmax, hcomplete⟩ := hp
    let _ := hdom
    let _ := hdvr
    have hpin : (p : R) ∈ maximalIdeal R := by
      have : (p : Λ) ∈ maximalIdeal Λ := by
        rw [hmax]
        exact Ideal.subset_span (by simp)
      rw [hm] at this
      exact this
    have hpne : (p : R) ≠ 0 := by
      intro h
      have hpΛ : (p : Λ) = 0 := Subtype.ext h
      exact IsDiscreteValuationRing.not_a_field Λ (by simp [hmax, hpΛ])
    let P : Ideal R := Ideal.span {(p : R)}
    have hPle : P ≤ maximalIdeal R := by
      rw [Ideal.span_le]
      simpa using hpin
    have hPne : P ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hPle
    have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPne
    let q : R →+* R ⧸ P := Ideal.Quotient.mk P
    have : IsLocalRing (R ⧸ P) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
    obtain ⟨n, tq, hdim, htq, N, hN⟩ := parameters (R ⧸ P)
    choose t ht using fun i ↦ Ideal.Quotient.mk_surjective (tq i)
    have htmem : ∀ i, t i ∈ maximalIdeal R := by
      intro i
      rw [← maximalIdeal_comap q]
      change q (t i) ∈ maximalIdeal (R ⧸ P)
      rw [show q (t i) = tq i from ht i]
      exact htq i
    have hmap : (Ideal.span (Set.range t)).map q = Ideal.span (Set.range tq) := by
      rw [Ideal.map_span, ← Set.range_comp]
      congr 2
      exact funext ht
    have hprimary : maximalIdeal R ^ N ≤ P ⊔ Ideal.span (Set.range t) := by
      have hle : (maximalIdeal R ^ N).map q ≤ (Ideal.span (Set.range t)).map q := by
        rw [Ideal.map_pow, map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,
          hmap]
        exact hN
      rw [Ideal.map_le_iff_le_comap,
        Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hle
      simpa [sup_comm] using hle
    have hcoeff : (maximalIdeal Λ).map Λ.subtype = P := by
      rw [hmax, Ideal.map_span, Set.image_singleton]
      rfl
    have hsource := MvPowerSeries.power_series_field_cohen_regular_complete n
      (Or.inr ⟨p, hcohen⟩)
    rcases hsource with hfield | ⟨p', hp', _, _, _, _, _, _, _, _, hsource⟩
    · exact (IsDiscreteValuationRing.not_isField Λ hfield.1).elim
    · have hdimR : ringKrullDim (R ⧸ P) + 1 = ringKrullDim R :=
        ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
          (by simpa using hpne) hpin
      refine ⟨n, t, ?_, htmem, N, ?_⟩
      · rw [hsource, Nat.cast_add, Nat.cast_one, hdim]
        exact hdimR
      · rwa [hcoeff]

private theorem finite_reduction {A R : Type*} [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
    (hmap : (maximalIdeal A).map (algebraMap A R) ≤ maximalIdeal R)
    (hpow : ∃ N : ℕ, maximalIdeal R ^ N ≤ (maximalIdeal A).map (algebraMap A R))
    (hsurj : Function.Surjective ((residue R).comp (algebraMap A R))) :
    Module.Finite (A ⧸ maximalIdeal A)
      (R ⧸ (maximalIdeal A • ⊤ : Submodule A R)) := by
  let J := (maximalIdeal A).map (algebraMap A R)
  have hJ : J ≠ ⊤ := by
    intro h
    have : J ≤ maximalIdeal R := hmap
    rw [show J = ⊤ from h] at this
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp this)
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmin : maximalIdeal R ∈ J.minimalPrimes := by
    refine ⟨⟨inferInstance, hmap⟩, ?_⟩
    intro K hK hKm
    obtain ⟨N, hN⟩ := hpow
    have hmK : maximalIdeal R ≤ K := by
      intro x hx
      exact hK.1.mem_of_pow_mem N ((hN.trans hK.2) (Ideal.pow_mem_pow hx N))
    exact hmK
  have : IsArtinianRing (R ⧸ J) :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hmin
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hm : maximalIdeal (R ⧸ J) = (maximalIdeal R).map q := by
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [q, sup_eq_left.mpr (show J ≤ maximalIdeal R from hmap),
      mem_maximalIdeal]
  have hres : Function.Surjective
      (algebraMap A ((R ⧸ J) ⧸ Ring.jacobson (R ⧸ J))) := by
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨a, ha⟩ := hsurj (residue R r)
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (q (algebraMap A R a)) = Ideal.Quotient.mk _ (q r)
    rw [Ideal.Quotient.eq]
    rw [← map_sub]
    rw [ringJacobson_eq_maximalIdeal, hm]
    apply Ideal.mem_map_of_mem
    apply Ideal.Quotient.eq.mp
    exact ha
  have : Module.Finite A ((R ⧸ J) ⧸ Ring.jacobson (R ⧸ J)) :=
    Module.Finite.of_surjective (Algebra.linearMap A _) hres
  have : Module.Finite A (R ⧸ J) :=
    IsSemiprimaryRing.finite_of_isArtinian A (R ⧸ J) (R ⧸ J)
  have : Module.Finite A (R ⧸ (maximalIdeal A • ⊤ : Submodule A R)) := by
    rw [Ideal.smul_top_eq_map]
    exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv A J).symm
  exact Module.Finite.of_restrictScalars_finite A (A ⧸ maximalIdeal A) _

private theorem power_series_maximalIdeal {Λ : Type u} [CommRing Λ] [IsLocalRing Λ]
    (n : ℕ) : maximalIdeal (MvPowerSeries (Fin n) Λ) =
      (maximalIdeal Λ).map MvPowerSeries.C ⊔
        Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) Λ)) := by
  have hcomap : maximalIdeal (MvPowerSeries (Fin n) Λ) =
      (maximalIdeal Λ).comap MvPowerSeries.constantCoeff := by
    ext f
    simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
  have hk := (MvPowerSeries.quotient_first_variables Λ n n le_rfl).2.2.2.2.1
  rw [hcomap]
  apply le_antisymm
  · intro f hf
    have hdiff : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈
        RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin n)) := by simp
    rw [hk] at hdiff
    have hc := Ideal.mem_map_of_mem (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin n) Λ)
      (show MvPowerSeries.constantCoeff f ∈ maximalIdeal Λ from hf)
    simpa using (Submodule.mem_sup.mpr ⟨_, hc, _, hdiff, add_sub_cancel _ _⟩)
  · apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · rw [← hk]
      exact Ideal.comap_mono bot_le

/-- The parameter construction gives a power-series algebra of the same dimension, with
Hausdorff target, finite reduction, and a surjective map to the target residue field.

Source: Stacks Project, Algebra, Lemma Tag 032D, Cases I and II before the application of
Lemma Tag 031D. (blueprint: lem-weil-pbc-complete-local-domain-residue-parameter-map)

Proof:
1. Choose a coefficient subring using Tag 032A(1). It is a domain with complete
   principal maximal ideal (p). Unless it is a field, p is nonzero and irreducible.
   Separatedness bounds the order of each nonzero element; induction on that bound
   expresses it as a unit times a power of p. Mathlib's factorization criterion makes
   the coefficient subring a DVR, hence a Cohen ring.
2. Mathlib's height theorem gives a parameter finset of cardinality dim R in the field
   case, or dim(R/pR) in the Cohen case. The associated quotient is Artinian, so a
   power of the maximal ideal lies in the parameter ideal. In the Cohen case lift the
   parameters from R/pR; the nonzerodivisor dimension formula gives dim(R/pR)+1=dim R.
3. Evaluate series directly using the given maximal-ideal completeness of R. The
   variables lie in its maximal ideal, so the complete power-series universal property
   applies to the coefficient inclusion and these parameters. Evaluation fixes constants.
4. By Tag 032C the source has dimension n in the field case and n+1 in the Cohen case.
   The parameter count in step 2 identifies this with dim R. The constant-coefficient
   kernel is generated by the variables, so the source maximal ideal is generated by
   the coefficient maximal ideal and variables. Its extension is the parameter ideal I.
5. Since I lies in the target maximal ideal, maximal-ideal separatedness of R implies
   Hausdorffness for the source maximal ideal, by Mathlib's IsHausdorff.of_map.
6. Every target residue class lifts from the coefficient subring by the coefficient
   residue isomorphism. The corresponding constant series proves residue surjectivity.
7. A power of the target maximal ideal lies in I, so R/I is Artinian local. Its quotient
   by the Jacobson radical is a surjective image of the source, hence a finite module
   over it. Apply the Artinian finite-length theorem to make R/I finite over the source.
   Identify the ideal quotient with the quotient by the source maximal ideal acting
   on R, and descend scalars to the source residue field.

This only constructs the parameter map and proves its reduction properties. Its finiteness
and injectivity are subsequent steps of Tag 032D, not assumptions of this assertion. -/
theorem complete_local_domain_residue_parameter_map
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsAdicComplete (maximalIdeal R) R] :
    ∃ (n : ℕ) (Λ : Type u) (_ : CommRing Λ),
      ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) Λ))
        (_ : Algebra (MvPowerSeries (Fin n) Λ) R),
        (IsField Λ ∨ ∃ p : ℕ, IsCohenRing p Λ) ∧
        ringKrullDim (MvPowerSeries (Fin n) Λ) = ringKrullDim R ∧
        IsHausdorff (maximalIdeal (MvPowerSeries (Fin n) Λ)) R ∧
        Module.Finite
          (MvPowerSeries (Fin n) Λ ⧸ maximalIdeal (MvPowerSeries (Fin n) Λ))
          (R ⧸ (maximalIdeal (MvPowerSeries (Fin n) Λ) • ⊤ :
            Submodule (MvPowerSeries (Fin n) Λ) R)) ∧
        Function.Surjective ((residue R).comp
          (algebraMap (MvPowerSeries (Fin n) Λ) R)) := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField R)
  let _ := hp
  obtain ⟨Λ, hlocal, hm, hc, hbij, hpmax⟩ := exists_coefficient_subring R p
  let _ := hlocal
  have : IsAdicComplete (maximalIdeal Λ) Λ := hm.symm ▸ hc
  have hΛ : IsField Λ ∨ ∃ q : ℕ, IsCohenRing q Λ :=
    field_or_cohen p (CharP.char_is_prime_or_zero (ResidueField R) p) (hm.trans hpmax)
  obtain ⟨n, t, hdim, ht, N, hN⟩ := residue_parameters Λ hm hΛ
  obtain ⟨Φ, hconst, hvars, _⟩ := MvPowerSeries.exists_ringHom_of_isAdicComplete
    (maximalIdeal R) Λ.subtype n t ht
  let _ : Algebra (MvPowerSeries (Fin n) Λ) R := Φ.toAlgebra
  have hcoeff : Φ.comp (MvPowerSeries.C : Λ →+* MvPowerSeries (Fin n) Λ) =
      Λ.subtype := RingHom.ext hconst
  have hvariable : Φ ∘ (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) Λ) = t :=
    funext hvars
  have hext : (maximalIdeal (MvPowerSeries (Fin n) Λ)).map
      (algebraMap (MvPowerSeries (Fin n) Λ) R) =
      (maximalIdeal Λ).map Λ.subtype ⊔ Ideal.span (Set.range t) := by
    change (maximalIdeal (MvPowerSeries (Fin n) Λ)).map Φ = _
    rw [power_series_maximalIdeal, Ideal.map_sup, Ideal.map_map, hcoeff,
      Ideal.map_span, ← Set.range_comp, hvariable]
  have hle : (maximalIdeal (MvPowerSeries (Fin n) Λ)).map
      (algebraMap (MvPowerSeries (Fin n) Λ) R) ≤ maximalIdeal R := by
    rw [hext]
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      exact hm.le
    · exact Ideal.span_le.mpr (Set.range_subset_iff.mpr ht)
  have hsurj : Function.Surjective ((residue R).comp
      (algebraMap (MvPowerSeries (Fin n) Λ) R)) := by
    intro z
    obtain ⟨a, ha⟩ := hbij.2 z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨MvPowerSeries.C a, ?_⟩
    change residue R (Φ (MvPowerSeries.C a)) = z
    rw [hconst]
    exact ha
  refine ⟨n, Λ, inferInstance, inferInstance, inferInstance, hΛ, hdim,
    IsHausdorff.of_map hle, ?_, hsurj⟩
  apply finite_reduction hle _ hsurj
  exact ⟨N, hext.symm ▸ hN⟩

end IsLocalRing
