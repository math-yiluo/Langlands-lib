/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HenselianDVRExtension
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.FieldTheory.Separable

/-!

# A henselian trait is separably closed in a power series completion

Let `R` be a henselian discrete valuation ring and `ι : R ⟶ k⟦t⟧` an injective ring map to the
power series over a field `k`, such that a uniformizer of `R` maps to a power series of order
one (`ι` is unramified) and the residue map `R ⟶ k⟦t⟧ ⟶ k` is surjective. Then the fraction field
`Frac R` is separably closed in `k((t)) = Frac k⟦t⟧`
(`IsDiscreteValuationRing.mem_range_fractionRingMap_of_isSeparable`).

For an element `α` of `k((t))` separable over `Frac R`, let `L = Frac R(α)` and `B` the integral
closure of `R` in `L`, a discrete valuation ring with `π = u ϖ ^ e` and `e f = [L : Frac R]`
(the fundamental identity
`IsDiscreteValuationRing.exists_eq_unit_mul_pow_mul_finrank_residueField`).
The ring `B` maps to `k⟦t⟧`, which is integrally closed; comparing the orders of `π`, `u` and `ϖ`
gives `e = 1`, and the residue field of `B`, which embeds into `k`, is that of `R`, so `f = 1`.

This is the henselian input of SGA 4½, [Th. finitude], 3.3: the strict localization of `𝔸¹_S` at
the generic point of its special fibre is separably closed in the completion of its fraction
field.

-/

@[expose] public section

universe u

open IsLocalRing Polynomial IntermediateField

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] {k : Type u} [Field k]
  (ι : R →+* PowerSeries k) (hι : Function.Injective ι)

omit [IsDomain R] in
/-- The composite `R ⟶ k⟦t⟧ ⟶ k((t))` is injective. -/
lemma injective_algebraMap_fractionRing_comp (hι : Function.Injective ι) :
    Function.Injective ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp ι) :=
  (IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))).comp hι

/-- The embedding `Frac R ⟶ k((t))` of fraction fields induced by an injection `ι : R ⟶ k⟦t⟧`. -/
noncomputable def fractionRingMap : FractionRing R →+* FractionRing (PowerSeries k) :=
  IsFractionRing.lift (injective_algebraMap_fractionRing_comp ι hι)

/-- The embedding of fraction fields extends `ι`. -/
lemma fractionRingMap_algebraMap (r : R) :
    fractionRingMap ι hι (algebraMap R (FractionRing R) r) =
      algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (ι r) :=
  IsFractionRing.lift_algebraMap _ r

variable [IsDiscreteValuationRing R] [HenselianLocalRing R]

/-- **A henselian trait is separably closed in a power series completion.** Let `R` be a henselian
discrete valuation ring and `ι : R ⟶ k⟦t⟧` injective, mapping a uniformizer to a power series of
order one, with surjective residue map `R ⟶ k`. Then every element of `k((t))` separable over
`Frac R` lies in `Frac R`. -/
theorem mem_range_fractionRingMap_of_isSeparable {π : R} (hπ : Irreducible π)
    (hπι : (ι π).order = 1) (hres : ∀ c : k, ∃ r : R, PowerSeries.constantCoeff (ι r) = c)
    (α : FractionRing (PowerSeries k))
    (hα : letI := (fractionRingMap ι hι).toAlgebra; IsSeparable (FractionRing R) α) :
    α ∈ (fractionRingMap ι hι).range := by
  classical
  let P := FractionRing R
  let Q := FractionRing (PowerSeries k)
  let : Algebra P Q := (fractionRingMap ι hι).toAlgebra
  let : Algebra R Q := ((algebraMap (PowerSeries k) Q).comp ι).toAlgebra
  have : IsScalarTower R P Q :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (fractionRingMap_algebraMap ι hι r).symm
  have hαi : IsIntegral P α := hα.isIntegral
  let L : IntermediateField P Q := P⟮α⟯
  have : FiniteDimensional P L := IntermediateField.adjoin.finiteDimensional hαi
  have : Algebra.IsSeparable P L :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hα
  obtain ⟨ϖ, u, e, hϖ, hu, he⟩ := exists_eq_unit_mul_pow_mul_finrank_residueField R P L hπ
  let B := integralClosure R L
  let := isLocalRing_integralClosure R L
  let := isLocalHom_algebraMap_integralClosure R P L
  -- the ring `B` maps to the integrally closed ring `k⟦t⟧`
  have hmem (b : B) : ((b : L) : Q) ∈ (algebraMap (PowerSeries k) Q).range := by
    have hb : IsIntegral R ((b : L) : Q) := b.2.map (L.val.restrictScalars R)
    have hb' : IsIntegral (PowerSeries k) ((b : L) : Q) :=
      IsIntegral.map_of_comp_eq ι (RingHom.id Q) rfl hb
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hb'
    exact ⟨y, hy⟩
  let e₀ := RingEquiv.ofLeftInverse
    (Function.leftInverse_invFun (IsFractionRing.injective (PowerSeries k) Q))
  let β : B →+* PowerSeries k := e₀.symm.toRingHom.comp
    ((L.val.toRingHom.comp B.val.toRingHom).codRestrict _ hmem)
  have hβ (b : B) : algebraMap (PowerSeries k) Q (β b) = ((b : L) : Q) :=
    (RingEquiv.ofLeftInverse_apply _ _).symm.trans (congrArg Subtype.val (e₀.apply_symm_apply _))
  have hβinj : Function.Injective β := fun a b hab ↦ by
    have := congrArg (algebraMap (PowerSeries k) Q) hab
    rw [hβ, hβ] at this
    exact Subtype.ext (Subtype.ext this)
  have hβR (r : R) : β (algebraMap R B r) = ι r := by
    apply IsFractionRing.injective (PowerSeries k) Q
    rw [hβ]
    rfl
  -- the ramification index is one
  have hu0 : (β u).order = 0 := PowerSeries.order_zero_of_isUnit (u.isUnit.map β)
  have hϖ0 : (β ϖ).order ≠ ⊤ := by
    rw [Ne, PowerSeries.order_eq_top, ← map_zero β]
    exact fun h ↦ hϖ.ne_zero (hβinj h)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hϖ0
  have key : ((e * m : ℕ) : ℕ∞) = 1 := by
    rw [← hπι, ← hβR, hu, map_mul, map_pow, PowerSeries.order_mul, PowerSeries.order_pow, hu0,
      zero_add, ← hm, nsmul_eq_mul, Nat.cast_mul]
  have he1 : e = 1 := Nat.eq_one_of_mul_eq_one_right (by exact_mod_cast key)
  -- the residue degree is one
  have hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField B)) := by
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, hr⟩ := hres (PowerSeries.constantCoeff (β b))
    refine ⟨residue R r, ?_⟩
    rw [ResidueField.algebraMap_residue, ← sub_eq_zero, ← RingHom.map_sub, residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h := (hunit.map β).map (PowerSeries.constantCoeff (R := k))
    rw [RingHom.map_sub, hβR, map_sub, hr, sub_self] at h
    exact not_isUnit_zero h
  have hf : Module.finrank (ResidueField R) (ResidueField B) = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap _ _)
      ⟨(algebraMap (ResidueField R) (ResidueField B)).injective, hsurj⟩).finrank_eq.symm.trans
      (Module.finrank_self _)
  rw [he1, hf, one_mul, eq_comm, IntermediateField.finrank_eq_one_iff] at he
  have hαL : α ∈ L := IntermediateField.mem_adjoin_simple_self P α
  rw [he, IntermediateField.mem_bot] at hαL
  obtain ⟨x, hx⟩ := hαL
  exact ⟨x, hx⟩

end IsDiscreteValuationRing
