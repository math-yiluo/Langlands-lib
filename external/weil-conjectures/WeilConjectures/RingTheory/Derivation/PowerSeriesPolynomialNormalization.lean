/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import WeilConjectures.RingTheory.CompleteLocalQuotient
import WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular
import WeilConjectures.RingTheory.NoetherNormalizationOverDomain
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.CharP.Invertible
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Power series polynomial normalization of a finite type domain

Source: Stacks Project, More on Algebra, Tag 07PH, first two proof paragraphs.
(blueprint: lem-weil-pbc-power-series-polynomial-normalization)
-/

@[expose] public section
set_option autoImplicit false
universe u v w

namespace Derivation

/-- A finite type domain over a complete Noetherian local base contains a polynomial
ring over a power series field, with a finite extension of fraction fields.
Source: Stacks Project, More on Algebra, Tag 07PH (`lemma-find-D`), first two
proof paragraphs, using Algebra Tags 0325, 032D and 07NA.
(blueprint: lem-weil-pbc-power-series-polynomial-normalization)

Proof: replace the base by its image in B, the quotient by the prime kernel.
A proper quotient remains Noetherian, local and complete (0325). The image
has characteristic p because it embeds in B. Apply 032D to this complete local
domain. Its regular coefficient subring is a power series ring over a field:
the Cohen-ring alternative is impossible, since its uniformizer is a nonzero
prime integer whereas, in this subring, p is zero and every other prime
integer is a unit by Bezout. Thus this subring is S = k[[x_1,...,x_n]], and the image base is
finite over S. Finite-type transitivity makes B finite type over S.
Apply 07NA to S inside B. It gives an embedded polynomial ring C over S
and C inside B0 inside B with B0 finite over C and B0[1/g] = B[1/g]
for nonzero g in S. Finite S-algebra generators of B still generate over C.
Consequently B is finite type over C. Localization equality identifies
Frac(B0) with M. Localizing the finite C-module B0 at all nonzero elements
of C gives a finite-dimensional domain over K = Frac(C); it is a field,
because multiplication by any nonzero element is an injective and hence
surjective endomorphism of a finite-dimensional vector space. It is therefore
Frac(B0). These identifications supply the compatible C-K-M algebra tower
and finite-dimensionality asserted below. All embeddings are the inclusions
in B followed by its fraction-field map. -/
theorem exists_powerSeries_polynomial_normalization
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [IsDomain B] [CharP B p]
    (M : Type v) [Field M] [Algebra B M] [IsFractionRing B M]
    (R₀ : Type w) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀]
    [Algebra R₀ B] [Algebra.FiniteType R₀ B] :
    ∃ C : Subring B, Algebra.FiniteType C B ∧
      ∃ (k : Type u) (hk : Field k), letI := hk
        ∃ n m : ℕ, CharP k p ∧
          Nonempty (C ≃+* MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ∧
          ∃ (K : Type u) (hK : Field K), letI := hK
            ∃ aCK : Algebra C K, letI := aCK
              ∃ hfrac : IsFractionRing C K, letI := hfrac
                ∃ aKM : Algebra K M, letI := aKM
                  letI : Algebra C M := ((algebraMap B M).comp C.subtype).toAlgebra
                  IsScalarTower C K M ∧ FiniteDimensional K M := by
  classical
  let φ := algebraMap R₀ B
  let R := φ.range
  let I := RingHom.ker φ
  have hI : I ≠ ⊤ := RingHom.ker_ne_top φ
  have : Nontrivial (R₀ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (R₀ ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨hnoeth, _, _, hcomplete⟩ := quotient_complete_local R₀ I hI
  let eqR : (R₀ ⧸ I) ≃+* R := RingHom.quotientKerEquivRange φ
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv (R₀ ⧸ I) eqR
  have : IsLocalRing R := eqR.isLocalRing
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal eqR]
    exact (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal (R₀ ⧸ I)) eqR).mpr
      hcomplete
  have hRB : Algebra.FiniteType R B := by
    apply (RingHom.finiteType_algebraMap).mp
    apply RingHom.FiniteType.of_comp_finiteType (f := φ.rangeRestrict)
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  obtain ⟨S, hreg, hScomp, hSfin, hSmax, eres, hres, hseries⟩ :=
    IsLocalRing.complete_local_domain_finite_over_regular R
  set_option maxRecDepth 1000 in
  have hfieldSeries : ∃ (k : Type u) (hk : Field k), letI := hk
      ∃ n : ℕ, Nonempty (S ≃+* MvPowerSeries (Fin n) k) := by
    rcases hseries with hfield | ⟨Λ, hΛ, d, q, hcohen, ⟨e⟩⟩
    · exact hfield
    · let := hΛ
      let inc : Λ →+* MvPowerSeries (Fin d) Λ := MvPowerSeries.C
      have hinj : Function.Injective inc := MvPowerSeries.C_injective
      let back : Λ →+* S := e.symm.toRingHom.comp inc
      have hback : Function.Injective back := e.symm.injective.comp hinj
      have : CharP Λ p := back.charP hback p
      obtain ⟨hq, hdom, hdvr, hmax, _⟩ := hcohen
      let := hdom
      let := hdvr
      have hqunit : ¬ IsUnit (q : Λ) := by
        have hmem : (q : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
          rw [hmax]
          exact Ideal.subset_span (by simp)
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmem
      have hpq : p ∣ q := by
        by_contra h
        exact hqunit ((CharP.isUnit_natCast_iff (R := Λ) (p := p) (Fact.out : p.Prime)).mpr h)
      have hqzero : (q : Λ) = 0 := (CharP.cast_eq_zero_iff Λ p q).mpr hpq
      have hbot : IsLocalRing.maximalIdeal Λ = ⊥ := by rw [hmax, hqzero, Ideal.span_singleton_zero]
      exact (IsDiscreteValuationRing.not_a_field Λ hbot).elim
  obtain ⟨k, hk, n, ⟨es⟩⟩ := hfieldSeries
  let := hk
  have hkp : CharP k p :=
    (es.symm.toRingHom.comp MvPowerSeries.C).charP
      (es.symm.injective.comp MvPowerSeries.C_injective) p
  let hSC : S →+* B := R.subtype.comp S.subtype
  have hSFT : S.subtype.FiniteType := by
    let := hSfin
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  have hSBT : hSC.FiniteType := ((RingHom.finiteType_algebraMap).mpr hRB).comp hSFT
  let : Algebra S B := hSC.toAlgebra
  have : Algebra.FiniteType S B := hSBT
  obtain ⟨m, y, B0, hinj, hinc, hfin, g, hg, haway⟩ :=
    Algebra.FiniteType.exists_finite_subalgebra_away S B
      (show Function.Injective hSC from Subtype.val_injective.comp Subtype.val_injective)
  let ψ := MvPolynomial.aeval (R := S) y
  let C : Subring B := ψ.range.toSubring
  let : Algebra S C := inferInstanceAs (Algebra S ψ.range)
  have : IsScalarTower S C B := inferInstanceAs (IsScalarTower S ψ.range B)
  have hCB : Algebra.FiniteType C B :=
    Algebra.FiniteType.of_restrictScalars_finiteType S C B
  let ep : MvPolynomial (Fin m) S ≃+* C :=
    RingEquiv.ofBijective ψ.toRingHom.rangeRestrict
      ⟨fun a b hab ↦ hinj (congrArg Subtype.val hab), ψ.toRingHom.rangeRestrict_surjective⟩
  let eC : C ≃+* MvPolynomial (Fin m) (MvPowerSeries (Fin n) k) :=
    ep.symm.trans (MvPolynomial.mapEquiv (Fin m) es)
  let : Algebra C M := ((algebraMap B M).comp C.subtype).toAlgebra
  have : IsScalarTower C B M := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : FaithfulSMul C M :=
    (faithfulSMul_iff_algebraMap_injective C M).mpr
      ((IsFractionRing.injective B M).comp Subtype.val_injective)
  let : Algebra C B0 := (Subalgebra.inclusion hinc).toRingHom.toAlgebra
  let : SMul C B0 := (inferInstance : Algebra C B0).toSMul
  let : Module.Finite C B0 := hfin
  let : Algebra B0 M := ((algebraMap B M).comp B0.val.toRingHom).toAlgebra
  let : SMul B0 M := (inferInstance : Algebra B0 M).toSMul
  have : IsScalarTower C B0 M := ⟨fun c b z ↦ by
    change algebraMap B M ((c : B) * (b : B)) * z =
      algebraMap B M (c : B) * (algebraMap B M (b : B) * z)
    rw [map_mul, mul_assoc]⟩
  have : FaithfulSMul B0 M :=
    (faithfulSMul_iff_algebraMap_injective B0 M).mpr
      ((IsFractionRing.injective B M).comp Subtype.val_injective)
  have hden : ∀ b : B, ∃ b0 : B0, ∃ j : ℕ,
      (b0 : B) = (algebraMap S B g) ^ j * b :=
    (IsLocalization.Away.map_surjective_iff
      (Localization.Away (algebraMap S B0 g))
      (Localization.Away (B0.val (algebraMap S B0 g)))
      B0.val.toRingHom (algebraMap S B0 g)).mp
      haway.2
  have hgB : algebraMap S B g ≠ 0 := by
    intro h
    apply hg
    exact (Subtype.val_injective.comp Subtype.val_injective)
      (h.trans (map_zero hSC).symm)
  have hgM : algebraMap B M (algebraMap S B g) ≠ 0 := by
    intro h
    exact hgB ((IsFractionRing.injective B M) (h.trans (map_zero _).symm))
  have : IsFractionRing B0 M := by
    apply IsFractionRing.of_field
    intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective B z
    obtain ⟨a0, i, ha0⟩ := hden a
    obtain ⟨b0, j, hb0⟩ := hden b
    refine ⟨a0 * (algebraMap S B0 g) ^ j, b0 * (algebraMap S B0 g) ^ i, ?_⟩
    rw [← hz]
    change algebraMap B M a / algebraMap B M b =
      algebraMap B M ((a0 : B) * (algebraMap S B g) ^ j) /
        algebraMap B M ((b0 : B) * (algebraMap S B g) ^ i)
    rw [ha0, hb0]
    simp only [map_mul, map_pow]
    field_simp
  have : Algebra.IsAlgebraic C M :=
    (IsFractionRing.isAlgebraic_iff' C B0 M).mp inferInstance
  let : Algebra (FractionRing C) M := FractionRing.liftAlgebra C M
  have : IsScalarTower C (FractionRing C) M := FractionRing.isScalarTower_liftAlgebra C M
  have : Algebra.IsAlgebraic (FractionRing C) M :=
    (IsFractionRing.comap_isAlgebraic_iff (A := C) (K := FractionRing C)
      (C := M)).mp inferInstance
  have : Algebra.EssFiniteType B M := Algebra.EssFiniteType.of_isLocalization M (nonZeroDivisors B)
  have : Algebra.EssFiniteType C B := by let := hCB; infer_instance
  have : Algebra.EssFiniteType C M := Algebra.EssFiniteType.comp C B M
  have : Algebra.EssFiniteType (FractionRing C) M :=
    Algebra.EssFiniteType.of_comp C (FractionRing C) M
  have : FiniteDimensional (FractionRing C) M :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  exact ⟨C, hCB, k, hk, n, m, hkp, ⟨eC⟩, FractionRing C, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Derivation
