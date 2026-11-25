/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import WeilConjectures.Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Étaleness over the ring of invariants of a finite group

Let a finite group `G` act on a commutative ring `A`, with ring of invariants `R` (an
`Algebra.IsInvariant R A G` extension). If `A` is reduced with finitely many minimal primes, `A`
is étale over `R` at every minimal prime (`Algebra.IsInvariant.isEtaleAt_of_mem_minimalPrimes`).
The essential point is the separability of the residue field extension `κ(Q) / κ(P)` at a
minimal prime `Q` over `P` (`Algebra.IsInvariant.isSeparable_of_mem_minimalPrimes`): the elements
of `κ(Q)` fixed by the stabilizer of `Q` come from `κ(P)`, by an orbit sum of an element vanishing
at the other minimal primes (`Algebra.IsInvariant.exists_algebraMap_sub_algebraMap_mul_mem`),
and `κ(Q)` is Galois over this fixed field.

Consequently a nonzero reduced noetherian `A`, finitely presented over `R`, has an invariant `c`,
not nilpotent, with `D(c)` contained in the étale locus
(`Algebra.IsInvariant.exists_basicOpen_subset_etaleLocus`). For a finitely generated algebra over
a field with an automorphism of finite order this gives a finitely generated subalgebra of
invariants over which `A` is finite and generically étale
(`Algebra.IsInvariant.exists_subalgebra_basicOpen_subset_etaleLocus`). This is the algebraic
part of the existence of generic quotients by finite groups (SGA 1, Exposé V, Prop. 1.1 and
Cor. 2.4).
-/

@[expose] public section

open scoped Pointwise

namespace Algebra.IsInvariant

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G A] [SMulCommClass G R A] [Algebra.IsInvariant R A G]

/-! ### Orbit sums and the stabilizer of a minimal prime -/

/-- The sum of the elements of the orbit of `b`. -/
noncomputable def orbitSum (b : A) : A :=
  ∑ c ∈ (Set.finite_range (fun g : G ↦ g • b)).toFinset, c

lemma smul_orbitSum (b : A) (g : G) : g • orbitSum (G := G) b = orbitSum (G := G) b := by
  classical
  rw [orbitSum, Finset.smul_sum]
  refine Finset.sum_nbij' (g • ·) (g⁻¹ • ·) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl) <;>
    simp [Set.mem_range, smul_smul]

lemma orbitSum_sub_mem {q : Ideal A} (b : A) (hb : ∀ g : G, g • b ≠ b → g • b ∈ q) :
    orbitSum (G := G) b - b ∈ q := by
  classical
  have hmem : b ∈ (Set.finite_range (fun g : G ↦ g • b)).toFinset := by
    simpa using ⟨1, one_smul G b⟩
  rw [orbitSum, ← Finset.add_sum_erase _ _ hmem, add_sub_cancel_left]
  refine q.sum_mem fun c hc ↦ ?_
  obtain ⟨hcb, hc⟩ := Finset.mem_erase.1 hc
  obtain ⟨g, rfl⟩ := (Set.Finite.mem_toFinset _).1 hc
  exact hb g hcb

variable (G) in
/-- For a minimal prime `q` of a ring with finitely many minimal primes, there is an element
`t ∉ q`, fixed by the stabilizer of `q`, lying in every other minimal prime. -/
lemma exists_smul_eq_notMem_mem_minimalPrimes (q : Ideal A) (hq : q ∈ minimalPrimes A)
    (hfin : (minimalPrimes A).Finite) :
    ∃ t : A, (∀ h ∈ MulAction.stabilizer G q, h • t = t) ∧ t ∉ q ∧
      ∀ q' ∈ minimalPrimes A, q' ≠ q → t ∈ q' := by
  classical
  have hqp : q.IsPrime := hq.1.1
  obtain ⟨_⟩ := nonempty_fintype G
  let S : Finset (Ideal A) := hfin.toFinset.erase q
  have hS : ¬ S.inf _root_.id ≤ q := by
    rw [Ideal.IsPrime.inf_le' hqp]
    rintro ⟨q', hq'S, hle⟩
    obtain ⟨hne, hq'⟩ := Finset.mem_erase.1 hq'S
    rw [Set.Finite.mem_toFinset] at hq'
    exact hne (le_antisymm hle (hq.2 hq'.1 hle))
  obtain ⟨t₀, ht₀S, ht₀q⟩ := IsConcreteLE.not_le_iff_exists.1 hS
  have ht₀ : ∀ q' ∈ minimalPrimes A, q' ≠ q → t₀ ∈ q' := fun q' hq' hne ↦
    (Finset.inf_le (f := _root_.id) (Finset.mem_erase.2 ⟨hne, (Set.Finite.mem_toFinset _).2 hq'⟩) :
      S.inf _root_.id ≤ q') ht₀S
  refine ⟨∏ h : MulAction.stabilizer G q, (h : G) • t₀, fun h hh ↦ ?_, ?_, fun q' hq' hne ↦ ?_⟩
  · rw [Finset.smul_prod']
    exact Finset.prod_nbij' (fun x ↦ ⟨h, hh⟩ * x) (fun x ↦ ⟨h, hh⟩⁻¹ * x) (by simp) (by simp)
      (by simp) (by simp) (fun x _ ↦ by simp [mul_smul])
  · refine hqp.prod_mem_iff.not.2 ?_
    simp only [Finset.mem_univ, true_and, not_exists]
    intro h
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := (h : G)⁻¹), inv_smul_smul]
    have : (h : G)⁻¹ • q = q := by
      rw [inv_smul_eq_iff]; exact h.2.symm
    rwa [this]
  · exact q'.prod_mem (Finset.mem_univ 1) (by simpa using ht₀ q' hq' hne)

omit [Finite G] [SMulCommClass G R A] [Algebra.IsInvariant R A G] in
lemma smul_mem_minimalPrimes {q : Ideal A} (hq : q ∈ minimalPrimes A) (g : G) :
    g • q ∈ minimalPrimes A := by
  have := hq.1.1
  refine ⟨⟨inferInstance, bot_le⟩, fun p hp hle ↦ ?_⟩
  have hp' := hp.1
  have h1 : g⁻¹ • p ≤ q := by
    rw [← inv_smul_smul g q]
    exact Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hle |>.trans le_rfl
  have h2 := hq.2 ⟨inferInstance, bot_le⟩ h1
  rw [← smul_inv_smul g p]
  exact Ideal.pointwise_smul_le_pointwise_smul_iff.mpr h2

omit [SMulCommClass G R A] in
/-- **Key lemma.** Let `q` be a minimal prime of a reduced ring `A` with finitely many minimal
primes and `a ∈ A` fixed modulo `q` by the stabilizer of `q`. Then `a` is a quotient of two
invariants modulo `q`. -/
lemma exists_algebraMap_sub_algebraMap_mul_mem [IsReduced A] (q : Ideal A)
    (hq : q ∈ minimalPrimes A) (hfin : (minimalPrimes A).Finite) (a : A)
    (ha : ∀ g ∈ MulAction.stabilizer G q, g • a - a ∈ q) :
    ∃ y z : R, algebraMap R A z ∉ q ∧ algebraMap R A y - algebraMap R A z * a ∈ q := by
  obtain ⟨t, htH, htq, htq'⟩ := exists_smul_eq_notMem_mem_minimalPrimes G q hq hfin
  have key : ∀ a : A, (∀ g ∈ MulAction.stabilizer G q, g • a - a ∈ q) →
      ∃ y : R, algebraMap R A y - t * a ∈ q := by
    intro a ha
    have hb : ∀ g : G, g • (t * a) ≠ t * a → g • (t * a) ∈ q := by
      intro g hg
      by_cases hgq : g ∈ MulAction.stabilizer G q
      · refine absurd ?_ hg
        rw [smul_mul', htH g hgq, ← sub_eq_zero, ← mul_sub]
        refine Ideal.eq_zero_of_forall_mem_minimalPrimes _ fun q' hq' ↦ ?_
        by_cases h : q' = q
        · exact h ▸ q.mul_mem_left _ (ha g hgq)
        · exact q'.mul_mem_right _ (htq' q' hq' h)
      · have hne : g⁻¹ • q ≠ q := by
          intro h
          apply hgq
          rw [MulAction.mem_stabilizer_iff, ← h, smul_inv_smul]
          exact h.symm
        have : t * a ∈ g⁻¹ • q :=
          (g⁻¹ • q).mul_mem_right _ (htq' _ (smul_mem_minimalPrimes hq _) hne)
        rwa [← Ideal.smul_mem_pointwise_smul_iff (a := g), smul_inv_smul] at this
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := R) (orbitSum (G := G) (t * a))
      (smul_orbitSum _)
    exact ⟨y, hy ▸ orbitSum_sub_mem _ hb⟩
  obtain ⟨y, hy⟩ := key a ha
  obtain ⟨z, hz⟩ := key 1 (fun g _ ↦ by simp)
  refine ⟨y, z, fun h ↦ htq ?_, ?_⟩
  · rw [mul_one] at hz
    simpa using q.sub_mem h hz
  · rw [mul_one] at hz
    have := q.sub_mem hy (q.mul_mem_right a hz)
    convert this using 1
    ring

/-! ### Separability of the residue field extensions at minimal primes -/

section Separable

variable (G) (P : Ideal R) (Q : Ideal A) [Q.IsPrime] [Q.LiesOver P]
  (K L : Type*) [Field K] [Field L]
  [Algebra (R ⧸ P) K] [Algebra (A ⧸ Q) L]
  [Algebra (R ⧸ P) L] [IsScalarTower (R ⧸ P) (A ⧸ Q) L]
  [Algebra K L] [IsScalarTower (R ⧸ P) K L]
  [IsFractionRing (R ⧸ P) K] [IsFractionRing (A ⧸ Q) L]

include G P in
/-- **Separability at a minimal prime.** For a minimal prime `Q` of a reduced ring `A` with
finitely many minimal primes, lying over `P` in the ring of invariants `R`, the extension
`Frac(A/Q) / Frac(R/P)` is separable: by the key lemma, the elements of `Frac(A/Q)` fixed by the
stabilizer of `Q` come from `Frac(R/P)`, and `Frac(A/Q)` is Galois over this fixed field. -/
theorem isSeparable_of_mem_minimalPrimes [IsReduced A] (hfin : (minimalPrimes A).Finite)
    (hQ : Q ∈ minimalPrimes A) : Algebra.IsSeparable K L := by
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under R Q
  have : Algebra.IsIntegral R A := Algebra.IsInvariant.isIntegral R A G
  let _ := MulSemiringAction.compHom L (IsFractionRing.stabilizerHom G P Q K L)
  have hfix : ∀ x : L, (∀ h : MulAction.stabilizer G Q, h • x = x) →
      x ∈ (algebraMap K L).fieldRange := by
    intro x hx
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A ⧸ Q) x
    obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R ⧸ P) y).exists_smul_eq_mul x hy
    replace ha : algebraMap (R ⧸ P) L a ≠ 0 := by
      rwa [Ne, IsScalarTower.algebraMap_apply (R ⧸ P) K L, FaithfulSMul.algebraMap_eq_zero_iff,
        FaithfulSMul.algebraMap_eq_zero_iff]
    replace hy : algebraMap (A ⧸ Q) L y ≠ 0 :=
      mt (FaithfulSMul.algebraMap_eq_zero_iff (A ⧸ Q) L).mp (nonZeroDivisors.ne_zero hy)
    replace h : algebraMap (A ⧸ Q) L x / algebraMap (A ⧸ Q) L y =
        algebraMap (A ⧸ Q) L b / algebraMap (R ⧸ P) L a := by
      rw [mul_comm, Algebra.smul_def, mul_comm] at h
      rw [div_eq_div_iff hy ha, ← map_mul, ← h, map_mul, ← IsScalarTower.algebraMap_apply]
    rw [h]
    refine Subfield.div_mem _ ?_ ⟨algebraMap (R ⧸ P) K a, by
      rw [← IsScalarTower.algebraMap_apply]⟩
    -- `b` is fixed by the stabilizer of `Q`
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb : ∀ g ∈ MulAction.stabilizer G Q, g • b - b ∈ Q := by
      intro g hg
      have := hx ⟨g, hg⟩
      change (IsFractionRing.stabilizerHom G P Q K L ⟨g, hg⟩) (_ / _) = _ / _ at this
      rw [h, map_div₀, IsFractionRing.stabilizerHom_apply_apply_mk,
        IsScalarTower.algebraMap_apply (R ⧸ P) K L, AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply, div_left_inj' ha] at this
      rw [← Ideal.Quotient.eq]
      exact IsFractionRing.injective (A ⧸ Q) L this
    obtain ⟨y, z, hz, hyz⟩ := exists_algebraMap_sub_algebraMap_mul_mem (R := R) Q hQ hfin b hb
    have hz' : algebraMap (R ⧸ P) L (Ideal.Quotient.mk P z) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply (R ⧸ P) (A ⧸ Q) L, Ne,
        FaithfulSMul.algebraMap_eq_zero_iff (A ⧸ Q) L, Ideal.Quotient.algebraMap_mk_of_liesOver,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hz
    have heq : algebraMap (A ⧸ Q) L (Ideal.Quotient.mk Q b) =
        algebraMap (R ⧸ P) L (Ideal.Quotient.mk P y) /
          algebraMap (R ⧸ P) L (Ideal.Quotient.mk P z) := by
      rw [eq_div_iff hz', IsScalarTower.algebraMap_apply (R ⧸ P) (A ⧸ Q) L,
        IsScalarTower.algebraMap_apply (R ⧸ P) (A ⧸ Q) L, ← map_mul,
        Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.algebraMap_mk_of_liesOver]
      congr 1
      rw [mul_comm, ← map_mul, Ideal.Quotient.eq, ← neg_sub]
      exact Q.neg_mem hyz
    rw [heq, IsScalarTower.algebraMap_apply (R ⧸ P) K L, IsScalarTower.algebraMap_apply (R ⧸ P) K L,
      ← map_div₀]
    exact RingHom.mem_fieldRange_self _ _
  let F := FixedPoints.subfield (MulAction.stabilizer G Q) L
  have hF : ∀ x : L, x ∈ F ↔ x ∈ (algebraMap K L).fieldRange := by
    refine fun x ↦ ⟨fun hx ↦ hfix x hx, ?_⟩
    rintro ⟨c, rfl⟩ h
    exact (IsFractionRing.stabilizerHom G P Q K L h).commutes c
  let e : K ≃+* F := RingEquiv.ofBijective
    ((algebraMap K L).codRestrict F fun c ↦ (hF _).2 ⟨c, rfl⟩)
    ⟨fun c d h ↦ (algebraMap K L).injective (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨c, hc⟩ := (hF x).1 x.2
      exact ⟨c, Subtype.ext hc⟩⟩
  refine Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl L) ?_
  ext x
  have : algebraMap K L (e.symm x) = x := congrArg Subtype.val (e.apply_symm_apply x)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.toRingHom_refl,
    RingHom.id_apply]
  exact this

end Separable

/-! ### Étaleness at the minimal primes -/

section Etale

variable (G)

include G in
/-- The prime of the invariants under a minimal prime is minimal. -/
lemma under_mem_minimalPrimes (hinj : Function.Injective (algebraMap R A)) {Q : Ideal A}
    (hQ : Q ∈ minimalPrimes A) : Q.under R ∈ minimalPrimes R := by
  have : Q.IsPrime := hQ.1.1
  have : Algebra.IsIntegral R A := Algebra.IsInvariant.isIntegral R A G
  refine ⟨⟨Ideal.IsPrime.under R Q, bot_le⟩, fun p' hp' hle ↦ ?_⟩
  have := hp'.1
  obtain ⟨Q₀, -, hQ₀, hQ₀p'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p' (⊥ : Ideal A)
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, ← map_zero (algebraMap R A)] at hx
      rw [hinj hx]; exact p'.zero_mem)
  obtain ⟨Q₁, hQ₁, hQ₁p, hQ₁e⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime (Q.under R) Q₀ (hQ₀p' ▸ hle)
  obtain ⟨g, hg⟩ := exists_smul_of_under_eq R A G Q Q₁ hQ₁e.symm
  have h₁ : g⁻¹ • Q₀ ≤ Q := by
    rw [← inv_smul_smul g Q, ← hg]
    exact Ideal.pointwise_smul_le_pointwise_smul_iff.mpr hQ₁
  have h₂ := hQ.2 ⟨Ideal.IsPrime.smul _, bot_le⟩ h₁
  calc Q.under R ≤ (g⁻¹ • Q₀).under R := Ideal.comap_mono h₂
    _ = Q₀.under R := Ideal.under_smul R Q₀ g⁻¹
    _ = p' := hQ₀p'

include G in
/-- **Étaleness at minimal primes.** A reduced ring `A` with finitely many minimal primes,
essentially of finite type over its ring of invariants `R` under a finite group, is étale over
`R` at every minimal prime. -/
theorem isEtaleAt_of_mem_minimalPrimes [IsReduced A] [EssFiniteType R A]
    (hfin : (minimalPrimes A).Finite) (hinj : Function.Injective (algebraMap R A)) {Q : Ideal A}
    (hQ : Q ∈ minimalPrimes A) :
    have := hQ.1.1
    Algebra.IsEtaleAt R Q := by
  have := hQ.1.1
  set P := Q.under R
  have hP : P ∈ minimalPrimes R := under_mem_minimalPrimes G hinj hQ
  have : P.IsPrime := hP.1.1
  have : Q.LiesOver P := ⟨rfl⟩
  have : IsReduced R := isReduced_of_injective _ hinj
  let := Localization.AtPrime.algebraOfLiesOver P Q
  let := (Localization.AtPrime.isField_of_mem_minimalPrimes hP).toField
  let := (Localization.AtPrime.isField_of_mem_minimalPrimes hQ).toField
  -- separability of the residue field extension
  let : Algebra (R ⧸ P) Q.ResidueField :=
    ((algebraMap P.ResidueField Q.ResidueField).comp (algebraMap (R ⧸ P) P.ResidueField)).toAlgebra
  have : IsScalarTower (R ⧸ P) P.ResidueField Q.ResidueField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (R ⧸ P) (A ⧸ Q) Q.ResidueField := .of_algebraMap_eq fun x ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap P.ResidueField Q.ResidueField (algebraMap (R ⧸ P) P.ResidueField
      (Ideal.Quotient.mk P r)) = _
    have h₁ : algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P r) =
        algebraMap R P.ResidueField r := by
      rw [IsScalarTower.algebraMap_apply R (R ⧸ P) P.ResidueField, Ideal.Quotient.algebraMap_eq]
    have h₂ : algebraMap (A ⧸ Q) Q.ResidueField (Ideal.Quotient.mk Q (algebraMap R A r)) =
        algebraMap A Q.ResidueField (algebraMap R A r) := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ Q) Q.ResidueField, Ideal.Quotient.algebraMap_eq]
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, h₁, h₂,
      ← IsScalarTower.algebraMap_apply R P.ResidueField Q.ResidueField,
      ← IsScalarTower.algebraMap_apply R A Q.ResidueField]
  have hsep : Algebra.IsSeparable P.ResidueField Q.ResidueField :=
    isSeparable_of_mem_minimalPrimes G P Q _ _ hfin hQ
  -- unramified at `Q`
  have : EssFiniteType R (Localization.AtPrime Q) := .comp R A _
  have : Algebra.IsUnramifiedAt R Q := by
    refine (Algebra.isUnramifiedAt_iff_map_eq R P Q).2 ⟨hsep, ?_⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    refine le_bot_iff.1 ?_
    rw [← IsLocalRing.maximalIdeal_eq_bot, ← Localization.AtPrime.map_eq_maximalIdeal,
      IsScalarTower.algebraMap_eq R A, ← Ideal.map_map]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)
  have : EssFiniteType (Localization.AtPrime P) (Localization.AtPrime Q) := .of_comp R _ _
  have : Algebra.FormallyEtale (Localization.AtPrime P) (Localization.AtPrime Q) :=
    .of_formallyUnramified_of_field _ _
  have : Algebra.FormallyEtale R (Localization.AtPrime P) := .of_isLocalization P.primeCompl
  exact Algebra.FormallyEtale.comp R (Localization.AtPrime P) (Localization.AtPrime Q)

include G in
/-- **Generic étaleness over the invariants.** A nonzero reduced noetherian ring `A`, finitely
presented over its ring of invariants `R` under a finite group, has an invariant `c`, not
nilpotent, such that `D(c)` lies in the étale locus of `A` over `R`. -/
theorem exists_basicOpen_subset_etaleLocus [IsReduced A] [IsNoetherianRing A] [Nontrivial A]
    [FinitePresentation R A] (hinj : Function.Injective (algebraMap R A)) :
    ∃ c : R, ¬ IsNilpotent (algebraMap R A c) ∧
      ↑(PrimeSpectrum.basicOpen (algebraMap R A c)) ⊆ Algebra.etaleLocus R A := by
  classical
  obtain ⟨_⟩ := nonempty_fintype G
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  obtain ⟨⟨Q₀, hQ₀⟩⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal A)) bot_ne_top
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1
    (Algebra.isOpen_etaleLocus (R := R) (A := A)).isClosed_compl
  have hIg : ∀ g : G, ¬ I ≤ g • Q₀ := by
    intro g hle
    have hmin := smul_mem_minimalPrimes hQ₀ g
    have : (⟨g • Q₀, hmin.1.1⟩ : PrimeSpectrum A) ∈ Algebra.etaleLocus R A :=
      isEtaleAt_of_mem_minimalPrimes G hfin hinj hmin
    have h' : (⟨g • Q₀, hmin.1.1⟩ : PrimeSpectrum A) ∈ (Algebra.etaleLocus R A)ᶜ := by
      rw [hI]; exact hle
    exact h' this
  have hav : ¬ ((I : Set A) ⊆
      ⋃ g ∈ (↑(Finset.univ : Finset G) : Set G), ((g • Q₀ : Ideal A) : Set A)) := by
    rw [Ideal.subset_union_prime (f := fun g : G ↦ g • Q₀) 1 1 (fun g _ _ _ ↦ hQ₀p.smul g)]
    rintro ⟨g, -, hg⟩
    exact hIg g hg
  obtain ⟨h, hhI, hhQ'⟩ := Set.not_subset.1 hav
  have hhQ : ∀ g : G, h ∉ g • Q₀ := fun g hg ↦
    hhQ' (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ g)) hg)
  obtain ⟨c, hc⟩ := Algebra.IsInvariant.isInvariant (A := R) (∏ g : G, g • h)
    (fun g ↦ Finset.smul_prod_perm h g)
  have hcQ : algebraMap R A c ∉ Q₀ := by
    rw [hc, hQ₀p.prod_mem_iff]
    rintro ⟨g, -, hg⟩
    apply hhQ g⁻¹
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := g), smul_inv_smul]
    exact hg
  have hcI : algebraMap R A c ∈ I := by
    rw [hc]
    exact I.prod_mem (Finset.mem_univ 1) (by simpa using hhI)
  refine ⟨c, fun ⟨n, hn⟩ ↦ hcQ (hQ₀p.mem_of_pow_mem n (hn ▸ Q₀.zero_mem)),
    fun x hx ↦ by_contra fun hxE ↦ ?_⟩
  have : x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by rw [← hI]; exact hxE
  exact hx (this hcI)

end Etale

end Algebra.IsInvariant

/-! ### Finitely generated algebras over a field -/

namespace Algebra.IsInvariant

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- **The ring-level generic quotient.** A nonzero reduced finitely generated `k`-algebra `A`
with an automorphism `σ` of finite order contains a finitely generated subalgebra `R` of
`σ`-invariants over which `A` is finite, and an element `c ∈ R`, not nilpotent, such that `D(c)`
lies in the étale locus of `A` over `R`. -/
theorem exists_subalgebra_basicOpen_subset_etaleLocus [Algebra.FiniteType k A] [IsReduced A]
    [Nontrivial A] (σ : A ≃ₐ[k] A) (hσ : IsOfFinOrder σ) :
    ∃ R : Subalgebra k A, (∀ x ∈ R, σ x = x) ∧ Algebra.FiniteType k R ∧ Module.Finite R A ∧
      ∃ c : R, ¬ IsNilpotent (c : A) ∧
        ↑(PrimeSpectrum.basicOpen (c : A)) ⊆ Algebra.etaleLocus R A := by
  let G := Subgroup.zpowers σ
  have : Finite G := finite_zpowers.2 hσ
  let R := FixedPoints.subalgebra k A G
  have : Algebra.IsInvariant R A G := ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
  have : Algebra.IsIntegral R A := Algebra.IsInvariant.isIntegral R A G
  have : Algebra.FiniteType R A := .of_restrictScalars_finiteType k R A
  have hfin : Module.Finite R A := Algebra.IsIntegral.finite
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hR : Algebra.FiniteType k R :=
    ⟨_root_.fg_of_fg_of_fg (A := k) (B := R) (C := A) Algebra.FiniteType.out
      (Module.Finite.fg_top) Subtype.val_injective⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Algebra.FinitePresentation R A := .of_finiteType.1 inferInstance
  obtain ⟨c, hc, hcE⟩ := exists_basicOpen_subset_etaleLocus G (R := R) Subtype.val_injective
  exact ⟨R, fun x hx ↦ hx ⟨σ, Subgroup.mem_zpowers σ⟩, hR, hfin, c, hc, hcE⟩

end Algebra.IsInvariant
