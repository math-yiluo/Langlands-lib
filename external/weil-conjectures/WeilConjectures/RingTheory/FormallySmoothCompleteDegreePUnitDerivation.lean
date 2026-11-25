/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.Derivation.DetectNonPthPower
import WeilConjectures.RingTheory.Derivation.FormallySmoothAdicExtension
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.RingTheory.FormallySmoothAdicBaseChange
import WeilConjectures.RingTheory.Derivation.Localization

/-!
# A degree-p presentation with a unit derivation

Source: Stacks Project, More on Algebra, Proposition 07PM, last two paragraphs.
(blueprint: lem-weil-pbc-fs-complete-degree-p-unit-derivation)
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem degree_p_coefficient
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [Module.Finite F E] [IsPurelyInseparable F E]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hdegree : Module.finrank F E = p) :
    ∃ g : F, (¬ ∃ x : F, x ^ p = g) ∧
      Nonempty ((Polynomial F ⧸ Ideal.span {Polynomial.X ^ p - Polynomial.C g}) ≃ₐ[F] E) := by
  classical
  have : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  have hne : (⊥ : IntermediateField F E) ≠ ⊤ := by
    intro h
    have := IntermediateField.bot_eq_top_iff_finrank_eq_one.mp h
    rw [hdegree] at this
    exact (Fact.out : p.Prime).ne_one this
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ (⊥ : IntermediateField F E) := by
    by_contra h
    apply hne
    apply top_unique
    intro x _
    exact not_not.mp (not_exists.mp h x)
  have hex := IsPurelyInseparable.pow_mem F p x
  let r := Nat.find hex
  have hr : x ^ p ^ r ∈ (⊥ : IntermediateField F E) := Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := by omega
    simp only [this, pow_zero, pow_one] at hr
    exact hx hr
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  let a := x ^ p ^ k
  have ha : a ∉ (⊥ : IntermediateField F E) := by
    exact Nat.find_min hex (by omega)
  have hap : a ^ p ∈ (⊥ : IntermediateField F E) := by
    simpa [a, hk, pow_succ, pow_mul] using hr
  obtain ⟨g, hg⟩ := hap
  change algebraMap F E g = a ^ p at hg
  have hnot : ¬ ∃ c : F, c ^ p = g := by
    rintro ⟨c, hc⟩
    have he : (algebraMap F E c) ^ p = a ^ p := by rw [← map_pow, hc, hg]
    exact ha ⟨c, frobenius_inj E p he⟩
  have hmin : minpoly F a = Polynomial.X ^ p - Polynomial.C g := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · exact X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) (fun c hc ↦ hnot ⟨c, hc⟩)
    · simp [hg]
    · exact Polynomial.monic_X_pow_sub_C g (Fact.out : p.Prime).ne_zero
  let := IntermediateField.isSimpleOrder_of_finrank_prime F E
    (hdegree.symm ▸ (Fact.out : p.Prime))
  have htop : IntermediateField.adjoin F ({a} : Set E) = ⊤ := by
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F ({a} : Set E)) with h | h
    · exact False.elim (ha (h ▸ IntermediateField.subset_adjoin F _ (Set.mem_singleton a)))
    · exact h
  have halg : Algebra.adjoin F ({a} : Set E) = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic a)).mp htop
  have e := (minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := F) a)).trans
    ((Subalgebra.equivOfEq _ _ halg).trans Subalgebra.topEquiv)
  rw [hmin] at e
  exact ⟨g, hnot, ⟨e⟩⟩

private noncomputable def polynomial_tensor_equiv
    (A : Type u) (M : Type v) (C : Type w)
    [CommRing A] [CommRing M] [CommRing C] [Algebra A M] [Algebra A C] :
    TensorProduct A (Polynomial M) C ≃ₐ[M] Polynomial (TensorProduct A M C) :=
  (TensorProduct.cancelBaseChange A M M (Polynomial M) C).symm.trans
    ((TensorProduct.comm M (Polynomial M) (TensorProduct A M C)).trans
      ((TensorProduct.congr (AlgEquiv.refl : TensorProduct A M C ≃ₐ[M] TensorProduct A M C)
        (MvPolynomial.uniqueAlgEquiv M PUnit.{1}).symm).trans
        (((MvPolynomial.algebraTensorAlgEquiv M (TensorProduct A M C)).restrictScalars M).trans
          ((MvPolynomial.uniqueAlgEquiv (TensorProduct A M C) PUnit.{1}).restrictScalars M))))

private theorem polynomial_tensor_relation
    (A : Type u) (M : Type v) (C : Type w)
    [CommRing A] [CommRing M] [CommRing C] [Algebra A M] [Algebra A C]
    (p : ℕ) (g : M) :
    polynomial_tensor_equiv A M C
      ((algebraMap (Polynomial M) (TensorProduct A (Polynomial M) C))
        (Polynomial.X ^ p - Polynomial.C g)) =
      Polynomial.X ^ p - Polynomial.C (algebraMap M (TensorProduct A M C) g) := by
  simp [polynomial_tensor_equiv, ← TensorProduct.one_def,
    MvPolynomial.uniqueAlgEquiv, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    TensorProduct.map_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]

private theorem tensor_degree_p_presentation
    (A : Type u) (M : Type v) (C : Type w) (L : Type*)
    [CommRing A] [CommRing M] [CommRing C] [CommRing L]
    [Algebra A M] [Algebra A C] [Algebra M L] [Algebra A L] [IsScalarTower A M L]
    (p : ℕ) (g : M)
    (e : (Polynomial M ⧸ Ideal.span {Polynomial.X ^ p - Polynomial.C g}) ≃ₐ[M] L) :
    Nonempty ((Polynomial (TensorProduct A M C) ⧸
      Ideal.span {Polynomial.X ^ p -
        Polynomial.C (algebraMap M (TensorProduct A M C) g)}) ≃+* TensorProduct A L C) := by
  let I : Ideal (Polynomial M) := Ideal.span {Polynomial.X ^ p - Polynomial.C g}
  let eP := polynomial_tensor_equiv A M C
  have hI : (I.map (algebraMap (Polynomial M) (TensorProduct A (Polynomial M) C))).map
      eP.toRingHom =
        Ideal.span {Polynomial.X ^ p - Polynomial.C (algebraMap M (TensorProduct A M C) g)} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    rw [show eP.toRingHom ((algebraMap (Polynomial M) (TensorProduct A (Polynomial M) C))
      (Polynomial.X ^ p - Polynomial.C g)) = _ from
      polynomial_tensor_relation A M C p g]
  let eQ := Ideal.quotientEquiv _ _ eP.toRingEquiv hI.symm
  let eT := TensorProduct.quotientTensorEquiv (R := A) A C (Polynomial M) I
  let eL := TensorProduct.congr (e.restrictScalars A) (AlgEquiv.refl : C ≃ₐ[A] C)
  exact ⟨eQ.symm.trans (eT.symm.toRingEquiv.trans eL.toRingEquiv)⟩

private theorem finite_fraction_model
    (A : Type u) (K : Type u) (M : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field M]
    [Algebra A K] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
    [IsFractionRing A K] [Module.Finite K M] :
    ∃ B : Subalgebra A M, Module.Finite A B ∧ IsFractionRing B M := by
  classical
  obtain ⟨t, e, he⟩ := FiniteDimensional.exists_is_basis_integral A K M
  let B := Algebra.adjoin A (Set.range e)
  have hB : Module.Finite A B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range e)
      (by rintro _ ⟨i, rfl⟩; exact he i)
  have hfrac (z : M) : ∃ b s : B, (s : M) ≠ 0 ∧ z = (b : M) / (s : M) := by
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors A) (fun i ↦ e.repr z i)
    choose a ha using hd
    have hd0 : (d : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
    have hdm : algebraMap A M d ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A K M]
      exact (map_ne_zero (algebraMap K M)).mpr
        ((map_ne_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mpr hd0)
    have hdz : (d : A) • z ∈ B := by
      rw [← e.sum_repr z, Finset.smul_sum]
      apply B.sum_mem
      intro i _
      rw [← smul_assoc, ← ha i, algebraMap_smul]
      exact B.smul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (a i)
    refine ⟨⟨(d : A) • z, hdz⟩, ⟨algebraMap A M d, B.algebraMap_mem d⟩, hdm, ?_⟩
    change z = ((d : A) • z) / algebraMap A M d
    rw [Algebra.smul_def, mul_div_cancel_left₀ _ hdm]
  refine ⟨B, hB, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s
    apply isUnit_iff_ne_zero.mpr
    exact fun h ↦ (mem_nonZeroDivisors_iff_ne_zero.mp s.property) (Subtype.ext h)
  · intro z
    obtain ⟨b, s, hs, hz⟩ := hfrac z
    refine ⟨⟨b, ⟨s, mem_nonZeroDivisors_iff_ne_zero.mpr ?_⟩⟩, ?_⟩
    · exact fun h ↦ hs (congrArg Subtype.val h)
    · change z * (s : M) = (b : M)
      rw [hz, div_mul_cancel₀ _ hs]
  · intro x y h
    exact ⟨1, by simpa using (Subtype.ext h : x = y)⟩

private theorem localized_derivation_extension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (W : Submonoid R) [IsLocalization W S] (D : Derivation ℤ R R) :
    ∃ Dw : Derivation ℤ S S,
      ∀ a, Dw (algebraMap R S a) = algebraMap R S (D a) := by
  let ψ : S →+* S := RingHom.id _
  let δ : R →+ S := (algebraMap R S).toAddMonoidHom.comp
    D.toLinearMap.toAddMonoidHom
  have hδ : ∀ x y, δ (x * y) = ψ (algebraMap R S x) • δ y +
      ψ (algebraMap R S y) • δ x := by
    intro x y
    simp only [δ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      RingHom.toAddMonoidHom_eq_coe, ψ, RingHom.id_apply, smul_eq_mul]
    change algebraMap R S (D (x * y)) = _
    rw [D.leibniz]
    simp [smul_eq_mul]
  let d : S →+ S := IsLocalization.extendDerivation W ψ δ hδ
  let Dw : Derivation ℤ S S := Derivation.mk' d.toIntLinearMap (by
    intro x y
    simpa [d, ψ, smul_eq_mul] using IsLocalization.extendDerivation_mul W ψ δ hδ x y)
  refine ⟨Dw, ?_⟩
  intro a
  exact IsLocalization.extendDerivation_algebraMap W ψ δ hδ a

private noncomputable def transport_derivation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Derivation.mk'
    ((e.toAddEquiv.toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom).comp
      e.symm.toAddEquiv.toAddMonoidHom).toIntLinearMap (by
        intro a b
        simp [D.leibniz, smul_eq_mul])

private theorem transport_derivation_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (D : Derivation ℤ R R) (x : R) :
    transport_derivation e D (e x) = e (D x) := by
  simp [transport_derivation]

/-- A non-pth-power coefficient in a finite purely inseparable extension of the fraction
field has a unit derivative in the generic fibre of a formally smooth complete algebra.
Source: Stacks Project, More on Algebra, Proposition 07PM, final two paragraphs.
(blueprint: lem-weil-pbc-fs-complete-degree-p-unit-derivation)

Proof: Mathlib supplies a finite K-basis of M whose vectors are integral over A,
by scaling an arbitrary basis by a nonzero common denominator. The A-subalgebra B
generated by these vectors is finite over A and has fraction field M, by clearing
the finitely many denominators in any K-linear combination. Write g = c/e in Frac(B) with e nonzero.
Put f0 = e^p g = e^(p-1)c in B. A pth root of f0 in M, divided by e, would be a
pth root of g, so f0 is not a pth power. Lemma 07PH gives an absolute derivation D0
of B with D0(f0) nonzero. Base change 07EG makes C tensor_A B formally smooth over B
for the extended maximal ideal of C. This tensor product is finite over C; 00MA and
change of scalars for adic completeness make it complete for that extended ideal.
Extend D0 by 07PL. Localize at B minus zero; localization base change and tensor
cancellation identify the result with M tensor_A C, and 07PE extends the derivation.
Its value on f0 is the image of D0(f0), a unit since D0(f0) is nonzero in M.
In characteristic p the derivative of e^p is zero. Thus the derivative of g is
(e^p)^(-1) times that unit and is a unit. If the generic fibre is the zero ring,
the unique derivation also has unit value; no nontriviality assumption is used. -/
private theorem exists_unit_derivation_generic_coefficient_of_formallySmoothAdic
    (A : Type u) (C : Type v) (K : Type u) (M : Type w)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [Field K] [Field M] [Algebra A C] [Algebra A K] [Algebra K M] [Algebra A M]
    [IsScalarTower A K M] [IsFractionRing A K] [Module.Finite K M]
    [IsPurelyInseparable K M] [IsLocalHom (algebraMap A C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hfs : FormallySmoothAdic A C (IsLocalRing.maximalIdeal C))
    (g : M) (hg : ¬ ∃ x : M, x ^ p = g) :
    ∃ D : Derivation ℤ (TensorProduct A M C) (TensorProduct A M C),
      IsUnit (D (algebraMap M (TensorProduct A M C) g)) := by
  classical
  have : CharP M p := (Algebra.charP_iff K M p).mp inferInstance
  obtain ⟨B, hB, hfrac⟩ := finite_fraction_model A K M
  let : Module.Finite A B := hB
  let : IsFractionRing B M := hfrac
  have : CharP B p := (algebraMap B M).charP (IsFractionRing.injective B M) p
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors B) g
  have hs : (s : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  have hsm : algebraMap B M (s : B) ≠ 0 :=
    (map_ne_zero_iff (algebraMap B M) (IsFractionRing.injective B M)).mpr hs
  let f : B := (s : B) ^ (p - 1) * c
  have hf : algebraMap B M f = (algebraMap B M (s : B)) ^ p * g := by
    change (s : M) ^ (p - 1) * (c : M) = (s : M) ^ p * g
    change g * (s : M) = (c : M) at hcs
    rw [← hcs]
    have hp : p - 1 + 1 = p := by have := (Fact.out : p.Prime).two_le; omega
    have hpow := pow_succ (s : M) (p - 1)
    rw [hp] at hpow
    rw [hpow]
    ring
  have hfnot : ¬ ∃ x : M, x ^ p = algebraMap B M f := by
    rintro ⟨x, hx⟩
    apply hg
    refine ⟨x / algebraMap B M (s : B), ?_⟩
    rw [div_pow, hx, hf, mul_div_cancel_left₀ _ (pow_ne_zero _ hsm)]
  obtain ⟨D0, hD0⟩ := Derivation.exists_apply_ne_zero_of_not_pth_power p B M A f hfnot
  let T := TensorProduct A C B
  let : Algebra B T := TensorProduct.rightAlgebra
  let n := (IsLocalRing.maximalIdeal C).map (algebraMap C T)
  have : IsAdicComplete (IsLocalRing.maximalIdeal C) T :=
    finite_module_complete_over_complete_noetherian C (IsLocalRing.maximalIdeal C) T
  have : IsAdicComplete n T := (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance
  have hT : FormallySmoothAdic B T n := formallySmoothAdic_tensorProduct A C B _ hfs
  obtain ⟨DT, hDT⟩ := Derivation.exists_extension_of_formallySmoothAdic n hT D0
  let W := Algebra.algebraMapSubmonoid T (nonZeroDivisors B)
  let U := TensorProduct B T M
  have : IsLocalization W U := inferInstance
  obtain ⟨DU, hDU⟩ := localized_derivation_extension (S := U) W DT
  let eR := (TensorProduct.comm B T M).trans
    ((TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[B] M)
      (TensorProduct.commRight A B C).symm).trans
      (TensorProduct.cancelBaseChange A B B M C))
  let E := eR.toRingEquiv
  let D := transport_derivation E DU
  have hext (b : B) :
      D (algebraMap M (TensorProduct A M C) (algebraMap B M b)) =
        algebraMap M (TensorProduct A M C) (algebraMap B M (D0 b)) := by
    have he (b : B) : E (algebraMap T U (algebraMap B T b)) =
        algebraMap M (TensorProduct A M C) (algebraMap B M b) := by
      simp [E, eR, T, U, Algebra.smul_def, TensorProduct.algebraMap_apply,
        TensorProduct.right_algebraMap_apply]
    rw [← he, transport_derivation_apply, hDU, hDT, he]
  have hunit : IsUnit (D (algebraMap M (TensorProduct A M C) (algebraMap B M f))) := by
    rw [hext]
    exact (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff (algebraMap B M) (IsFractionRing.injective B M)).mpr hD0)).map _
  have hpzero : D ((algebraMap M (TensorProduct A M C) (algebraMap B M (s : B))) ^ p) = 0 := by
    rw [D.leibniz_pow]
    have hpcast : (p : TensorProduct A M C) = 0 := by
      rw [← map_natCast (algebraMap M (TensorProduct A M C)), CharP.cast_eq_zero M p,
        map_zero]
    simp [nsmul_eq_mul, hpcast]
  refine ⟨D, ?_⟩
  have hproduct : D (algebraMap M (TensorProduct A M C) (algebraMap B M f)) =
      (algebraMap M (TensorProduct A M C) (algebraMap B M (s : B))) ^ p *
        D (algebraMap M (TensorProduct A M C) g) := by
    rw [hf, map_mul, map_pow, D.leibniz, hpzero, smul_zero, add_zero, smul_eq_mul]
  rw [hproduct] at hunit
  exact isUnit_of_mul_isUnit_right hunit


attribute [-instance] IntermediateField.module' in
/-- A degree-p purely inseparable base change of a formally smooth complete algebra
has a polynomial quotient presentation whose constant term admits a unit derivative.
Source: Stacks Project, More on Algebra, Proposition 07PM, final paragraph.
(blueprint: lem-weil-pbc-fs-complete-degree-p-unit-derivation)

Proof: Fields 09HI presents L/M as M[z]/(z^p-g), with g not a pth power in M.
Choose a finite K-basis of M. Each basis vector has a p-power in K. Multiplying
by a nonzero denominator in A puts that p-power in A, hence makes the rescaled
vector integral. Adjoining these integral vectors gives a finite A-subalgebra A'
of M with fraction field M. Write g = c/e in that fraction field and replace g
by e^p g = e^(p-1)c and its root beta by e beta. Thus f0 lies in A', is not a
pth power in M, and L = M[z]/(z^p-f0). By 07PH choose D0 : A' -> A' nonzero
on f0; A' is finite type over the complete Noetherian local A. Base change 07EG
makes C tensor_A A' formally smooth over A' for the extended maximal ideal of C.
It is finite over C, so 00MA makes it complete for that ideal. Lemma 07PL extends
D0 to this tensor product. Localize at the nonzero elements of A' and use tensor
associativity to identify the resulting ring with C tensor_A M. The localization
formula for derivations produces D, and its value on the image of f0 equals the
image of D0(f0). This is a unit, since D0(f0) is nonzero in M. Tensor the quotient
presentation of L with C tensor_A M; polynomial base change and quotient base
change identify the result with (C tensor_A M)[z]/(z^p-f0). Tensor commutativity
transports both the presentation and the derivation to M tensor_A C. This gives
the claimed f, D and ring isomorphism. Regularity is not needed in this construction.
If the generic fibre is zero, its unique element is a unit and all the displayed
rings are zero; the same construction applies. Prime p includes p = 2, the
coefficient field can be imperfect, and no positive number of variables is needed. -/
theorem exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic
    (A : Type u) (C : Type v) (K : Type u) (L : Type w)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [Module.Finite K L]
    [IsPurelyInseparable K L]
    [IsLocalHom (algebraMap A C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : IntermediateField K L) [Algebra A M] [IsScalarTower A K M]
    (hdegree : Module.finrank M L = p)
    (hfs : FormallySmoothAdic A C (IsLocalRing.maximalIdeal C)) :
    ∃ (f : TensorProduct A M C) (D : Derivation ℤ (TensorProduct A M C)
      (TensorProduct A M C)), IsUnit (D f) ∧
      Nonempty ((Polynomial (TensorProduct A M C) ⧸
        Ideal.span {Polynomial.X ^ p - Polynomial.C f}) ≃+* TensorProduct A L C) := by
  classical
  have : IsScalarTower A M L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K M L])
  have : CharP M p := (Algebra.charP_iff K M p).mp inferInstance
  obtain ⟨g, hg, ⟨e⟩⟩ := degree_p_coefficient M L p hdegree
  obtain ⟨D, hD⟩ := exists_unit_derivation_generic_coefficient_of_formallySmoothAdic
    A C K M p hfs g hg
  refine ⟨algebraMap M (TensorProduct A M C) g, D, hD, ?_⟩
  exact tensor_degree_p_presentation A M C L p g e

end Algebra
