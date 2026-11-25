/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

import WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Verdier duality preserves finite-Tor constructible complexes

Source: blueprint main-20261015, chap-Construction-of-f,
`sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.md`, order 2414
(blueprint: lemma-verdier-duality-preserves-constructibility--1).

## Main declarations

* `finiteStageDualizingComplex`: the canonical ambient dualizing complex.
* `verdier_preservation_strata`: preservation with the specified uniform Tor bound.
* `verdier_preserves_boundedConstructible_finiteTor`: qualitative preservation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

-- Align the lifted coefficient Ring instance with the generic CommRing theorem.
attribute [local instance 2000] CommRing.toRing

private theorem boundedConstructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
    · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

private theorem preservation_of_perfectField
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] [PerfectField k]
    [HasInvertibleExponent A (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    (K : Etale.DerivedCategoryModule A X)
    (hc : Etale.DerivedCategory.isBoundedConstructible A X K)
    (ht : Etale.DerivedCategory.hasTorAmplitudeIn A X a b K) :
    Etale.DerivedCategory.isBoundedConstructible A X
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
          (Etale.dualizingComplex A f)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A X (-b - 2 * (d : ℤ)) (-a)
        (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
          (Etale.dualizingComplex A f)) := by
  obtain ⟨hbc, htor⟩ :=
    Etale.constructibleFiniteTor_and_torAmplitudeIn_verdierDual_of_perfectField A
      f d hd a b ((boundedConstructible_iff A X K).1 hc)
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 ht)
  exact ⟨(boundedConstructible_iff A X _).2 hbc.1,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 htor⟩

private theorem preservation_of_perfectField_ulift
    (R : Type u) [CommRing R] [Finite R]
    {k : Type u} [Field k] [PerfectField k]
    [HasInvertibleExponent (ULift.{u + 1, u} R) (Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a b : ℤ)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} R) X)
    (hc : Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} R) X K)
    (ht : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} R) X a b K) :
    Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} R) X
        (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).obj (op K)).obj
          (Etale.dualizingComplex (ULift.{u + 1, u} R) f)) ∧
      Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} R) X (-b - 2 * (d : ℤ)) (-a)
        (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).obj (op K)).obj
          (Etale.dualizingComplex (ULift.{u + 1, u} R) f)) := by
  exact preservation_of_perfectField (ULift.{u + 1, u} R) f d hd a b K hc ht

private theorem coefficient_invertibleExponent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    HasInvertibleExponent (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      (Spec (.of D.k)) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hlk : (l : D.k) ≠ 0 := fun hz ↦
    hl ((CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm.trans
      (ringChar.eq D.k D.p))
  have hu : IsUnit ((l ^ n : ℕ) : D.k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow n
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · exact ULift.down_injective hkill
  · simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom

/-- The canonical finite-stage ambient dualizing complex for the structure morphism of a
finite-type scheme over the fixed algebraically closed finite-field datum. The adjoint
instance is supplied by the ambient exceptional-adjoint theorem and Nagata compactification.
Source: blueprint `lemma-verdier-duality-preserves-constructibility--1`
(blueprint: lemma-verdier-duality-preserves-constructibility--1).
-/
noncomputable def finiteStageDualizingComplex
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X := by
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  letI : CompactSpace (HasCompactification.compactification
      (X ↘ Spec (.of D.k))).Z :=
    QuasiCompact.compactSpace_of_compactSpace
      (HasCompactification.compactification (X ↘ Spec (.of D.k))).g
  letI : IsLocallyNoetherian (HasCompactification.compactification
      (X ↘ Spec (.of D.k))).Z :=
    LocallyOfFiniteType.isLocallyNoetherian
      (HasCompactification.compactification (X ↘ Spec (.of D.k))).g
  letI : (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n)))
      (X ↘ Spec (.of D.k))).IsLeftAdjoint := by
    apply Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
  exact Etale.dualizingComplex
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
    (X ↘ Spec (.of D.k))

/-- Verdier duality preserves bounded constructible finite-Tor complexes over a finite
coefficient stage, with the uniform interval `[-b - 2*d, -a]`.

Source: blueprint main-20261015, chap-Construction-of-f,
`sk-prop-sf-rf-shriek-preservation/lem-weil-verdier-preservation-strata.md`, order 2414
(blueprint: lemma-verdier-duality-preserves-constructibility--1).

Proof (the five steps of the DAG node):
1. If a > b, the tensor-unit lemma lem-kun-tensor-unit makes K zero, so its dual is zero.
Otherwise lem-sf-etale-smooth-stratified-ctf supplies a finite smooth locally closed
stratification, dimensions e <= d, and finite-projective local models in [a,b].
2. The same stratification theorem supplies localization triangles building K from
G = Rs! P, with the terminal object zero. It suffices to bound the dual of each G.
3. Finite-type-over-Noetherian and open-subscheme facts, together with closed-immersion
finite type, verify the hypotheses of Nagata and theorem-existence-exceptional-inverse-image--1 on
all strata. The compact-support composition of lem-amb-unbounded-compact-support-comparisons,
the composite adjunction def-weil-pbc-composite-adjunction and proposition-sp-unique-adjoint--1
identify s! omega_X with omega_S. Then lemma-internal-adjunction-two-exchange-formulas--1 gives
D_X(Rs! P) = Rs* D_S P using ambient adjunctions only.
4. By proposition-exceptional-inverse-image-smooth-morphism, omega_S is locally A[2e]. Restrict
using lem-weil-pbc-ringed-internal-hom-exact-restriction and compute the Hom complex of
E with A[2e] via def-pur-derived-internal-hom: its j-th term is Hom(E^(-j-2e),A).
These are finite projective and vanish outside [-b-2e,-a-2e]. Finite-locally-constant
Serre closure proves constructible cohomology. The bounded-flat Tor bound and derived
tensor restriction descend this interval. Apply theorem-results-from-etale-theory--4
and proposition-six-operations-dctf--2 to Rs* to obtain [-b-2e,-a].
5. By definition-verdier-dual-evaluation--3 dualize the localization triangles and induct backwards
from zero. Tensor each triangle with every module sheaf;
proposition-open-direct-image-preserves-finite and lem-sf-derived-homology-long-exact preserve the
common interval [-b-2d,-a]. The untensored cohomology sequence and thm-constructible-serre preserve
constructibility. The interval contains no n, so the bound is uniform in the coefficient level.
-/
theorem verdier_preservation_strata
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    (K : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X K)
    (_hTor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj
          (finiteStageDualizingComplex D l _hl E n hn X)) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (-b - 2 * (d : ℤ)) (-a)
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj
          (finiteStageDualizingComplex D l _hl E n hn X)) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertibleExponent D l _hl E n
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact preservation_of_perfectField_ulift (Padic.coefficientExtensionRing l E n)
    (X ↘ Spec (.of D.k)) d _hd a b K _hK _hTor

end WeilConjectures
