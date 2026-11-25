/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! # Finite shifted Hom over arbitrary algebraically closed base fields

Source: SGA 4½, finiteness theorem; the mapping-limit argument in
proposition-six-operations-change-coefficients and the existing qcqs shifted-Hom proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem intrinsic_hom_finite_algClosed
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hlD : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K₀ : Type u) [Field K₀] [IsAlgClosed K₀] (hl : IsUnit (l : K₀))
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [∀ x : X, Invertible (l : X.residueField x)]
    (K M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (hK : intrinsicFiniteTorsionConstructible l E n hn X K)
    (hM : intrinsicFiniteTorsionConstructible l E n hn X M)
    (a b c d : ℤ)
    (hKt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) K a b)
    (hMt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) M c d) :
    Finite (K ⟶ M) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let : HasInvertibleExponent (ULift.{u + 1, u} A) (Spec (.of K₀)) :=
    coefficient_has_invertible_exponent l E K₀
      hl n hn
  let J := ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} A) X) ⋙ ProEtale.finiteCoefficientIntrinsicDerivedComparison X A
  have hJ := finiteRing_constructibleDerived_origin X A
  let : J.Full := hJ.1
  let : J.Faithful := hJ.2.1
  have origin (L : proEtaleDerivedCategory X A)
      (hL : intrinsicFiniteTorsionConstructible l E n hn X L) : J.essImage L := by
    obtain ⟨lo, hlo⟩ := hL.1.bddBelow
    obtain ⟨hi, hhi⟩ := hL.1.bddAbove
    apply (hJ.2.2.1 L).mpr
    refine ⟨hL.2, min lo hi, max lo hi, min_le_max, fun i hi' ↦ ?_⟩
    by_contra hz
    rcases hi' with hi' | hi'
    · exact (not_lt_of_ge (hlo hz)) (hi'.trans_le (min_le_left _ _))
    · exact (not_lt_of_ge (hhi hz)) ((le_max_right _ _).trans_lt hi')
  obtain ⟨K', ⟨eK⟩⟩ := origin K hK
  obtain ⟨M', ⟨eM⟩⟩ := origin M hM
  have hKb := etale_bc _ X K'.obj K'.property
  have hMb := etale_bc _ X M'.obj M'.property
  have hKt' := finiteCoefficient_comparison_reflects_torAmplitude
    D l hlD E n hn X a b K'.obj hKb.1.1 K hK hKt eK.symm
  have hMt' := finiteCoefficient_comparison_reflects_torAmplitude
    D l hlD E n hn X c d M'.obj hMb.1.1 M hM hMt eM.symm
  let hfin : Finite (K'.obj ⟶ M'.obj) := etale_hom_finite (ULift.{u + 1, u} A) K₀ X
    (X ↘ Spec (.of K₀)) K'.obj M'.obj hKb hMb a b c d
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hKt')
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hMt')
  let : Finite (K' ⟶ M') := @Finite.of_equiv _ _ hfin
    ((ObjectProperty.fullyFaithfulι
      (Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1, u} A) X)).homEquiv
        (X := K') (Y := M')).symm
  exact Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful J).homEquiv.trans
    (eK.homCongr eM))

/-- Finite shifted Hom into every restricted reduction over any algebraically
closed base field. No separatedness of the structure morphism is assumed.

Source: SGA 4½, finiteness theorem, and the scalar-adjunction proof of
`lem-sf-integral-reduction-shifted-hom-finite-qcqs`.
(blueprint: lem-sf-integral-reduction-shifted-hom-finite-alg-closed).

Proof: shift the first integral constructible input. Its residue support, and
that of the target, bound the Tor amplitudes of all finite reductions by the
residue Tor theorem. That theorem's auxiliary finite-field datum is unrelated
to the geometric base: construct one using any prime different from l. The
finite-ring étale/pro-étale comparison is fully faithful on bounded constructible
objects and reflects the Tor bounds. Finite-coefficient étale Hom finiteness
therefore gives a finite Hom set between the two reductions over the given
algebraically closed field. Transpose by the scalar extension/restriction
adjunction. This includes index zero, zero objects and empty schemes. -/
theorem integralReduction_shiftedHom_finite_algClosed
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K₀ : Type u) [Field K₀] [IsAlgClosed K₀] (hl : IsUnit (l : K₀))
    (X : Scheme.{u}) [X.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    (K M : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    Finite (K.obj⟦(1 : ℤ)⟧ ⟶
      (sfDerivedReductionRestricted l E X n).obj M.obj) := by
  classical
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{u} := {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_rfl
    cardinality_eq := (pow_one p).symm
    k₀ := ULift.{u} (ZMod p)
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ULift.{u} (ZMod p)) }
  have hlD : l ≠ D.p := by change l ≠ p; omega
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (by simpa using hl.map ((X ↘ Spec (.of K₀)).residueFieldAlgebraMap x) :
      IsUnit (l : X.residueField x)).invertible
  let K' : sfIntegralConstructibleCategory l E X :=
    ⟨K.obj⟦(1 : ℤ)⟧, (sfIntegralConstructible l E X).le_shift (1 : ℤ) _ K.property⟩
  obtain ⟨a, b, hab, hK⟩ := K'.property.2
  obtain ⟨c, d, hcd, hM⟩ := M.property.2
  have htK := (integral_residue_tor D l hlD E X).1
    K'.obj K'.property a b hab (hK 0).2 n
  have htM := (integral_residue_tor D l hlD E X).1
    M.obj M.property c d hcd (hM 0).2 n
  let : Finite ((scalarReductionDerivedExtension.{u, u} l E X n).obj K'.obj ⟶
      (scalarReductionDerivedExtension.{u, u} l E X n).obj M.obj) :=
    intrinsic_hom_finite_algClosed D l hlD E K₀ hl (n + 1) (by omega) X _ _
      (hK n).1 (hM n).1 a b c d htK htM
  exact Finite.of_equiv _
    ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _)

end WeilConjectures
