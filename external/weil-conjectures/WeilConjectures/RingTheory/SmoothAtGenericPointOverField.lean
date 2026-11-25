/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.FieldTheory.SeparableExtension
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import Mathlib.RingTheory.AlgebraicIndependent.Basic

@[expose] public section
universe u v w
namespace Algebra

private theorem separablyGenerated_of_algEquiv
    {k : Type u} {K : Type v} {K' : Type w}
    [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    (e : K ≃ₐ[k] K') (h : IsSeparablyGenerated k K) : IsSeparablyGenerated k K' := by
  rcases h with ⟨s, hs, hsep⟩
  refine ⟨e '' s, ?_, ?_⟩
  · exact (isTranscendenceBasis_image e.injective.injOn).mp
      (e.isTranscendenceBasis hs)
  · let ebase : IntermediateField.adjoin k s ≃ₐ[k] IntermediateField.adjoin k (e '' s) :=
      ((IntermediateField.adjoin k s).equivMap e.toAlgHom).trans
        (IntermediateField.equivOfEq (IntermediateField.adjoin_map k s e.toAlgHom))
    let := hsep
    apply Algebra.IsSeparable.of_equiv_equiv ebase.toRingEquiv e.toRingEquiv
    ext x
    change (ebase x : K') = e (x : K)
    rfl

/-- Core finitely generated subextension transport used to prove separability of the
zero-prime residue field. Source: Stacks Project, Algebra, Lemma 07ND. The proof
identifies the zero-prime residue field with the fraction field, transports the
finitely generated intermediate field across that identification, and applies
separable generation supplied by `hsep`.
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable-fg) -/
theorem separableExtension_bot_residueField_finitelyGenerated
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L]
    (hsep : IsSeparableExtension k L)
    (F : IntermediateField k (⊥ : Ideal S).ResidueField) (hF : F.FG) :
    IsSeparablyGenerated k F := by
  let e : (⊥ : Ideal S).ResidueField ≃ₐ[k] L :=
    (IsLocalization.algEquiv (nonZeroDivisors S) (⊥ : Ideal S).ResidueField L).restrictScalars k
  have hmap : (F.map e.toAlgHom).FG := by
    rcases IntermediateField.fg_def.mp hF with ⟨s, hs, hFs⟩
    rw [← hFs, IntermediateField.adjoin_map]
    exact IntermediateField.fg_adjoin_of_finite (hs.image e)
  exact separablyGenerated_of_algEquiv (F.equivMap e.toAlgHom).symm
    (hsep (F.map e.toAlgHom) hmap)

/-- Separability of the fraction field transfers to the residue field at the generic point.
Source: Stacks Project, Algebra, Lemma 07ND. The proof identifies the residue field at
the zero prime with the fraction field through the localization and residue-field
isomorphisms for a domain, then transports `IsSeparableExtension` across that
field isomorphism. The required compatibility with the given `k`-algebra structures
follows from the canonical maps in the localization construction.
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field-residue-separable) -/
theorem separableExtension_bot_residueField
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L] (hsep : IsSeparableExtension k L) :
    IsSeparableExtension k (⊥ : Ideal S).ResidueField := by
  intro F hF
  exact separableExtension_bot_residueField_finitelyGenerated k S L hsep F hF


/-- A finite type domain over a field with separable fraction field is smooth at the zero prime.
Source: Stacks Project, Algebra, Lemma 07ND.
(blueprint: lem-weil-pbc-smooth-at-generic-point-over-field) -/
theorem smoothAtPrime_bot_of_isSeparable_fractionRing
    (k : Type u) (S : Type v) (L : Type w)
    [Field k] [CommRing S] [IsDomain S] [Field L]
    [Algebra k S] [Algebra S L] [Algebra k L] [IsScalarTower k S L]
    [FiniteType k S] [IsFractionRing S L] (hsep : IsSeparableExtension k L) :
    IsSmoothAtPrime k (⟨(⊥ : Ideal S), inferInstance⟩ : PrimeSpectrum S) := by
  let _ : IsLocalization (⊥ : Ideal S).primeCompl (FractionRing S) := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let e : Localization.AtPrime (⊥ : Ideal S) ≃+* FractionRing S :=
    (IsLocalization.algEquiv (⊥ : Ideal S).primeCompl
      (Localization.AtPrime (⊥ : Ideal S)) (FractionRing S)).toRingEquiv
  have hreg : IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal S)) :=
    IsRegularLocalRing.of_ringEquiv (R := FractionRing S) e.symm
  exact (regularLocal_iff_smoothAtPrime k S (⊥ : Ideal S)
    (separableExtension_bot_residueField k S L hsep)).mpr hreg

end Algebra
