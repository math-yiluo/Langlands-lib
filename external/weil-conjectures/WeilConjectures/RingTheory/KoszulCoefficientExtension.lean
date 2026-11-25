/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulConormalComparison
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.KoszulCoefficientExtensionChi
import WeilConjectures.RingTheory.KoszulCoefficientExtensionNu

/-! # Coefficient extension of the dual Koszul complex and normal determinant

Source: Stacks Project, Tag 0BQZ, the finite free Koszul computation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- Coefficient extension of the finite dual Koszul terms and conormal determinant.
Source: Stacks Project, Tag 0BQZ, finite free Koszul computation and its localization
(blueprint: lem-sc-koszul-coefficient-extension).

Proof: In each exterior degree, take the exterior basis of the standard basis
of A^r. Extend a dual vector by applying algebraMap A S to each of its coefficients
in the dual exterior basis. The exterior determinant formula gives the asserted
evaluation on all image wedges. The contraction differential has coefficients
f i with its fixed degreewise sign, so applying the ring map to its matrix gives
the localized differential; the coefficient maps form the asserted cochain map.
For the determinant, the conormal classes of f form a basis over A/I. Flat
localization preserves Koszul regularity, so their images are the corresponding
basis over S/IS. Extend the dual basis by the quotient map q and then take its
rth exterior power. Evaluate on basis wedges using the determinant formula;
the quotient-map equation gives compatibility on image generators, and
multilinearity gives the displayed equation for arbitrary vectors. These
constructions work for r=0, where the empty determinant is 1, and for zero
quotients, where all determinant values are zero. This lemma constructs only
the coefficient maps, and asserts no compatibility of normalized comparisons. -/
theorem exists_koszul_coefficient_extension
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S))
    (q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)))
    (hq : ∀ b : A, q (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) :
  ∃ (χ : koszulDualComplex A r f ⟶
    ((ModuleCat.restrictScalars (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (koszulDualComplex S r (algebraMap A S ∘ f)))
  (ν : koszulNormalDeterminant A I r →ₗ[A]
    (ModuleCat.restrictScalars (algebraMap A S)).obj
      (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
  (∀ (n : ℕ) (x : (koszulComplex A r f).X n ⟶ ModuleCat.of A A)
    (v : Fin n → (Fin r →₀ A)),
    (χ.f n x).hom (exteriorPower.ιMulti S n
      (fun i ↦ (v i).mapRange (algebraMap A S) (map_zero _))) =
    algebraMap A S (x.hom (exteriorPower.ιMulti A n v))) ∧
  (∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
    exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r (ν w)
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
        (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
          (algebraMap A S ∘ f) hs
          ((v i).mapRange (algebraMap A S) (map_zero _)))) =
    q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
      (exteriorPower.ιMulti (A ⧸ I) r
        (fun i ↦ koszulConormalVector A I r f hf (v i))))) := by
  obtain ⟨χ, hχ⟩ := exists_koszul_coefficient_extension_chi A r f S
  obtain ⟨ν, hν⟩ := exists_koszul_coefficient_extension_nu A I r f hreg hf T S hs q hq
  exact ⟨χ, ν, hχ, hν⟩

end ExteriorAlgebra
