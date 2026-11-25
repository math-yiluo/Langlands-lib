/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible

/-! # Étale origin of inverse finite coefficient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private theorem etaleBoundedIff (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : AlgebraicGeometry.Etale.DerivedCategoryModule A X) :
    AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible A X K ↔
      AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private theorem fixedEtaleOrigin (X : SixFunctorSpace D)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    let A := Padic.coefficientExtensionRing C.l E n
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    ∃ L : AlgebraicGeometry.Etale.DerivedCategoryModule (ULift.{u + 1} A) X.obj.left,
      AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left L ∧
      Nonempty ((AlgebraicGeometry.ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left).mapDerivedCategory.obj L ≅
          (realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) := by
  classical
  dsimp only
  let A := Padic.coefficientExtensionRing C.l E n
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := realization (C := C) (E := E) (n := n) (hn := hn) X
  let U := AlgebraicGeometry.ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X.obj.left
  obtain ⟨a, ha⟩ := K.property.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin X.obj.left A).2.2.1
    K.obj).mpr ⟨K.property.2, min a b, b, min_le_right _ _, hv⟩
  refine ⟨L.obj, (etaleBoundedIff _ _ _).1 L.property, ⟨?_⟩⟩
  apply R.functor.preimageIso
  exact ((Functor.mapDerivedCategoryCompIso U
    (sfIntrinsicModuleEquivalence X.obj.left A).functor).app L.obj) ≪≫
      eL ≪≫ (R.counitIso.app K.obj).symm

/-- Inverse realization of a bounded constructible input has bounded-below étale origin.
Source: finiteRing_constructibleDerived_origin and preservation of boundedness by the
coefficient equivalence (blueprint: lem-sf-finite-realization-etale-origin).
Proof: the intrinsic constructibility and finite homology support of K give a bounded
constructible etale preimage by the finite-ring origin theorem. Lift its comparison
through the coefficient equivalence. Its lower bound gives the required plus origin. -/
theorem finiteRealization_etaleOrigin (X : SixFunctorSpace D)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))
      X.obj.left ((realization (C := C) (E := E) (n := n) (hn := hn) X).inverse.obj K.obj) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  obtain ⟨L, hL, e⟩ := fixedEtaleOrigin X K
  exact ⟨L, hL.1.1, e⟩

end WeilConjectures.CompactSupportFiniteProjection
