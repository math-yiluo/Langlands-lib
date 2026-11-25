/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.SmoothBaseChange.SbcCompletedOperations

/-! # Finite quotient restriction is derived complete

Source: Stacks Tags 091N, 099L and 093M; the finite-restriction geometric-series completeness
calculation and its normalized completed-coefficient transport.
(blueprint: lem-sf-regular-quotient-restriction-complete). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

private def finiteCoefficientIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      integralCoefficientCommRingSheaf l E T n :=
  (fullyFaithfulSheafCompose (ProEt.topology T)
    (Functor.FullyFaithful.ofFullyFaithful
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).preimageIso
    (integralDetailedLevelComparison T l E n)

private theorem finiteCoefficientIso_projection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    (purCoefficientIso l E T).hom ≫
        completedIntegralCommRingProjectionUnrestricted l E T n =
      pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (finiteCoefficientIso l E T n).hom := by
  apply (adicLisseForget T).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  have hc := congrArg Iso.hom (purCoefficientIso_existsUnique l E T).exists.choose_spec
  have hf := (fullyFaithfulSheafCompose (ProEt.topology T)
    (Functor.FullyFaithful.ofFullyFaithful
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))).map_preimage
        (integralDetailedLevelComparison T l E n).hom
  change (adicLisseForget T).map (purCoefficientIso l E T).hom = _ at hc
  change (adicLisseForget T).map (finiteCoefficientIso l E T n).hom = _ at hf
  rw [hc, hf]
  exact (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec n

/-- Restriction of every unbounded finite-quotient complex is intrinsically derived
complete over the actual completed coefficient sheaf.
Source: Stacks Tags 091N, 099L and 093M; the finite-restriction geometric-series completeness
calculation and its normalized completed-coefficient transport.
(blueprint: lem-sf-regular-quotient-restriction-complete). -/
theorem scalarReductionDerivedRestriction_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget l E T n)) :
    IsSfDerivedComplete l E T ((scalarReductionDerivedRestriction l E T n).obj K) := by
  let d := pbcIntegralDatum l E
  let c := purCoefficientIso l E T
  let b := finiteCoefficientIso l E T n
  let q := completedIntegralCommRingProjectionUnrestricted l E T n
  let p := pbcAdicProjection T d n
  have hc : (adicLisseForget T).map c.hom =
      (integralDetailedCoefficientComparison T l E).hom :=
    congrArg Iso.hom (purCoefficientIso_existsUnique l E T).exists.choose_spec
  let e₀ : pbcDerivedRestrict q ⋙ pbcDerivedRestrict c.hom ≅
      pbcDerivedRestrict b.hom ⋙ pbcDerivedRestrict p :=
    pbcDerivedRestrictComp c.hom q (c.hom ≫ q) rfl ≪≫
      (pbcDerivedRestrictComp p b.hom (c.hom ≫ q)
        (finiteCoefficientIso_projection l E T n).symm).symm
  let e₁ : pbcRestrict c.hom ≅
      SheafOfModules.restrictScalars (integralDetailedCoefficientComparison T l E).hom :=
    eqToIso (congrArg SheafOfModules.restrictScalars hc)
  let := (integralDetailedCoefficientRestriction_exact T l E).1
  let := (integralDetailedCoefficientRestriction_exact T l E).2
  let e₂ : pbcDerivedRestrict c.hom ≅ integralDetailedTransport T l E :=
    Functor.mapDerivedCategoryNatIso e₁
  let e : (integralDetailedTransport T l E).obj
        ((scalarReductionDerivedRestriction l E T n).obj K) ≅
      (pbcDerivedRestrict p).obj ((pbcDerivedRestrict b.hom).obj K) := by
    exact (e₂.app ((scalarReductionDerivedRestriction l E T n).obj K)).symm ≪≫
      e₀.app K
  have h := sbcFiniteRestricted_complete T d 1
    (fun _ : Fin 1 ↦ pbcUniformizer l E)
    (by
      change Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcUniformizer l E)) =
        Ideal.span {pbcUniformizer l E}
      simp only [Set.range_const])
    n ((pbcDerivedRestrict b.hom).obj K)
  apply (purDetailedTransport_complete_iff l E T _).mpr
  exact sbcComplete_iso l E e.symm h

end WeilConjectures
