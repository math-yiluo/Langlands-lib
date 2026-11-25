/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenReductionMateLocalization
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Invertibility of the canonical open reduction mate
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical open reduction mate is invertible on every derived object.
Source: Stacks 03DI, 06YS, 06YY and 0GL1; the localization paragraph of
`fix-prop-coherence.proof.md` (blueprint: lem-sf-integral-open-reduction-iso).

Proof: pass to the localization of good K-flat complexes.  The open reduction
localization formula identifies the derived mate with the ordinary open mate on a
K-flat representative.  The ordinary mate is an isomorphism degreewise by the
direct-sum open-extension comparison.  Derived localization preserves this
isomorphism, and essential surjectivity of the localization transports it to every
derived object.  No completeness, constructibility or geometric characteristic
hypothesis is used.
-/
theorem integralOpenReductionIso (o : Operations l E)
    (m : RealizationModel l E o) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategory (scalarReductionSource l E U)) :
    IsIso ((m.openReduction l E j).app K) := by
  let L := integralOperationsGoodLocalization l E U
  let W := (HomologicalComplex.quasiIso (scalarReductionSource l E U) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E U).ι
  let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E U
  let : L.EssSurj := Localization.essSurj L W
  rw [← NatTrans.isIso_app_iff_of_iso _ (L.objObjPreimageIso K)]
  let P := L.objPreimage K
  let : (pullbackTensorOrdinaryReduction l E U).Additive :=
    (pullbackTensorOrdinary_additive l E U).1
  let : (pullbackTensorOrdinaryReduction l E V).Additive :=
    (pullbackTensorOrdinary_additive l E V).1
  let : (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Additive :=
    (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).left_adjoint_additive
  obtain ⟨s, t, _, he⟩ := openReduction_mate_localization l E o m j P
  have : ∀ i, IsIso ((m.ordinary.openReductionComplex l E j
      (o.extension j) P.obj).f i) := fun i ↦
    ordinaryOpenReduction_isIso l E m.ordinary j (o.extension j) (P.obj.X i)
  have : IsIso (m.ordinary.openReductionComplex l E j (o.extension j) P.obj) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (DerivedCategory.Q.map
      (m.ordinary.openReductionComplex l E j (o.extension j) P.obj)) := inferInstance
  exact IsIso.of_isIso_fac_right he

end WeilConjectures.IntegralSystemRealization
