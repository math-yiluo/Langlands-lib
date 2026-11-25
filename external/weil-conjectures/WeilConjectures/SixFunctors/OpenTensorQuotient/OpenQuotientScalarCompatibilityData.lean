/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import all WeilConjectures.SmoothPurity.Integral.Open.IntegralOpenScalarRestrictionComparison

/-! # Existence of normalized scalar compatibility data for an open quotient

Source: Stacks Project, Tags 03DI, 03DA, 0E8I and 0941.
(blueprint: lem-sf-open-quotient-scalar-compatibility-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenTensorQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private theorem normalizedFinite (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    ∃ finite : IntegralOpenReduction.finiteExtension l E j o n ⋙
        scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E U n ⋙ IntegralOpenReduction.extension l E j o,
    ∀ (M : normalizedDVRModules l E U n) (V : X.ProEt)
      (a : V ⟶ IntegralOpenReduction.openObject j)
      (x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a)))),
      (finite.hom.app M).val.app (op V)
        (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) =
      IntegralOpenReduction.extensionSection l E j o
        ((scalarReductionRestriction l E U n).obj M) V a x := by
  let fm := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map o.completedMap
  let fn := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (o.finiteMap n)
  let b := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (completedIntegralCommRingProjectionUnrestricted l E X n)
  let q := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (completedIntegralCommRingProjectionUnrestricted l E U n)
  have hs : fm ≫ ((IntegralOpenReduction.sliceSite j).sheafPushforwardContinuous
      RingCat.{u + 1} ((ProEt.topology X).over (IntegralOpenReduction.openObject j))
        (ProEt.topology U)).map q =
      ((ProEt.topology X).overPullback RingCat.{u + 1}
        (IntegralOpenReduction.openObject j)).map b ≫ fn := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    exact congrArg ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map)
      (congrArg (fun k ↦ k.hom.app W) (o.projections n))
  obtain ⟨d⟩ := @WeilConjectures.openScalarComparison.{u + 1, u + 1, u, u, u + 1}
    X.ProEt inferInstance U.ProEt inferInstance (ProEt.topology X) (ProEt.topology U)
    (IntegralOpenReduction.openAbSheafify.{u, u} (X := X))
    (IntegralOpenReduction.openAbLocallyBijective.{u, u} (X := X))
    (IntegralOpenReduction.openObject j) (IntegralOpenReduction.sliceSite j)
    (cbcSliceFunctor_continuous X (IntegralOpenReduction.openObject j))
    (completedIntegralCommRingSheafUnrestricted l E X) (integralCoefficientCommRingSheaf l E X n)
    (completedIntegralCommRingProjectionUnrestricted l E X n)
    (completedIntegralCoefficientSheafUnrestricted l E U) (integralCoefficientSheaf l E U n)
    q fm fn o.integral.functor (o.finite n).functor
    (eqToIso o.integralFunctor) (eqToIso (o.finiteFunctor n))
    b rfl hs
  let e := @WeilConjectures.OpenScalarResult.ordinary.{u + 1, u + 1, u, u, u + 1}
    X.ProEt inferInstance U.ProEt inferInstance (ProEt.topology X) (ProEt.topology U)
    (IntegralOpenReduction.openAbSheafify.{u, u} (X := X))
    (IntegralOpenReduction.openAbLocallyBijective.{u, u} (X := X))
    (IntegralOpenReduction.openObject j) (IntegralOpenReduction.sliceSite j)
    (cbcSliceFunctor_continuous X (IntegralOpenReduction.openObject j))
    (completedIntegralCommRingSheafUnrestricted l E X) (integralCoefficientCommRingSheaf l E X n)
    (completedIntegralCoefficientSheafUnrestricted l E U) (integralCoefficientSheaf l E U n)
    q fm fn o.integral.functor (o.finite n).functor
    (eqToIso o.integralFunctor) (eqToIso (o.finiteFunctor n)) b d
  have he := @WeilConjectures.OpenScalarResult.generators.{u + 1, u + 1, u, u, u + 1}
    X.ProEt inferInstance U.ProEt inferInstance (ProEt.topology X) (ProEt.topology U)
    (IntegralOpenReduction.openAbSheafify.{u, u} (X := X))
    (IntegralOpenReduction.openAbLocallyBijective.{u, u} (X := X))
    (IntegralOpenReduction.openObject j) (IntegralOpenReduction.sliceSite j)
    (cbcSliceFunctor_continuous X (IntegralOpenReduction.openObject j))
    (completedIntegralCommRingSheafUnrestricted l E X) (integralCoefficientCommRingSheaf l E X n)
    (completedIntegralCoefficientSheafUnrestricted l E U) (integralCoefficientSheaf l E U n)
    q fm fn o.integral.functor (o.finite n).functor
    (eqToIso o.integralFunctor) (eqToIso (o.finiteFunctor n)) b d
  refine ⟨e.symm, ?_⟩
  intro M V a x
  have h := he M (op V) a
  have hh := congrFun (eq_of_heq h) x
  change (e.inv.app M).val.app (op V)
    (IntegralOpenReduction.finiteExtensionSection l E j o n M V a x) = _
  have hg : (e.hom.app M).val.app (op V)
      (IntegralOpenReduction.extensionSection l E j o
        ((scalarReductionRestriction l E U n).obj M) V a x) =
      IntegralOpenReduction.finiteExtensionSection l E j o n M V a x := hh
  rw [← hg]
  have hi := congrArg (fun f ↦ f.val.app (op V)
    (IntegralOpenReduction.extensionSection l E j o
      ((scalarReductionRestriction l E U n).obj M) V a x))
    (Iso.hom_inv_id_app e M)
  exact hi

/-- The finite scalar comparisons can be chosen with their generator normalization.

Apply the generic open/scalar comparison to each completed coefficient projection.
The projection equation of `o` supplies its ring square. Invert the comparison and
cancel its generator equation with its inverse to obtain the normalized finite maps.
These are the two fields used to construct the strict quotient-tower comparison and
prove its scalar-unit equation. Strictness is retained by `ScalarComparison.iso`,
without an independent comparison on arbitrary coefficient systems.
Source: Stacks Tags 03DI, 03DA and 0E8I.
(blueprint: lem-sf-open-quotient-scalar-compatibility-data). -/
theorem openQuotientScalarCompatibilityData
    (o : IntegralOpenReduction.Operations l E j) :
    Nonempty (ScalarCompatibility l E j o) := by
  classical
  choose finite sections using normalizedFinite l E j o
  exact ⟨{ finite := finite, sections := sections }⟩

end WeilConjectures.OpenTensorQuotient
