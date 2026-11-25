/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
import all WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
import all WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData

/-! # Localization of completed-coefficient scalar balancing

The ordinary comparison is a parameter, so localization preserves precisely the
comparison fixed by the caller. Source: Stacks Tags 06YY and 099L
(blueprint: lem-pur-completed-scalar-localization-balancing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme hiding Modules
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

attribute [local irreducible] constantMap completedCoefficientMap

private theorem exact_of_conservative_balancing
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasFiniteLimits D] [HasFiniteColimits D]
    (H : A ⥤ B) (T : B ⥤ C) (E : A ⥤ D) (U : D ⥤ C)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] [U.ReflectsIsomorphisms]
    (b : H ⋙ T ≅ E ⋙ U) : PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
  have : ReflectsFiniteLimits U := reflectsFiniteLimits_of_reflectsIsomorphisms U
  have : ReflectsFiniteColimits U := reflectsFiniteColimitsOfReflectsIsomorphisms U
  have : PreservesFiniteLimits (H ⋙ T) := comp_preservesFiniteLimits H T
  have : PreservesFiniteColimits (H ⋙ T) := comp_preservesFiniteColimits H T
  have : PreservesFiniteLimits (E ⋙ U) := preservesFiniteLimits_of_natIso b
  have : PreservesFiniteColimits (E ⋙ U) := preservesFiniteColimits_of_natIso b
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves E U,
    preservesFiniteColimits_of_reflects_of_preserves E U⟩

/-- Every ordinary completed/constant balancing has a unique localization
compatible with all complex counits.
Source: Stacks Tags 06YY and 099L
(blueprint: lem-pur-completed-scalar-localization-balancing).
Proof: constant extension is exact by finite freeness. Restriction of completed
coefficients is conservative, since its underlying abelian sheaf is unchanged.
The given ordinary balancing therefore detects exactness of completed extension.
Its universal left-derived counit is invertible on all complexes. Localize the
ordinary balancing, using these counits and the canonical exact-functor
factorizations. This yields the displayed equation. Any other normalized map
agrees after precomposition with the complex localization, hence agrees by
localization extensionality. The argument includes the zero complex and identity
coefficient extensions and makes no choice of a new ordinary balancing. -/
theorem completedScalarBalancing_existsUnique (W : Scheme.{u})
    [hHA : (constantRestriction l E W).Additive]
    [hHL : PreservesFiniteLimits (constantRestriction l E W)]
    [hHC : PreservesFiniteColimits (constantRestriction l E W)]
    [hUA : (constantRestriction l F W).Additive]
    [hUL : PreservesFiniteLimits (constantRestriction l F W)]
    [hUC : PreservesFiniteColimits (constantRestriction l F W)]
    [(pbcExtend (completedCoefficientMap l E F i W) ⋙
      constantRestriction l F W).Additive]
    (β : constantRestriction l E W ⋙ pbcExtend (constantMap l E F i W) ≅
      pbcExtend (completedCoefficientMap l E F i W) ⋙ constantRestriction l F W) :
    ∃! χ : (constantRestriction l E W).mapDerivedCategory ⋙ baseTensor l E F i W ≅
        pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
          (constantRestriction l F W).mapDerivedCategory,
      ∀ P : CochainComplex (scalarReductionSource l E W) ℤ,
        χ.hom.app (DerivedCategory.Q.obj P) ≫
            (constantRestriction l F W).mapDerivedCategory.map
              (pbcComplexCounit (completedCoefficientMap l E F i W) P) ≫
            (constantRestriction l F W).mapDerivedCategoryFactors.hom.app
              (((pbcExtend (completedCoefficientMap l E F i W)).mapHomologicalComplex
                (.up ℤ)).obj P) =
          (baseTensor l E F i W).map
              ((constantRestriction l E W).mapDerivedCategoryFactors.hom.app P) ≫
            baseTensorCounit l E F i W
              (((constantRestriction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P) := by
  let a := completedCoefficientMap l E F i W
  let U := constantRestriction l F W
  have hLH : PreservesFiniteLimits (constantRestriction l E W) :=
    hHL
  have hCH : PreservesFiniteColimits (constantRestriction l E W) :=
    hHC
  have hLU : PreservesFiniteLimits U := hUL
  have hCU : PreservesFiniteColimits U := hUC
  have hLT : PreservesFiniteLimits (pbcExtend (constantMap l E F i W)) :=
    (baseTensor_exact l E F i W).1
  have hCT : PreservesFiniteColimits (pbcExtend (constantMap l E F i W)) :=
    (baseTensor_exact l E F i W).2
  have hRef : U.ReflectsIsomorphisms := by
    refine ⟨fun f _ ↦ ?_⟩
    have : IsIso ((SheafOfModules.toSheaf _).map f) := by
      change IsIso ((SheafOfModules.toSheaf _).map (U.map f))
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have hFL : HasFiniteLimits (SheafOfModules.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted l F W)) :=
    SheafOfModules.Finite.hasFiniteLimits _
  have hFC : HasFiniteColimits (SheafOfModules.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted l F W)) := inferInstance
  obtain ⟨hLE, hCE⟩ :=
    @exact_of_conservative_balancing _ _ _ _ _ _ _ _ hFL hFC
      (constantRestriction l E W) (pbcExtend (constantMap l E F i W)) (pbcExtend a) U
      hLH hCH hLT hCT hLU hCU hRef β
  have hAddE : (pbcExtend a).Additive := pbcExtend_additive a
  have := pbcDerivedExtension_universal a
  let c := exactScalarCochainIso (pbcExtend a) (pbcDerivedExtend a) (pbcExtensionCounit a)
  have hc (P : CochainComplex
      (pbcModules W (completedIntegralCommRingSheafUnrestricted l E W)) ℤ) :
      c.hom.app P = pbcComplexCounit a P := by
    simp only [c, exactScalarCochainIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      asIso_hom, Category.id_comp, pbcComplexCounit]
  obtain ⟨χ, hχ, huniq⟩ :=
    @localizedBalancing
      (SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E W))
      (pbcModules W ((constants l E).ring W))
      (pbcModules W ((constants l F).ring W))
      (SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l F W))
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (integralCompletedRingHasDerivedCategory l E W) inferInstance inferInstance
      (integralCompletedRingHasDerivedCategory l F W)
      (constantRestriction l E W) (pbcExtend (constantMap l E F i W)) (pbcExtend a) U
      hHA
      (pbcExtend_additive (constantMap l E F i W)) hAddE
      hUA
      hLH hCH hLT hCT hLE hCE hLU hCU (pbcDerivedExtend a) c
      β
  dsimp only [baseTensor, baseTensorCounit]
  refine ⟨χ, ?_, ?_⟩
  · intro P
    simpa only [hc P, a, U] using hχ P
  · intro χ' hχ'
    apply huniq χ'
    intro P
    simpa only [hc P, a, U] using hχ' P

end WeilConjectures.PurStrictScalar
