/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # Coherent reduction of the regular completed coefficient

Source: Stacks Project, Tags 07A4 and 0941; the coefficient-unit tower.
(blueprint: lem-pur-regular-coefficient-coherent-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private def closedUnitIso {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S T : CoefficientClosedStructure H) :
    S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit :=
  (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    ((T.adjunction T.monoidal.tensorUnit).leftAdjointUniq
      (S.adjunction T.monoidal.tensorUnit)).app S.monoidal.tensorUnit ≪≫
    S.monoidal.leftUnitor T.monoidal.tensorUnit

private def imageUnitIso {C D : Type*} [Category* C] [Category* D]
    {H : Cᵒᵖ × C ⥤ C} {J : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure J)
    (F : C ⥤ D) (μ : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor)
    (V : C) (e : F.obj V ≅ T.monoidal.tensorUnit) :
    F.obj S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit :=
  (T.monoidal.rightUnitor _).symm ≪≫
    T.tensor.mapIso (Iso.prod (Iso.refl _) e.symm) ≪≫
    (μ.app (S.monoidal.tensorUnit, V)).symm ≪≫
    F.mapIso (S.monoidal.leftUnitor V) ≪≫ e

/-- The regular completed sheaf reduces to the actual coherent coefficient-ring unit.

Source: Stacks Project, Tags 07A4 and 0941; the coefficient-unit tower.
(blueprint: lem-pur-regular-coefficient-coherent-reduction).

Proof: compare the ordinary integral tensor unit with the regular coefficient
using uniqueness of left adjoints to the fixed internal Hom and the normalized
ringed-site unit isomorphism. Let V be the reconstructed integral tensor unit.
Its reduction is the system unit by the invertible coherent reduction counit.
The reduction functor preserves tensor. Thus reduction of the ordinary integral
unit is isomorphic to its tensor with reduction(V), then to reduction of the
tensor of the integral unit with V, then to reduction(V), and hence to the
system unit. Compose with reduction of the regular-coefficient identification.
Only isomorphisms of whole coherent systems are used. This argument also
applies to the zero scheme and needs no bounded Tor-amplitude assumption. -/
theorem regularCoefficient_coherentReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty ((pullbackTensorCalculus l E X).reduction.obj
      (integralConstantCoefficientObject l E X) ≅
        (pullbackTensorCalculus l E X).systemClosed.monoidal.tensorUnit) := by
  let S := pullbackTensorCalculus l E X
  let D := Classical.choice (ringedSiteDualityMaps_exists.{u + 1, u, u, u + 2}
    (Scheme.ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X))
  let a : S.integralClosed.monoidal.tensorUnit ≅
      integralConstantCoefficientObject l E X :=
    closedUnitIso S.integralClosed D.closed ≪≫ D.unitIso ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (scalarReductionSource l E X) 0).app
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))).symm
  let V := (pullbackTensorIntegralUnit l E X).obj
  have : IsIso (S.adjunction.counit.app S.systemClosed.monoidal.tensorUnit) :=
    pullbackTensorIntegralUnit_counit l E X
  let e : S.reduction.obj V ≅ S.systemClosed.monoidal.tensorUnit :=
    asIso (S.adjunction.counit.app _)
  exact ⟨S.reduction.mapIso a.symm ≪≫
    imageUnitIso S.integralClosed S.systemClosed S.reduction S.reductionTensor V e⟩

end WeilConjectures
