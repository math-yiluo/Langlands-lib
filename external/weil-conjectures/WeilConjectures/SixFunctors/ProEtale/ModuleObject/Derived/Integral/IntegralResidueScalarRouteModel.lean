/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullPresentation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueScalarGeometryBridge
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorRouteModel

/-! Computation of the scalar-route in the residue tensor square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-scalar-route-model)

The target is the explicit ordinary homotopy tensor model. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueScalarRouteModel
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

private theorem existsKFlatPullModel
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type*} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
    (F : C ⥤ D) [F.Additive] [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]
    (M : DerivedCategory C) :
    ∃ R, (HomotopyCategory.quasiIso C (.up ℤ)).kFlat R ∧ F.kFlatMap R ∧
      Nonempty (DerivedCategory.Qh.obj R ≅ M) := by
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some
  let K := DerivedCategory.Q.objPreimage M
  let R := (HomotopyCategory.quotient C (.up ℤ)).obj
    (Λ.reduced.resolutionFunctor.obj K)
  have hR : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat R :=
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K)
  have hFR := F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced K
  have : IsIso (DerivedCategory.Q.map (Λ.reduced.resolutionNatTrans.app K)) :=
    inferInstance
  exact ⟨R, hR, hFR, ⟨(DerivedCategory.quotientCompQhIso C).app
    (Λ.reduced.resolutionFunctor.obj K) ≪≫
      asIso (DerivedCategory.Q.map (Λ.reduced.resolutionNatTrans.app K)) ≪≫
      DerivedCategory.Q.objObjPreimageIso M⟩⟩

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Compute the scalar-route against the ordinary homotopy tensor model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-scalar-route-model)

Proof. Expand the canonical restriction/pullback square using the exact
pullback identifications. The scalar comparison is the inverse mate of this
square. Its counit identity cancels the scalar-extension comparison against the
extension counit that defines the tensor presentation on X. The ordinary
restriction/pullback square and the regular-module unit comparison identify its
coefficient with the inverse image of the coefficient on Y. On ordinary balanced
tensor presentations both remaining maps send s tensor m to s tensor f*(m):
precompose with the balanced coequalizer epimorphism to verify the equality.
Apply the homotopy quotient and Qh; the exact-pullback counit and the defining
left-derived comparison identities give the stated formula. The extension
counit is retained as a map, so P and the residue coefficient need not be flat. -/
theorem integralResidue_scalarRoute_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
    let M := DerivedCategory.Qh.obj P
    (residueExchangeRestrictPullIso ℓ E f).hom.app
          ((residueExchangeReduction ℓ E Y).obj M) ≫
        (residueExchangeRestriction ℓ E X).map
          (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
        (residueExchangeTensorPullIso ℓ E f).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  set_option linter.style.haveILetI false in
  classical
  letI := residueExchangePullMonoidal ℓ E f
    (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
  let M := DerivedCategory.Qh.obj P
  let F := residueExchangeUpperStar (integralCoeff ℓ E) f
  let RY := residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y
  let B := F.obj (residueExchangeCoefficient ℓ E Y)
  let α : RY ⋙ F ⟶ F ⋙ tensorRight B :=
    Functor.whiskerRight (residueExchangeTensorIso ℓ E Y).hom F ≫
      (Functor.Monoidal.commTensorRight F (residueExchangeCoefficient ℓ E Y)).inv
  let β : RY ⋙ F ⟶ F ⋙ tensorRight B :=
    Functor.whiskerLeft (residueExchangeReduction ℓ E Y)
        (residueExchangeRestrictPullIso ℓ E f).hom ≫
      Functor.whiskerRight ((residueExchangePullComparisons ℓ E).pull f).inv
        (residueExchangeRestriction ℓ E X) ≫
      Functor.whiskerLeft F (residueExchangeTensorPullIso ℓ E f).hom
  have hgeom : α.app M = β.app M := by
    obtain ⟨R, hR, hFR, ⟨e⟩⟩ :=
      existsKFlatPullModel ((f)^*⟦integralCoeff ℓ E⟧) M
    have h : α.app (DerivedCategory.Qh.obj R) = β.app (DerivedCategory.Qh.obj R) := by
      simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.Monoidal.commTensorRight_inv_app,
        Functor.Monoidal.μIso_inv, Category.assoc] using
          integralResidue_tensorGeometry_component ℓ E f hFlat R hR hFR
    have hα := α.naturality e.hom
    have hβ := β.naturality e.hom
    rw [h, ← hβ] at hα
    exact (cancel_epi ((RY ⋙ F).map e.hom)).mp hα
  have hmodel := congrArg (fun k ↦ k ≫ residueExchangeTensorModelTarget ℓ E f P)
    hgeom.symm
  simp only [α, β, M, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.Monoidal.commTensorRight_inv_app,
    Category.assoc] at hmodel
  exact hmodel.trans (integralResidue_tensorRoute_model ℓ E f hFlat P)

end AlgebraicGeometry.ProEtale.CondensedRing
