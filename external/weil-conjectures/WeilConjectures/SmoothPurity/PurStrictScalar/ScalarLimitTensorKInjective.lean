/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import WeilConjectures.Algebra.Category.ModuleCat.CoextendScalarsAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.RingTheory.FrobeniusForm
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree

/-! # K-injective preservation for strict scalar tensor

The Frobenius form on the finite extension of integral coefficient rings identifies
strict scalar extension with a right adjoint of exact restriction.
(blueprint: lem-pur-compact-support-scalar-limit-tensor-kinjective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

/-- Constant-module encoding commutes with restriction: the underlying sections
and restriction maps are unchanged, and scalar compatibility is naturality of
the sheafification unit. -/
private def encodingSquare (W : Scheme.{u}) {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) :
    pbcRestrict ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom f.ulift.{u + 1, u + 1})) ⋙
        (proEtaleModuleEncoding W A).functor ≅
    (proEtaleModuleEncoding W B).functor ⋙
      Sheaf.restrictScalars (ProEt.topology W) f.ulift.{u + 1, u + 1} := by
  let L := pbcRestrict ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom f.ulift.{u + 1, u + 1})) ⋙ (proEtaleModuleEncoding W A).functor
  let R := (proEtaleModuleEncoding W B).functor ⋙
    Sheaf.restrictScalars (ProEt.topology W) f.ulift.{u + 1, u + 1}
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
      LinearEquiv.toModuleIso
        (show (L.obj M).obj.obj U ≃ₗ[ULift.{u + 1} A] (R.obj M).obj.obj U from
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ })) ?_)
    · intro a x
      let : Module (((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} B))).obj.obj U)
          ((L.obj M).obj.obj U) := (M.val.obj U).isModule
      change (((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom f.ulift.{u + 1, u + 1})).hom.app U)
        ((toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) •
          (show M.val.obj U from x) =
        ((toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app U
          (f.ulift.{u + 1, u + 1} a)) • (show M.val.obj U from x)
      congr 1
      exact (ConcreteCategory.congr_hom (congr_app
        (toSheafify_naturality (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).map
            (CommRingCat.ofHom f.ulift.{u + 1, u + 1}))) U) a).symm
    · intro U V g
      ext x
      rfl
  · intro M N g
    ext U x
    rfl

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Finite-free strict scalar extension preserves K-injective complexes.
Source: Stacks 03CY and 0941; dual-basis tensor/restriction argument.
(blueprint: lem-pur-compact-support-scalar-limit-tensor-kinjective).
Proof: the integral coefficient rings are principal ideal domains. Their finite
free extension has a Frobenius form, identifying extension with coextension.
Transport its two adjunctions through the constant-module encoding equivalences,
then apply the K-injective criterion to exact restriction on strict towers. -/
theorem scalarTensor_preservesKInjective (W : Scheme.{u}) :
    (tensor l E F i W).PreservesKInjectiveComplexes := by
  classical
  let := i.toAlgebra
  let f := integralScalarIntegerInclusion l E F i
  let := f.toAlgebra
  obtain ⟨b⟩ := WeilConjectures.integral_basis l E F i
  let : Algebra (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (Padic.coefficientExtensionIntegers l F) :=
    ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  let b' : Module.Basis (Fin (Module.finrank E F)) A B :=
    WeilConjectures.liftedBasis.{u, u} b
  have : Module.Free A B := Module.Free.of_basis b'
  have : Module.Finite A B := Module.Finite.of_basis b'
  have hF := (Padic.coefficientExtensionIntegers_dvr l F).choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l F) :=
    hF.2.2.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective
    ULift.ringEquiv.symm.toRingHom ULift.ringEquiv.symm.surjective
  have : IsDomain A := MulEquiv.isDomain
    (Padic.coefficientExtensionIntegers l E) ULift.ringEquiv.toMulEquiv
  have : IsDomain B := MulEquiv.isDomain
    (Padic.coefficientExtensionIntegers l F) ULift.ringEquiv.toMulEquiv
  obtain ⟨φ, hφ⟩ := Module.exists_bijective_comp_mulLeft A B
  let J := ProEt.topology W
  let EA := proEtaleModuleEncoding W (Padic.coefficientExtensionIntegers l E)
  let EB := proEtaleModuleEncoding W (Padic.coefficientExtensionIntegers l F)
  let co := sheafCompose J (ModuleCat.coextendScalars (algebraMap A B))
  let res := Sheaf.restrictScalars J (algebraMap A B)
  let hleft : co ⊣ res := Sheaf.sheafComposeRestrictScalarsAdj J _
    (ModuleCat.coextendRestrictScalarsAdj b' φ hφ)
  let hright : res ⊣ co := Sheaf.restrictCoextendScalarsAdj J _
  let U := pbcRestrict (constantMap l E F i W)
  let C := (EA.functor ⋙ co) ⋙ EB.inverse
  let Q := (EB.functor ⋙ res) ⋙ EA.inverse
  let q : Q ≅ U :=
    Functor.isoWhiskerRight (encodingSquare W f).symm EA.inverse ≪≫
      Functor.associator U EA.functor EA.inverse ≪≫
      Functor.isoWhiskerLeft U EA.unitIso.symm ≪≫ U.rightUnitor
  let left : C ⊣ U :=
    ((EA.toAdjunction.comp hleft).comp EB.symm.toAdjunction).ofNatIsoRight q
  let right : U ⊣ C :=
    ((EB.toAdjunction.comp hright).comp EA.symm.toAdjunction).ofNatIsoLeft q
  let e : pbcExtend (constantMap l E F i W) ≅ C :=
    (pbcScalarAdjunction (constantMap l E F i W)).leftAdjointUniq left
  let adj := (right.ofNatIsoRight e.symm).whiskerRight ℕᵒᵖ
  exact adj.preservesKInjectiveComplexes

end WeilConjectures.PurStrictScalar
