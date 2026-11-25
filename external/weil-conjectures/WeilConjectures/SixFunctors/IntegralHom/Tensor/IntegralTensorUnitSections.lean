/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison

set_option linter.privateModule false

/-! # Inverse tensor-unit maps on local sections

Source: the finite-free quotient resolution in the first paragraph of the current
blueprint `lem-coef-integral-hom-reduction.proof.md`; Stacks Tags 06YY, 08J7 and 07A6.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses)
namespace WeilConjectures.IntegralHom

open CategoryTheory.MonoidalCategory
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local instance] countableColimits
  ordinaryTensorZero ordinaryTensorObjZero

private noncomputable instance moduleMonoidal
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    MonoidalCategory (Modules.{t, u} Y R) := SheafOfModules.monoidalCategory R

private noncomputable instance modulePreadditive
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    MonoidalPreadditive (Modules.{t, u} Y R) := SheafOfModules.tensorPreadditive R

private noncomputable instance tensorColimits
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (M : Modules.{t, u} Y R) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
  exact preservesColimitsOfSize_shrink (tensorLeft M)

private noncomputable instance tensorRightColimits
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (M : Modules.{t, u} Y R) : PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
  let : SymmetricCategory (Modules.{t, u} Y R) := SheafOfModules.symmetricCategory R
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

private noncomputable def coefficientUnit
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    CochainComplex (Modules.{t, u} Y R) ℤ :=
  (CochainComplex.singleFunctor (Modules.{t, u} Y R) 0).obj
    (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))

private noncomputable def tensorUnitIso
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (N : CochainComplex (Modules.{t, u} Y R) ℤ) :
    ((totalTensor.{t, u} Y R).obj N).obj (coefficientUnit.{t, u} Y R) ≅ N :=
  HomologicalComplex.rightUnitor N

private theorem tensorUnitIso_naturality
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    {N N' : CochainComplex (Modules.{t, u} Y R) ℤ} (f : N ⟶ N') :
    ((totalTensor.{t, u} Y R).map f).app (coefficientUnit.{t, u} Y R) ≫
        (tensorUnitIso.{t, u} Y R N').hom = (tensorUnitIso.{t, u} Y R N).hom ≫ f :=
  rightUnitor_naturality f

attribute [local implicit_reducible] homComplex totalTensor coefficientTotalTensor
  evaluate projection
  homComplexπ moduleMonoidal coefficientUnit SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.Functor.map₂HomologicalComplex

attribute [local irreducible] tensorUnitIso homComplexFunctor
  completedIntegralCoefficientSheafUnrestricted HasDerivedCategory.standard
  derivedInternalHomOfUniverses

attribute [local implicit_reducible] SheafOfModules.monoidalCategory

private theorem tensorUnitIso_inv_section
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (N : CochainComplex (Modules.{t, u} Y R) ℤ) (n : ℤ)
    (U : Y.ProEtᵒᵖ) (v : (N.X n).val.obj U) :
    ((tensorUnitIso.{t, u} Y R N).inv.f n).val.app U v =
      coefficientTensorGenerator.{u, t + 1, t} (AlgebraicGeometry.Scheme.ProEt.topology Y)
        R N (coefficientUnit.{t, u} Y R) n 0 n (add_zero n) U v
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (forget₂ CommRingCat RingCat)).obj R))).inv.val.app U
                (1 : R.obj.obj U)) := by
  let : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf _
  let B := coefficientUnit.{t, u} Y R
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat RingCat)).obj R))
  let j := HomologicalComplex.ιTensorObj N B n 0 n (add_zero n)
  have hu : (tensorUnitIso.{t, u} Y R N).inv.f n =
      (ρ_ (N.X n)).inv ≫ (N.X n ◁ e.inv) ≫ j := by
    unfold tensorUnitIso
    exact HomologicalComplex.rightUnitor'_inv N n
  calc
    _ = (j.val.app U) (((N.X n ◁ e.inv).val.app U)
        (((ρ_ (N.X n)).inv.val.app U) v)) := by
      rw [hu, SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
        SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
      rfl
    _ = (j.val.app U) (CategoryTheory.CochainPullback.moduleTmul
        (R := R) (N.X n) (B.X 0) U v (e.inv.val.app U (1 : R.obj.obj U))) := by
      rw [SheafOfModules.unitor_inv_pure.{t + 1, t, u} R (N.X n) U v]
      apply congrArg (j.val.app U)
      rw [← id_tensorHom]
      exact CategoryTheory.CochainPullback.moduleTmul_map (𝟙 (N.X n)) e.inv U v (1 : R.obj.obj U)
    _ = _ := rfl

end WeilConjectures.IntegralHom
