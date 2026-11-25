/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermHomCoordinates
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! Evaluation of the two surviving tensor coordinates. Source: Stacks 03EK and 0A8X. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] homComplexFunctor

local instance twoTermHomCoordinateEvaluationLocal1 :
    MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.monoidalCategory R

local instance twoTermHomCoordinateEvaluationLocal2 : HasBinaryBiproducts (Modules.{t, u} Y R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

local instance twoTermHomCoordinateEvaluationLocal3 :
    HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  countableColimits Y R

local instance twoTermHomCoordinateEvaluationLocal4 :
    (ordinaryTensor Y R).PreservesZeroMorphisms :=
  ordinaryTensorZero Y R

local instance twoTermHomCoordinateEvaluationLocal5 (M : Modules.{t, u} Y R) :
    ((ordinaryTensor Y R).obj M).PreservesZeroMorphisms := ordinaryTensorObjZero Y R M

local instance twoTermHomCoordinateEvaluationLocal6 (K L : CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex.HasMapBifunctor K L (ordinaryTensor Y R) := fun _j ↦
  @HasColimitsOfShape.has_colimit _ _ _ _
    ((countableColimits.{t, u} Y R).has_colimits_of_shape _) _

namespace TwoTermCoordinates

attribute [local irreducible] SheafOfModules.monoidalCategory totalTensor
  twoTermHomIso twoTermHomComponentIso twoTermTensorIso

/-- Sectionwise coordinate calculus. Source: Stacks 03EK and 0A8X.
(blueprint: lem-sf-two-term-hom-coordinate-evaluation). -/
noncomputable def localEvaluation (M N : Modules.{t, u} Y R)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) :
    (SheafOfModules.homObj (R := R) M N).val.obj U →ₗ[R.obj.obj U]
      M.val.obj U →ₗ[R.obj.obj U] N.val.obj U :=
  { toFun := fun φ ↦ (φ.app (op (Over.mk (𝟙 U.unop)))).hom
    map_add' := fun _ _ ↦ rfl
    map_smul' := by
      intro r φ
      ext x
      rw [PresheafOfModules.smul_app, ModuleCat.hom_comp, LinearMap.comp_apply,
        PresheafOfModules.sectionsSMul_app_apply, PresheafOfModules.overSections_coe_apply]
      simp }

/-- Evaluation is linear evaluation after the indicated Hom product projection.
Source: Stacks 03EO and 0A8X
(blueprint: lem-sf-two-term-hom-coordinate-evaluation). -/
theorem localEvaluation_π (P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (j p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (w : ((homComplex (R := R) P I).X j).val.obj U) (x : (P.X p).val.obj U) :
    localEvaluation Y R (P.X p) (I.X (p + j)) U
      ((homComplexπ (R := R) P I j p (p + j) rfl).val.app U w) x =
        evaluate Y R P I j p U w x := by
  rfl

attribute [local irreducible] evaluate projection homComplexπ

/-- Sectionwise coordinate calculus. Source: Stacks 03EK and 0A8X.
(blueprint: lem-sf-two-term-hom-coordinate-evaluation). -/
theorem post_evaluation (M N N' : Modules.{t, u} Y R) (g : N ⟶ N')
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (SheafOfModules.homObj (R := R) M N).val.obj U) (x : M.val.obj U) :
    localEvaluation Y R M N' U
        ((((SheafOfModules.homFunctor R).obj (op M)).map g).val.app U v) x =
      g.val.app U (localEvaluation Y R M N U v x) := by
  rfl

/-- Sectionwise coordinate calculus. Source: Stacks 03EK and 0A8X.
(blueprint: lem-sf-two-term-hom-coordinate-evaluation). -/
theorem parity_evaluation (M N : Modules.{t, u} Y R) (p : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (v : (SheafOfModules.homObj (R := R) M N).val.obj U) (x : M.val.obj U) :
    localEvaluation Y R M N U ((parityIso Y R _ p).hom.val.app U v) x =
      p.negOnePow • localEvaluation Y R M N U v x := by
  change localEvaluation Y R M N U
    ((p.negOnePow • 𝟙 (SheafOfModules.homObj (R := R) M N)).val.app U v) x = _
  rw [Units.smul_def, RingedDerivedNative.zsmul_apply]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
    map_zsmul, LinearMap.smul_apply, Units.smul_def]

variable (Q : CochainComplex (Modules.{t, u} Y R) ℤ)
  (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
  (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
  (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R)))

/-- Sectionwise coordinate calculus. Source: Stacks 03EK and 0A8X.
(blueprint: lem-sf-two-term-hom-coordinate-evaluation). -/
theorem hom_fst_evaluation
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) (j p : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (w : ((homComplex (R := R) P (((totalTensor Y R).obj I).obj Q)).X j).val.obj U)
    (x : (P.X p).val.obj U) :
    localEvaluation Y R (P.X p) (I.X (p + (j + 1))) U
      ((((twoTermHomIso Y R P I Q hzero eNeg eZero j).hom ≫ biprod.fst ≫
        homComplexπ (R := R) P I (j + 1) p (p + (j + 1)) rfl).val.app U) w) x =
      p.negOnePow • (eqToHom (congrArg I.X (add_assoc p j 1))).val.app U
        ((((twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)).hom ≫
          biprod.fst).val.app U) (evaluate Y R P (((totalTensor Y R).obj I).obj Q)
            j p U w x)) := by
  rw [twoTermHomIso_hom_fst_π, twoTermHomComponentIso_hom_fst]
  erw [show ((homComplexπ (R := R) P (((totalTensor Y R).obj I).obj Q) j p (p + j) rfl ≫
      ((SheafOfModules.homFunctor R).obj (op (P.X p))).map
        ((twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)).hom ≫ biprod.fst ≫
          eqToHom (congrArg I.X (add_assoc p j 1))) ≫ (parityIso Y R _ p).hom).val.app U w) =
      (parityIso Y R _ p).hom.val.app U
        ((((SheafOfModules.homFunctor R).obj (op (P.X p))).map
          ((twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)).hom ≫ biprod.fst ≫
            eqToHom (congrArg I.X (add_assoc p j 1)))).val.app U
              ((homComplexπ (R := R) P (((totalTensor Y R).obj I).obj Q) j p (p + j) rfl).val.app
                U w)) by rfl]
  erw [parity_evaluation, post_evaluation]
  rw [localEvaluation_π]
  rfl

/-- Sectionwise coordinate calculus. Source: Stacks 03EK and 0A8X.
(blueprint: lem-sf-two-term-hom-coordinate-evaluation). -/
theorem hom_snd_evaluation
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) (j p : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (w : ((homComplex (R := R) P (((totalTensor Y R).obj I).obj Q)).X j).val.obj U)
    (x : (P.X p).val.obj U) :
    localEvaluation Y R (P.X p) (I.X (p + j)) U
      ((((twoTermHomIso Y R P I Q hzero eNeg eZero j).hom ≫ biprod.snd ≫
        homComplexπ (R := R) P I j p (p + j) rfl).val.app U) w) x =
      (((twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)).hom ≫
        biprod.snd).val.app U) (evaluate Y R P (((totalTensor Y R).obj I).obj Q)
          j p U w x) := by
  rw [twoTermHomIso_hom_snd_π, twoTermHomComponentIso_hom_snd]
  change localEvaluation Y R _ _ U
    ((((SheafOfModules.homFunctor R).obj (op (P.X p))).map _).val.app U
      ((homComplexπ (R := R) P (((totalTensor Y R).obj I).obj Q) j p (p + j) rfl).val.app U w)) x =
      _
  rw [post_evaluation, localEvaluation_π]

end TwoTermCoordinates

end WeilConjectures.IntegralHom
