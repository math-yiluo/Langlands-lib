/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermHomCoordinates
import WeilConjectures.SixFunctors.IntegralHom.TwoTermCoordinates.TwoTermTensorCoordinateSections
import WeilConjectures.SixFunctors.IntegralHom.TwoTermCoordinates.TwoTermHomCoordinateEvaluation
import WeilConjectures.SixFunctors.IntegralHom.Tensor.TensorHomEvaluationExt

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

local instance twoTermCoordinateEvaluationLocal1 :
    MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.monoidalCategory R

local instance twoTermCoordinateEvaluationLocal2 : HasBinaryBiproducts (Modules.{t, u} Y R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

local instance twoTermCoordinateEvaluationLocal3 :
    HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  countableColimits Y R

local instance twoTermCoordinateEvaluationLocal4 :
    (ordinaryTensor Y R).PreservesZeroMorphisms :=
  ordinaryTensorZero Y R

local instance twoTermCoordinateEvaluationLocal5 (M : Modules.{t, u} Y R) :
    ((ordinaryTensor Y R).obj M).PreservesZeroMorphisms := ordinaryTensorObjZero Y R M

local instance twoTermCoordinateEvaluationLocal6 (K L : CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex.HasMapBifunctor K L (ordinaryTensor Y R) := fun _j ↦
  @HasColimitsOfShape.has_colimit _ _ _ _
    ((countableColimits.{t, u} Y R).has_colimits_of_shape _) _
open TwoTermCoordinates

/-- Test a total-tensor component after postcomposition into a Hom-complex term.
The tensor and Hom extensionality reductions are shared by all four coordinates. -/
private theorem twoTermCoordinate_component_ext
    (A Q P I : CochainComplex (Modules.{t, u} Y R) ℤ)
    (a b j n : ℤ) (hab : a + b = j) {N T : Modules.{t, u} Y R}
    (f : (((totalTensor Y R).obj A).obj Q).X j ⟶ N)
    {g : N ⟶ T} {g' : (((totalTensor Y R).obj A).obj Q).X j ⟶ T}
    {π : T ⟶ (homComplex (R := R) P I).X n}
    (h : ∀ (p : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (v : (A.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
      localEvaluation Y R _ _ U
        ((g ≫ π ≫ homComplexπ (R := R) P I n p (p + n) rfl).val.app U
          (f.val.app U (generator Y R A Q a b j hab U v z))) x =
      localEvaluation Y R _ _ U
        ((homComplexπ (R := R) P I n p (p + n) rfl).val.app U
          ((g' ≫ π).val.app U (generator Y R A Q a b j hab U v z))) x) :
    (CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b j hab ≫ f ≫ g) ≫ π =
      (CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b j hab ≫ g') ≫ π := by
  apply homComplex_hom_ext (R := R)
  intro p q hpq
  subst q
  apply tensorHomEvaluation_ext.{t + 1, t, u} R
  intro U v z x
  exact h p U v z x

attribute [local irreducible] SheafOfModules.monoidalCategory
  twoTermHomIso twoTermHomComponentIso twoTermTensorIso
  projection homComplexπ evaluate totalTensor

variable (Q : CochainComplex (Modules.{t, u} Y R) ℤ)

/-- A homogeneous signed evaluation map has the two invertible finite coordinates.
Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1; Stacks 0A8X.
(blueprint: lem-sf-two-term-coordinate-evaluation).
Proof: compose with the signed target coordinates and compare with the source
coordinates. The total coproduct reduces this to coefficient degrees -1 and 0;
all other source summands vanish. Project to each Hom factor and test on local
pure tensors. In degree -1, contraction with eNeg and the right unitor gives
its scalar times the input. The two parity signs cancel. In degree zero the
same contraction uses eZero and has no sign. The opposite projections vanish.
Tensor evaluation extensionality and the product universal properties give
the comparison identity. Both coordinate maps are isomorphisms, hence so is f.
The proof includes zero modules and the zero ring and assumes nothing about
the differentials or boundedness of P and I. -/
theorem twoTermCoordinate_isIso
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R)))
    (P I : CochainComplex (Modules.{t, u} Y R) ℤ) (j : ℤ)
    (f : (((totalTensor Y R).obj (homComplex (R := R) P I)).obj Q).X j ⟶
      (homComplex (R := R) P (((totalTensor Y R).obj I).obj Q)).X j)
    (hf : ∀ (a b : ℤ) (hab : a + b = j) (p : ℤ)
      (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (v : ((homComplex (R := R) P I).X a).val.obj U)
      (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U),
      evaluate Y R P (((totalTensor Y R).obj I).obj Q) j p U
        (f.val.app U ((eqToHom (congrArg
          (fun k ↦ (((totalTensor Y R).obj (homComplex (R := R) P I)).obj Q).X k)
          hab)).val.app U (totalPair Y R (homComplex (R := R) P I) Q a b U v z))) x =
        (b * p).negOnePow •
          ((eqToHom (congrArg (fun k ↦ (((totalTensor Y R).obj I).obj Q).X k)
            (by omega : (p + a) + b = p + j))).val.app U
              (totalPair Y R I Q (p + a) b U (evaluate Y R P I a p U v x) z))) : IsIso f := by
  let H := homComplex (R := R) P I
  have hgen (a b : ℤ) (hab : a + b = j) (p : ℤ)
      (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (v : (H.X a).val.obj U) (z : (Q.X b).val.obj U) (x : (P.X p).val.obj U) :
      evaluate Y R P (((totalTensor Y R).obj I).obj Q) j p U
        (f.val.app U (generator Y R H Q a b j hab U v z)) x =
        (b * p).negOnePow • generator Y R I Q (p + a) b (p + j) (by omega) U
          (evaluate Y R P I a p U v x) z := by
    have hh := hf a b hab p U v z x
    rw [TwoTermCoordinates.generator_transport Y R (homComplex (R := R) P I) Q
      a b j hab U v z] at hh
    rw [TwoTermCoordinates.generator_transport Y R I Q (p + a) b (p + j)
      (by omega) U (evaluate Y R P I a p U v x) z] at hh
    exact hh
  have he : f ≫ (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom =
      (twoTermTensorIso Y R H Q hzero eNeg eZero j).hom := by
    apply totalTensor_hom_ext Y R H Q _ j
    intro a b hab
    change a + b = j at hab
    by_cases hb : b = -1
    · subst b
      obtain rfl : a = j + 1 := by omega
      apply biprod.hom_ext
      · refine twoTermCoordinate_component_ext Y R H Q P I (j + 1) (-1) j (j + 1) hab f
          (g := (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom)
          (g' := (twoTermTensorIso Y R H Q hzero eNeg eZero j).hom)
          (π := biprod.fst) ?_
        intro p U v z x
        rw [hom_fst_evaluation, generator_neg_fst]
        have hs := hgen (j + 1) (-1) (by omega) p U v z x
        rw [hs]
        simp only [neg_one_mul, Int.negOnePow_neg, Units.smul_def, map_zsmul]
        rw [generator_neg_fst_transport]
        simp only [smul_smul, ← Units.val_mul]
        simp only [map_smul, LinearMap.smul_apply]
        rw [localEvaluation_π]
        simp
      · refine twoTermCoordinate_component_ext Y R H Q P I (j + 1) (-1) j j hab f
          (g := (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom)
          (g' := (twoTermTensorIso Y R H Q hzero eNeg eZero j).hom)
          (π := biprod.snd) ?_
        intro p U v z x
        rw [hom_snd_evaluation, generator_neg_snd]
        have hs := hgen (j + 1) (-1) (by omega) p U v z x
        rw [hs]
        simp only [Units.smul_def, map_zsmul]
        rw [generator_neg_snd_general]
        simp only [smul_zero, map_zero, LinearMap.zero_apply]
    · by_cases hb' : b = 0
      · subst b
        have ha : a = j := by omega
        subst a
        apply biprod.hom_ext
        · refine twoTermCoordinate_component_ext Y R H Q P I j 0 j (j + 1) hab f
            (g := (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom)
            (g' := (twoTermTensorIso Y R H Q hzero eNeg eZero j).hom)
            (π := biprod.fst) ?_
          intro p U v z x
          rw [hom_fst_evaluation, generator_zero_fst]
          have hs := hgen j 0 (by simp) p U v z x
          rw [hs]
          simp only [zero_mul, Int.negOnePow_zero, one_smul]
          rw [generator_zero_fst]
          simp only [map_zero, LinearMap.zero_apply, smul_zero]
        · refine twoTermCoordinate_component_ext Y R H Q P I j 0 j j hab f
            (g := (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom)
            (g' := (twoTermTensorIso Y R H Q hzero eNeg eZero j).hom)
            (π := biprod.snd) ?_
          intro p U v z x
          rw [hom_snd_evaluation, generator_zero_snd]
          have hs := hgen j 0 (by simp) p U v z x
          rw [hs]
          simp only [zero_mul, Int.negOnePow_zero, one_smul]
          rw [generator_zero_snd]
          simp only [map_smul, LinearMap.smul_apply]
          rw [localEvaluation_π]
      · exact (((ordinaryTensor Y R).obj (H.X a)).map_isZero
          (hzero b hb hb')).eq_of_src _ _
  let : IsIso (f ≫ (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right f
    (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom

end WeilConjectures.IntegralHom
