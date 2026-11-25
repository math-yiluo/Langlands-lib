/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryTensorRepresentatives
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # Common K-flat roofs for ordinary tensor resolutions

Source: Stacks 06YS, 06YU; blueprint step 1 of
`lem-sf-native-weil-tensor-ringed-derived-square-ordinary-resolution-extension`.
(blueprint: lem-sf-native-weil-tensor-resolution-roof)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open scoped ZeroObject
namespace AlgebraicGeometry.ProEtaleWeilSheaf

set_option linter.unusedVariables false in
/--
Every map of second complexes admits a common K-flat roof whose two
augmentations are quasi-isomorphisms and whose comparison commutes up to a
chain homotopy.

Source: Stacks Tags 06YS and 06YU, common K-flat roof paragraph.  Resolve the
middle object of a homotopy-category common refinement by a K-flat complex and
compose its augmentation with the two refinement legs.  Two-out-of-three
preserves the quasi-isomorphism assertions, while the refinement equality
lifts to the displayed homotopy.
(blueprint: lem-sf-native-weil-tensor-resolution-roof)
-/
theorem native_ordinary_tensor_model_resolution_roof
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ∀ (Q Q' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (g : Q ⟶ Q'),
      ∃ (K K' : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (hK : NativeOrdinaryKFlat l Y K)
        (hK' : NativeOrdinaryKFlat l Y K')
        (q : K ⟶ Q) (q' : K' ⟶ Q') (u : K ⟶ K'),
        QuasiIso q ∧ QuasiIso q' ∧ Nonempty (Homotopy (u ≫ q') (q ≫ g)) := by
  -- Keep the existing flat resolution functorial: its natural augmentation already
  -- supplies a strict square, so no homotopy-category common refinement is needed.
  classical
  let A := ProEtale.AdicSheaf l Y
  let : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  have : HasExactColimitsOfShape ℤ A := by
    have := AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} A
    infer_instance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ A) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by
    intro i j
    infer_instance
  have (X₁ X₂ X₃ : GradedObject ℤ A) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by
    intro i j
    infer_instance
  have (X₁ X₂ X₃ : GradedObject ℤ A) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by
    intro i j
    infer_instance
  have (M : A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor A).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by
        intros
        simp [MonoidalCategory.curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  have hflat (Q : CochainComplex A ℤ) :
      NativeOrdinaryKFlat l Y (Λ.resolutionFunctor.obj Q) := by
    have hK := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le Q
    intro N hN
    let T := MonoidalCategory.tensorRight (Λ.resolutionFunctor.obj Q)
    have hz : (0 : CochainComplex A ℤ).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)
    have hs : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ N) :=
      ⟨fun i ↦ (quasiIsoAt_iff_exactAt _ i (hz i)).2 (hN i)⟩
    have ht : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ N)) := hK.2 _ hs
    have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    have htarget : (T.obj N).Acyclic :=
      fun i ↦ (exactAt_iff_of_quasiIsoAt
        (T.map (0 : (0 : CochainComplex A ℤ) ⟶ N)) i).1 (htzero i)
    intro i
    exact (htarget i).of_iso
      (GenericOrdinaryTensor.ordinaryTotalIso (Λ.resolutionFunctor.obj Q) N).symm
  intro Q Q' g
  refine ⟨Λ.resolutionFunctor.obj Q, Λ.resolutionFunctor.obj Q', hflat Q, hflat Q',
    Λ.resolutionNatTrans.app Q, Λ.resolutionNatTrans.app Q', Λ.resolutionFunctor.map g,
    inferInstance, inferInstance, ?_⟩
  exact ⟨Homotopy.ofEq (Λ.resolutionNatTrans.naturality g)⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
