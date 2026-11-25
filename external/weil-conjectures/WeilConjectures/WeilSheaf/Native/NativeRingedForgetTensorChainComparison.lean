/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorChainAssociativity

/-! # The normalized ringed restriction comparison on complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

-- Keep the large total-complex comparison abstract so concrete sheaf tensor
-- presentations are not unfolded while elaborating its coherence proof.
private theorem nativeChainTensorComparison
    {B : Type*} [Category* B] [Preadditive B] [HasZeroObject B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (U : B ⥤ A) [U.Additive]
    [∀ I : Type, PreservesColimitsOfShape (Discrete I) U]
    (ν : MonoidalCategory.tensor B ⋙ U ≅ (U.prod U) ⋙ MonoidalCategory.tensor A)
    (βB : SymmetricCategory B) (βA : SymmetricCategory A)
    (coherence : RingedForgetTensorTransposition.TensorCoherence
      inferInstance inferInstance βB βA U ν) :
    let F := U.mapHomologicalComplex (.up ℤ)
    ∃ ε : MonoidalCategory.tensor (CochainComplex B ℤ) ⋙ F ≅
        F.prod F ⋙ MonoidalCategory.tensor (CochainComplex A ℤ),
      (∀ (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
        U.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (ε.hom.app (P, Q)).f n =
          ν.hom.app (P.X p, Q.X q) ≫
            HomologicalComplex.ιTensorObj (F.obj P) (F.obj Q) p q n h) ∧
      (∀ P Q N : CochainComplex B ℤ,
        F.map (α_ P Q N).hom ≫ ε.hom.app (P, Q ⊗ N) ≫
            (F.obj P ◁ ε.hom.app (Q, N)) =
          ε.hom.app (P ⊗ Q, N) ≫ (ε.hom.app (P, Q) ▷ F.obj N) ≫
            (α_ (F.obj P) (F.obj Q) (F.obj N)).hom) := by
  let e : Functor.uncurry.obj (curriedTensor B) ⋙ U ≅
      (U.prod U) ⋙ Functor.uncurry.obj (curriedTensor A) :=
    Functor.isoWhiskerRight RingedForgetTensorTransposition.uncurryTensorIso U ≪≫
      ν ≪≫ Functor.isoWhiskerLeft (U.prod U)
        RingedForgetTensorTransposition.uncurryTensorIso.symm
  have he (P Q : B) : e.hom.app (P, Q) = ν.hom.app (P, Q) := by
    change U.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  let δ := RingedForgetTensorTransposition.totalComparisonNatIso
    (curriedTensor B) (curriedTensor A) U e
  let F := U.mapHomologicalComplex (.up ℤ)
  let iB : Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex) ≅
      MonoidalCategory.tensor (CochainComplex B ℤ) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨f, g⟩
      simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, tensor_map] using
        (RingedForgetTensorTransposition.tensor_map₂_eq f g))
  let iA : Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex) ≅
      MonoidalCategory.tensor (CochainComplex A ℤ) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      rintro ⟨P, Q⟩ ⟨P', Q'⟩ ⟨f, g⟩
      simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, tensor_map] using
        (RingedForgetTensorTransposition.tensor_map₂_eq f g))
  let ε := Functor.isoWhiskerRight iB.symm F ≪≫ δ ≪≫
    Functor.isoWhiskerLeft (F.prod F) iA
  have hε (P Q : CochainComplex B ℤ) : ε.hom.app (P, Q) = δ.hom.app (P, Q) := by
    change F.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hs (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n) :
      U.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
          (δ.hom.app (P, Q)).f n =
        ν.hom.app (P.X p, Q.X q) ≫
          HomologicalComplex.ιTensorObj (F.obj P) (F.obj Q) p q n h := by
    exact (RingedForgetTensorTransposition.totalComparison_summand
      (curriedTensor B) (curriedTensor A) U e P Q p q n h).trans
        (by rw [he])
  refine ⟨ε, ?_, ?_⟩
  · intro P Q p q n h
    rw [hε]
    exact hs P Q p q n h
  · intro P Q N
    have hν (P Q N : B) :
        (ν.inv.app (P, Q) ▷ U.obj N) ≫
            ν.inv.app (P ⊗ Q, N) ≫ U.map (α_ P Q N).hom =
          (α_ (U.obj P) (U.obj Q) (U.obj N)).hom ≫
            (U.obj P ◁ ν.inv.app (Q, N)) ≫
              ν.inv.app (P, Q ⊗ N) := by
      apply (cancel_epi (ν.hom.app (P ⊗ Q, N) ≫
        (ν.hom.app (P, Q) ▷ U.obj N))).1
      apply (cancel_mono (ν.hom.app (P, Q ⊗ N) ≫
        (U.obj P ◁ ν.hom.app (Q, N)))).1
      have hr : (ν.hom.app (P, Q) ▷ U.obj N) ≫
          (ν.inv.app (P, Q) ▷ U.obj N) = 𝟙 _ := by
        rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight]
      have hl : (U.obj P ◁ ν.inv.app (Q, N)) ≫
          (U.obj P ◁ ν.hom.app (Q, N)) = 𝟙 _ := by
        rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
          MonoidalCategory.whiskerLeft_id]
      simp only [Category.assoc, reassoc_of% hr, hl,
        Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
      erw [Category.comp_id]
      have h := coherence.associativity P Q N
      simp only [tensor_map] at h
      erw [tensorHom_id, id_tensorHom] at h
      exact h
    have hsε (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n) :
        U.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫
            (ε.hom.app (P, Q)).f n =
          ν.hom.app (P.X p, Q.X q) ≫
            HomologicalComplex.ιTensorObj (F.obj P) (F.obj Q) p q n h := by
      rw [hε]
      exact hs P Q p q n h
    have h := RingedForgetTensorTransposition.chain_inverse_associativity
      U ν ε hsε hν P Q N
    apply (cancel_epi ((ε.inv.app (P, Q) ▷ F.obj N) ≫
      ε.inv.app (P ⊗ Q, N))).1
    simp only [Category.assoc]
    rw [reassoc_of% h]
    have hl : (F.obj P ◁ ε.inv.app (Q, N)) ≫
        (F.obj P ◁ ε.hom.app (Q, N)) = 𝟙 _ := by
      rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
        MonoidalCategory.whiskerLeft_id]
    have hr : (ε.inv.app (P, Q) ▷ F.obj N) ≫
        (ε.hom.app (P, Q) ▷ F.obj N) = 𝟙 _ := by
      rw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight]
    simp only [Iso.inv_hom_id_app_assoc]
    erw [hl, Category.comp_id, reassoc_of% hr]

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)

set_option synthInstance.maxHeartbeats 200000 in
-- Elaborate the two site tensors through their comparison APIs.
set_option maxHeartbeats 1200000 in
-- The independently chosen site tensors require large definitional equalities.
set_option genInjectivity false in
set_option genSizeOfSpec false in
-- The two independently chosen site tensors occur in the same field.
/-- The normalized restriction tensorator and its associativity equation.
Source: Stacks 06YN and 0FPT
(blueprint: new-sf-native-ringed-forget-tensor-chain-comparison). -/
structure NativeRingedForgetTensorChainComparison where
  tensor : MonoidalCategory.tensor
      (CochainComplex (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) ℤ) ⋙
        b.forget.mapHomologicalComplex (.up ℤ) ≅
    (b.forget.mapHomologicalComplex (.up ℤ)).prod
      (b.forget.mapHomologicalComplex (.up ℤ)) ⋙ MonoidalCategory.tensor
        (CochainComplex (RingedTensorModules.{u + 1, u + 1, u + 1} b.K b.Q) ℤ)
  summand (P Q : CochainComplex (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) ℤ)
      (p q n : ℤ) (h : p + q = n) :
    b.forget.map (RingedForgetTensorTransposition.tensorSummand b.J b.R P Q p q n h) ≫
        (tensor.hom.app (P, Q)).f n =
      b.underived.tensor.hom.app (P.X p, Q.X q) ≫
        RingedForgetTensorTransposition.tensorSummand b.K b.Q
          ((b.forget.mapHomologicalComplex (.up ℤ)).obj P)
          ((b.forget.mapHomologicalComplex (.up ℤ)).obj Q) p q n h
  associativity (P Q N :
      CochainComplex (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) ℤ) :
    let F := b.forget.mapHomologicalComplex (.up ℤ)
    F.map (α_ P Q N).hom ≫ tensor.hom.app (P, Q ⊗ N) ≫
        (F.obj P ◁ tensor.hom.app (Q, N)) =
      tensor.hom.app (P ⊗ Q, N) ≫ (tensor.hom.app (P, Q) ▷ F.obj N) ≫
        (α_ (F.obj P) (F.obj Q) (F.obj N)).hom

-- Elaborate the two site tensors through their comparison APIs.
-- The independently chosen site tensors require large definitional equalities.
-- Elaborate the two site tensors through their comparison APIs.
/-- Restriction has the comparison obtained by summing its underived tensorators.
Its summand equations determine it uniquely.
Source: Stacks 06YN and 0FPT
(blueprint: new-sf-native-ringed-forget-tensor-chain-comparison).

Proof: curry the underived tensorator and apply the generic total-complex
comparison. Convert between the curried tensor total and the monoidal tensor by
its identity-component natural isomorphism. The generic summand formula gives
the stated normalization. Cancel the underived isomorphisms to put their
associativity in inverse form; the generic triple-summand associativity theorem
then gives associativity on complexes. -/
theorem native_ringed_forget_tensor_chain_comparison :
    Nonempty (NativeRingedForgetTensorChainComparison b) := by
  let B := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R
  let A := RingedTensorModules.{u + 1, u + 1, u + 1} b.K b.Q
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.Q
  let : MonoidalCategory B := SheafOfModules.monoidalCategory b.R
  let : MonoidalCategory A := SheafOfModules.monoidalCategory b.Q
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients b.R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients b.R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients b.Q
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients b.Q
  have (I : Type) : PreservesColimitsOfShape (Discrete I) b.forget :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift.{u + 1, 0} : ULift.{u + 1} I ≃ I)) b.forget
  obtain ⟨ε, hs, ha⟩ := nativeChainTensorComparison b.forget b.underived.tensor
    (SheafOfModules.symmetricCategory b.R) (SheafOfModules.symmetricCategory b.Q)
    b.underived.coherence
  refine ⟨{ tensor := ε, summand := ?_, associativity := ha }⟩
  intro P Q p q n h
  exact hs P Q p q n h

end AlgebraicGeometry.ProEtaleWeilSheaf
