/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import all WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
import WeilConjectures.WeilSheaf.Native.NativeHomRepresentativeExistence
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorGeometry
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRepresentativeCurrying
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorEvaluation

/-! # A normalized ringed tensor model before comparison with a supplied left adjoint

Source: Stacks 06YS, 08J9 and 0FPT; native constraint lifting, geometric model step.
-/

@[expose] public section
set_option autoImplicit false
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

private theorem uncurry_eq
    {C : Type a} [Category.{b} C] {H : Cᵒᵖ × C ⥤ C}
    (W : CoefficientClosedStructure H) (A K L : C) (f : A ⟶ H.obj (op K, L)) :
    (W.transpose A K L).symm f = W.tensor.map (f, 𝟙 K) ≫ W.evaluation K L := by
  let := W.monoidal
  simp [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, MonoidalCategory.tensor]

private theorem uncurry_of_evaluation
    {C D : Type a} [Category.{b} C] [Category.{b} D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (W : CoefficientClosedStructure H) (S : CoefficientClosedStructure H')
    (F : C ⥤ D) (t : W.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (χ : H ⋙ F ≅ F.op.prod F ⋙ H')
    (he : ∀ K L, F.map (W.evaluation K L) =
      t.hom.app (H.obj (op K, L), K) ≫
        S.tensor.map
          (X := (F.obj (H.obj (op K, L)), F.obj K))
          (Y := (H'.obj (op (F.obj K), F.obj L), F.obj K))
          (Prod.mkHom (χ.hom.app (op K, L)) (𝟙 (F.obj K))) ≫
          S.evaluation (F.obj K) (F.obj L))
    (A K L : C) (f : A ⟶ H.obj (op K, L)) :
    (S.transpose (F.obj A) (F.obj K) (F.obj L)).symm
        (F.map f ≫ χ.hom.app (op K, L)) =
      t.inv.app (A, K) ≫ F.map ((W.transpose A K L).symm f) := by
  have hn : F.map (W.tensor.map (f, 𝟙 K)) ≫ t.hom.app (H.obj (op K, L), K) =
      t.hom.app (A, K) ≫ S.tensor.map
        (X := (F.obj A, F.obj K)) (Y := (F.obj (H.obj (op K, L)), F.obj K))
        (Prod.mkHom (F.map f) (𝟙 (F.obj K))) := by
    simpa using t.hom.naturality (Prod.mkHom f (𝟙 K))
  rw [uncurry_eq, uncurry_eq, F.map_comp, he]
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← S.tensor.map_comp_assoc]
  congr 2
  exact Prod.ext rfl (Category.id_comp _).symm

private theorem unit_mate_of_uncurry
    {C D : Type a} [Category.{b} C] [Category.{b} D]
    {H : Cᵒᵖ × C ⥤ C} {H' : Dᵒᵖ × D ⥤ D}
    (W : CoefficientClosedStructure H) (S : CoefficientClosedStructure H')
    (F : C ⥤ D) (t : W.tensor ⋙ F ≅ F.prod F ⋙ S.tensor)
    (χ : H ⋙ F ≅ F.op.prod F ⋙ H')
    (hu : ∀ (A K L : C) (f : A ⟶ H.obj (op K, L)),
      (S.transpose (F.obj A) (F.obj K) (F.obj L)).symm
          (F.map f ≫ χ.hom.app (op K, L)) =
        t.inv.app (A, K) ≫ F.map ((W.transpose A K L).symm f)) :
    ∀ A K, t.inv.app (A, K) =
      (S.transpose (F.obj A) (F.obj K) (F.obj (W.tensor.obj (A, K)))).symm
        (F.map ((W.adjunction K).unit.app A) ≫ χ.hom.app (op K, W.tensor.obj (A, K))) := by
  intro A K
  have h := hu A K (W.tensor.obj (A, K)) ((W.adjunction K).unit.app A)
  have hi : (W.transpose A K (W.tensor.obj (A, K))).symm
      ((W.adjunction K).unit.app A) = 𝟙 _ := (W.adjunction K).homEquiv_symm_unit A
  have hm : F.map ((W.transpose A K (W.tensor.obj (A, K))).symm
      ((W.adjunction K).unit.app A)) = 𝟙 (F.obj (W.tensor.obj (A, K))) :=
    (congrArg (fun f ↦ F.map f) hi).trans (F.map_id _)
  exact (h.trans ((congrArg (fun f ↦ t.inv.app (A, K) ≫ f) hm).trans
    (Category.comp_id _))).symm

namespace AlgebraicGeometry.ProEtaleWeilSheaf
private theorem normalization_from_currying
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A] [HasDerivedCategory.{b} A]
    (H₀ : Aᵒᵖ ⥤ A ⥤ A) [H₀.Additive] [∀ P, (H₀.obj P).Additive]
    (T : A ⥤ A ⥤ A) [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : ∀ P, T.obj P ⊣ H₀.obj (op P))
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H₀ H) (S : CoefficientClosedStructure H)
    (flat : CochainComplex A ℤ → Prop)
    (model : ∀ P Q : CochainComplex A ℤ, flat P →
      (S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q T)))
    (e : ∀ B K L : DerivedCategory A,
      (S.tensor.obj (B, K) ⟶ L) ≃ (B ⟶ H.obj (op K, L)))
    (he : ∀ B K L, S.transpose B K L = e B K L)
    (hmodel :
      ∀ (P Q I : CochainComplex A ℤ) (hP : flat P) (_hQ : flat Q)
      (hI : I.IsKInjective) (φ : Q ⟶ CochainComplex.bifunctorHomObj H₀ P I),
      ∃ ψ : CochainComplex.mapBifunctor P Q T ⟶ I,
        (∀ (p q n : ℤ) (hpq : p + q = n),
          HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq ≫ ψ.f n =
            (T.obj (P.X p)).map (φ.f q ≫
                CochainComplex.bifunctorHomπ H₀ P I q p n hpq) ≫
              (adj (P.X p)).counit.app (I.X n)) ∧
        (model P Q hP).hom ≫ DerivedCategory.Q.map ψ =
          (e (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj I)).symm
              (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv)) :
    NativeAdjunctionNormalization H₀ T adj H R S flat model := by
  intro P Q I hP hQ hI φ
  obtain ⟨ψ, hψ, hloc⟩ := hmodel P Q I hP hQ hI φ
  refine ⟨ψ, hψ, ?_⟩
  exact hloc.trans (congrArg
    (fun f ↦ f.symm (DerivedCategory.Q.map φ ≫ (R.model P I hI).inv))
    (he (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj I)).symm)

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Keep the large existential goal folded during witness elimination. -/
private def TensorModelConclusion
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal) : Prop :=
    ∃ W : CoefficientClosedStructure M.weilHom,
    ∃ γ : @SymmetricCategory _ _ W.monoidal,
    ∃ δ : W.monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ t : W.tensor ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence W.monoidal S.monoidal
      γ β (nativeForget k₀ l X) t,
      c.unit = (nativeForget k₀ l X).mapIso δ ≪≫
        ((Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X)) ≪≫ ε.symm ∧
      NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ ∧
      (∀ A K, t.inv.app (A, K) =
        (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
          ((nativeForget k₀ l X).obj (W.tensor.obj (A, K)))).symm
            ((nativeForget k₀ l X).map ((W.adjunction K).unit.app A) ≫
              χ.hom.app (op K, W.tensor.obj (A, K))))

private theorem tensorModelConclusion_iff
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal) :
    TensorModelConclusion k₀ l X M S β ↔
    ∃ W : CoefficientClosedStructure M.weilHom,
    ∃ γ : @SymmetricCategory _ _ W.monoidal,
    ∃ δ : W.monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ t : W.tensor ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence W.monoidal S.monoidal
      γ β (nativeForget k₀ l X) t,
      c.unit = (nativeForget k₀ l X).mapIso δ ≪≫
        ((Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X)) ≪≫ ε.symm ∧
      NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ ∧
      (∀ A K, t.inv.app (A, K) =
        (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
          ((nativeForget k₀ l X).obj (W.tensor.obj (A, K)))).symm
            ((nativeForget k₀ l X).map ((W.adjunction K).unit.app A) ≫
              χ.hom.app (op K, W.tensor.obj (A, K)))) := Iff.rfl

attribute [local irreducible] TensorModelConclusion

/-- The action-site tensor model and its normalized comparisons, before imposing
any supplied native tensor bifunctor or adjunction. In particular no assertion
about constraints on an arbitrary T is included.

Source: native constraint lifting, steps 1 and 3; Stacks 06YS, 08J9, 0FPT
(blueprint: lem-sf-native-weil-ringed-tensor-model).

Proof: obtain the symmetric native tensor, coherent tensor comparison, units
and explicit complex presentation from native_weil_tensor_geometry. Independently
construct chi for the prescribed Hom representatives by rebasing the existing
standard two-injective comparison through the row-sign isomorphisms. Apply
native_weil_representative_currying to the presentation: the underived adjunction
and the K-flat and K-injective localizations give natural derived currying,
including the homogeneous uncurrying formula. Construct W by
closed_of_natural_currying; its transpose is precisely this descended bijection.
The representative formula therefore supplies its adjunction normalization.
Apply native_weil_tensor_evaluation to obtain the forgotten evaluation square.
For any f:A to Hom(K,L), inverse transposition is tensor(f,identity) followed
by evaluation. Naturality of t and its inverse cancel the tensor comparison,
so this evaluation square gives the full normalized uncurrying identity.
Specialize to the adjunction unit at A. Its inverse transpose is identity by
the triangle identity, leaving exactly the displayed formula for t inverse.
The geometry step already supplies the four coherence equations and the
precise coefficient-unit factorization. No change to the target statement,
source categories, unboundedness or zero/empty-site cases is made. -/
theorem native_weil_ringed_tensor_model
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (β : @SymmetricCategory _ _ S.monoidal)
    (hmonoidal : S.monoidal = (inferInstance : MonoidalCategory
      (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))))
    (hS : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      M.ordinaryHom M.ordinaryRepresentatives S β) :
    ∃ W : CoefficientClosedStructure M.weilHom,
    ∃ γ : @SymmetricCategory _ _ W.monoidal,
    ∃ δ : W.monoidal.tensorUnit ≅
      (DerivedCategory.singleFunctor _ 0).obj (adicConstant k₀ l X),
    ∃ ε : S.monoidal.tensorUnit ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber),
    ∃ t : W.tensor ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    ∃ χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom,
    ∃ c : RingedForgetTensorTransposition.TensorCoherence W.monoidal S.monoidal
      γ β (nativeForget k₀ l X) t,
      c.unit = (nativeForget k₀ l X).mapIso δ ≪≫
        ((Functor.mapDerivedCategorySingleFunctor
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) 0).app
            (adicConstant k₀ l X)) ≪≫ ε.symm ∧
      NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ ∧
      (∀ A K, t.inv.app (A, K) =
        (S.transpose ((nativeForget k₀ l X).obj A) ((nativeForget k₀ l X).obj K)
          ((nativeForget k₀ l X).obj (W.tensor.obj (A, K)))).symm
            ((nativeForget k₀ l X).map ((W.adjunction K).unit.app A) ≫
              χ.hom.app (op K, W.tensor.obj (A, K)))) := by
  apply (tensorModelConclusion_iff k₀ l X M S β).mp
  obtain ⟨χ, hχ⟩ := native_hom_representative_exists k₀ l X M
  obtain ⟨m, γ, δ, ε, t, P, c, hc⟩ :=
    native_weil_tensor_geometry k₀ l X M S β hmonoidal hS
  obtain ⟨e, hn, hmodel⟩ := native_weil_representative_currying P
  let := m
  obtain ⟨⟨m', adj, ev⟩, hm, ht⟩ := closed_of_natural_currying M.weilHom e hn
  dsimp only [CoefficientClosedStructure.monoidal] at hm
  subst m'
  let W : CoefficientClosedStructure M.weilHom := ⟨m, adj, ev⟩
  have he (A K L : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
      W.transpose A K L = e A K L := eq_of_heq (ht A K L)
  have hW := normalization_from_currying (ihomBifunctor k₀ l X) P.tensor
    (fun K ↦ P.adjunction.adj K) M.weilHom M.weilRepresentatives W
    (NativeTensorKFlat k₀ l X P.tensor) P.model e he hmodel
  have hev := native_weil_tensor_evaluation k₀ l X M S W t P hW χ hχ
  have hu := uncurry_of_evaluation W S (nativeForget k₀ l X) t χ hev
  have hunit := unit_mate_of_uncurry W S (nativeForget k₀ l X) t χ hu
  unfold TensorModelConclusion
  exact ⟨W, γ, δ, ε, t, χ, c, hc, hχ, hunit⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
