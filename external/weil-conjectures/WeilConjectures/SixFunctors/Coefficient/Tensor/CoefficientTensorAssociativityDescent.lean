/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityRepresentatives
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Descent of ordinary tensor associativity through resolving comparisons

Source: Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r wb d vd s wa b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  CategoryTheory.MonoidalCategory.leftAssocTensor
  CategoryTheory.MonoidalCategory.rightAssocTensor

section Transport

variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
  {H : Bᵒᵖ × B ⥤ B} {H' : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H) (T : CoefficientClosedStructure H')
  (F : B ⥤ A) (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)

@[reducible] private def rho (X Y : B) :
    F.obj (S.tensor.obj (X, Y)) ≅ T.tensor.obj (F.obj X, F.obj Y) :=
  μ.app (X, Y)

private theorem rho_naturality (X Y X' Y' : B) (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (S.tensor.map (f, g)) ≫ (rho S T F μ X' Y').hom =
      (rho S T F μ X Y).hom ≫ T.tensor.map (F.map f, F.map g) :=
  μ.hom.naturality (X := (X, Y)) (Y := (X', Y')) (f, g)

private theorem associator_of_iso
    {P Q N L M V : B} (e : P ≅ L) (e' : Q ≅ M) (e'' : N ≅ V)
    (h : F.map (S.monoidal.associator P Q N).hom ≫
      (rho S T F μ P (S.tensor.obj (Q, N))).hom ≫
      T.tensor.map (X := (F.obj P, F.obj (S.tensor.obj (Q, N))))
        (Y := (F.obj P, T.tensor.obj (F.obj Q, F.obj N)))
        (𝟙 (F.obj P), (rho S T F μ Q N).hom) =
      (rho S T F μ (S.tensor.obj (P, Q)) N).hom ≫
      T.tensor.map (X := (F.obj (S.tensor.obj (P, Q)), F.obj N))
        (Y := (T.tensor.obj (F.obj P, F.obj Q), F.obj N))
        ((rho S T F μ P Q).hom, 𝟙 (F.obj N)) ≫
      (T.monoidal.associator (F.obj P) (F.obj Q) (F.obj N)).hom) :
    F.map (S.monoidal.associator L M V).hom ≫
      (rho S T F μ L (S.tensor.obj (M, V))).hom ≫
      T.tensor.map (X := (F.obj L, F.obj (S.tensor.obj (M, V))))
        (Y := (F.obj L, T.tensor.obj (F.obj M, F.obj V)))
        (𝟙 (F.obj L), (rho S T F μ M V).hom) =
      (rho S T F μ (S.tensor.obj (L, M)) V).hom ≫
      T.tensor.map (X := (F.obj (S.tensor.obj (L, M)), F.obj V))
        (Y := (T.tensor.obj (F.obj L, F.obj M), F.obj V))
        ((rho S T F μ L M).hom, 𝟙 (F.obj V)) ≫
      (T.monoidal.associator (F.obj L) (F.obj M) (F.obj V)).hom := by
  with_unfolding_all
    let := S.monoidal
    let := T.monoidal
    let F₁ := (leftAssocTensor B) ⋙ F
    let F₂ := (rightAssocTensor B) ⋙ F
    let G₁ := (F.prod (F.prod F)) ⋙ leftAssocTensor A
    let G₂ := (F.prod (F.prod F)) ⋙ rightAssocTensor A
    let α : F₁ ⟶ F₂ := Functor.whiskerRight (associatorNatIso B).hom F
    let β : G₁ ⟶ G₂ := Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso A).hom
    let c₁ : F₁ ⟶ G₁ :=
      { app := fun X ↦ (rho S T F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
          (rho S T F μ X.1 X.2.1).hom ▷ F.obj X.2.2
        naturality := by
          intro X Y f
          have h₁ := rho_naturality S T F μ (X.1 ⊗ X.2.1) X.2.2
            (Y.1 ⊗ Y.2.1) Y.2.2 (f.1 ⊗ₘ f.2.1) f.2.2
          have h₂ := rho_naturality S T F μ X.1 X.2.1 Y.1 Y.2.1 f.1 f.2.1
          simp only [CoefficientClosedStructure.tensor, tensor_obj, tensor_map] at h₁ h₂
          change F.map ((f.1 ⊗ₘ f.2.1) ⊗ₘ f.2.2) ≫ _ = _
          erw [reassoc_of% h₁]
          change (rho S T F μ (X.1 ⊗ X.2.1) X.2.2).hom ≫
              (F.map (f.1 ⊗ₘ f.2.1) ⊗ₘ F.map f.2.2) ≫
                (rho S T F μ Y.1 Y.2.1).hom ▷ F.obj Y.2.2 = _
          simp only [← tensorHom_id, Category.assoc,
            tensorHom_comp_tensorHom,
            Category.comp_id]
          erw [h₂]
          simp only [G₁, Functor.comp_map, Functor.prod_map,
            leftAssocTensor_map,
            tensorHom_comp_tensorHom,
            Category.id_comp] }
    let c₂ : F₂ ⟶ G₂ :=
      { app := fun X ↦ (rho S T F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
          F.obj X.1 ◁ (rho S T F μ X.2.1 X.2.2).hom
        naturality := by
          intro X Y f
          have h₁ := rho_naturality S T F μ X.1 (X.2.1 ⊗ X.2.2)
            Y.1 (Y.2.1 ⊗ Y.2.2) f.1 (f.2.1 ⊗ₘ f.2.2)
          have h₂ := rho_naturality S T F μ X.2.1 X.2.2 Y.2.1 Y.2.2 f.2.1 f.2.2
          simp only [CoefficientClosedStructure.tensor, tensor_obj, tensor_map] at h₁ h₂
          change F.map (f.1 ⊗ₘ (f.2.1 ⊗ₘ f.2.2)) ≫ _ = _
          erw [reassoc_of% h₁]
          change (rho S T F μ X.1 (X.2.1 ⊗ X.2.2)).hom ≫
              (F.map f.1 ⊗ₘ F.map (f.2.1 ⊗ₘ f.2.2)) ≫
                F.obj Y.1 ◁ (rho S T F μ Y.2.1 Y.2.2).hom = _
          simp only [← id_tensorHom, Category.assoc,
            tensorHom_comp_tensorHom,
            Category.comp_id]
          erw [h₂]
          simp only [G₂, Functor.comp_map, Functor.prod_map,
            rightAssocTensor_map,
            tensorHom_comp_tensorHom,
            Category.id_comp] }
    let z : (P, Q, N) ≅ (L, M, V) := e.prod (e'.prod e'')
    have hz : IsIso (F₁.map z.hom) := inferInstance
    apply (cancel_epi (F₁.map z.hom)).mp
    have hh : (α ≫ c₂).app (P, Q, N) = (c₁ ≫ β).app (P, Q, N) := by
      simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
        F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
        CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
        id_tensorHom, tensorHom_id, Category.assoc] using h
    have hh' := congrArg (fun f ↦ f ≫ G₂.map z.hom) hh
    rw [← (α ≫ c₂).naturality, ← (c₁ ≫ β).naturality] at hh'
    simpa only [α, β, c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, associatorNatIso_hom_app, Functor.prod_obj,
        F₁, G₂, Functor.comp_obj, leftAssocTensor_obj, rightAssocTensor_obj, tensor_obj,
        CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
      id_tensorHom, tensorHom_id, Category.assoc] using hh'

end Transport

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]

private theorem flat_representative (X : DerivedCategory (RingedTensorModules.{c, v, r} J R)) :
    ∃ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (_hP : P.IsKFlatIndependentCoefficients)
      (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)), Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  obtain ⟨P, f, hP, fP, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (DerivedCategory.Q.objPreimage X)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hf
  refine ⟨P, hP, ?_, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩
  intro n
  unfold SheafOfModules.IsFlatOnSite
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (fP n)

variable (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory _ _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)
  (K : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
    CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ)
  (F : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
    DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
  (ε : DerivedCategory.Q ⋙ F ⟶ K ⋙ DerivedCategory.Q)
  (hε : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) → IsIso (ε.app P))
  (hU : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
  (chain : coefficientTotalTensor.{r, c, v} J R ⋙ K ≅
    K.prod K ⋙ coefficientTotalTensor.{s, d, vd} J' R')
  (hκ : CoefficientComplexTensorAssociativity J R J' R' K chain)
  (μ : SB.tensor ⋙ F ≅ F.prod F ⋙ SA.tensor)
  (hμ : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hUP : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
    (hUQ : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj Q))
    (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (_fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p)),
    F.map (TB.iso J R SB P Q hP hQ).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SA.tensor.map
          (X := (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj (K.obj P), DerivedCategory.Q.obj (K.obj Q)))
          (Prod.mkHom (ε.app P) (ε.app Q)) =
      ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
        (TA.iso J' R' SA (K.obj P) (K.obj Q) hUP hUQ).hom)

include cB cA hε hU hκ hμ

/-- A natural comparison invertible on resolving complexes descends ordinary tensor
associativity. The proof pastes four binary squares, cancels model isomorphisms, and
transports along flat-term K-flat resolutions. Source: Stacks 07A4 and 0FPT.
(blueprint: lem-coef-tensor-associativity-descent). -/
theorem coefficientTensorAssociativityDescent (X Y Z : DerivedCategory
    (RingedTensorModules.{c, v, r} J R)) :
    F.map (SB.monoidal.associator X Y Z).hom ≫
        μ.hom.app (X, SB.tensor.obj (Y, Z)) ≫
        SA.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z))) =
      μ.hom.app (SB.tensor.obj (X, Y), Z) ≫
        SA.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))) ≫
        (SA.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  obtain ⟨P, hP, fP, ⟨e⟩⟩ := flat_representative.{c, v, r, wb} J R X
  obtain ⟨Q, hQ, fQ, ⟨e'⟩⟩ := flat_representative.{c, v, r, wb} J R Y
  obtain ⟨N, hN, fN, ⟨e''⟩⟩ := flat_representative.{c, v, r, wb} J R Z
  apply associator_of_iso SB SA F μ e e' e''
  exact coefficientTensorAssociativityOnRepresentatives J R J' R' SB TB βB cB SA TA βA cA
    K F ε hε hU chain hκ μ hμ P Q N hP fP hQ fQ hN fN

end WeilConjectures
