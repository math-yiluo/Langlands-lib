/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleUnit
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Transpose calculus for recorded closed structures

Naturality of the tensor-Hom transpose of a `CoefficientClosedStructure` in all three
variables, the action of total-tensor maps on homogeneous generators, and the
naturality of the degree-zero homology classes of cycles.

Source: Stacks Project, Tags 08J9, 03EK and 08JA.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u c v w a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

namespace CoefficientClosedStructure

variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

/-- The inverse transpose is tensoring with the source followed by evaluation.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
theorem transpose_symm_apply (T P Q : D) (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm g =
      S.tensor.map (Prod.mkHom g (𝟙 P)) ≫ S.evaluation P Q := by
  let := S.monoidal
  exact ((S.adjunction P).homEquiv_counit T Q g).trans
    (congrArg (· ≫ S.evaluation P Q) (tensorHom_id g P).symm)

/-- The transpose is natural in the tensor factor and in the target.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
theorem comp_transpose_comp {T' T P Q Q' : D} (k : T' ⟶ T)
    (f : S.tensor.obj (T, P) ⟶ Q) (g : Q ⟶ Q') :
    k ≫ S.transpose T P Q f ≫ H.map (Prod.mkHom (𝟙 (op P)) g) =
      S.transpose T' P Q' (S.tensor.map (Prod.mkHom k (𝟙 P)) ≫ f ≫ g) := by
  let := S.monoidal
  have hk : (tensorRight P).map k = S.tensor.map (Prod.mkHom k (𝟙 P)) := (tensorHom_id k P).symm
  have h1 : S.transpose T' P Q ((tensorRight P).map k ≫ f) = k ≫ S.transpose T P Q f :=
    (S.adjunction P).homEquiv_naturality_left k f
  have h2 : S.transpose T' P Q' (((tensorRight P).map k ≫ f) ≫ g) =
      S.transpose T' P Q ((tensorRight P).map k ≫ f) ≫ H.map (Prod.mkHom (𝟙 (op P)) g) :=
    (S.adjunction P).homEquiv_naturality_right _ g
  rw [← Category.assoc, ← h1, ← h2, hk, Category.assoc]

/-- The transpose is natural in the evaluated variable.
Source: Stacks 08J9 (auxiliary; not a blueprint node). -/
theorem transpose_comp_map_op {T P P' Q : D} (k : P' ⟶ P)
    (f : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P Q f ≫ H.map (Prod.mkHom k.op (𝟙 Q)) =
      S.transpose T P' Q (S.tensor.map (Prod.mkHom (𝟙 T) k) ≫ f) := by
  apply (S.transpose T P' Q).symm.injective
  rw [Equiv.symm_apply_apply, transpose_symm_apply]
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) k) ≫ S.evaluation P Q := by
    let := S.monoidal
    refine (congrArg (· ≫ S.evaluation P' Q) (tensorHom_id _ P')).trans
      ((S.evaluation_naturality P P' Q k).trans ?_)
    exact (congrArg (· ≫ S.evaluation P Q) (id_tensorHom _ k)).symm
  have hf := (S.transpose T P Q).symm_apply_apply f
  rw [transpose_symm_apply] at hf
  have hx : S.tensor.map (Prod.mkHom (S.transpose T P Q f) (𝟙 P')) ≫
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) k) =
      S.tensor.map (Prod.mkHom (𝟙 T) k) ≫
        S.tensor.map (Prod.mkHom (S.transpose T P Q f) (𝟙 P)) := by
    rw [← S.tensor.map_comp, ← S.tensor.map_comp]
    congr 1
    ext <;> simp
  have hc : S.tensor.map (Prod.mkHom (S.transpose T P Q f ≫ H.map (Prod.mkHom k.op (𝟙 Q)))
      (𝟙 P')) = S.tensor.map (Prod.mkHom (S.transpose T P Q f) (𝟙 P')) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom k.op (𝟙 Q))) (𝟙 P')) := by
    rw [← S.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [hc, Category.assoc, he, ← Category.assoc, hx, Category.assoc, hf]

end CoefficientClosedStructure

section TotalTensor

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

attribute [local instance] SheafOfModules.cochainModulesMonoidal

/-- Total-tensor maps act on homogeneous generators by applying both input maps.
Source: Stacks 03EK, 07A4 (auxiliary; not a blueprint node).
Proof: on the bidegree summand the total map is the tensor product of the two
components, which acts on sheafified pure tensors componentwise. -/
theorem coefficientTotalTensor_map_tensorGenerator
    {P Q P' Q' : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q i : ℤ) (h : p + q = i) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((coefficientTotalTensor.{u, c, v} J A).map (Prod.mkHom f g)).f i).val.app U
        (coefficientTensorGenerator.{u, c, v} J A P Q p q i h U x y) =
      coefficientTensorGenerator.{u, c, v} J A P' Q' p q i h U
        ((f.f p).val.app U x) ((g.f q).val.app U y) := by
  have hι : HomologicalComplex.ιTensorObj P Q p q i h ≫
      ((coefficientTotalTensor.{u, c, v} J A).map (Prod.mkHom f g)).f i =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj P' Q' p q i h := by
    simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
      Functor.map₂HomologicalComplex, HomologicalComplex.comp_f,
      HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
      HomologicalComplex.id_f, MonoidalCategory.curriedTensor_map_app,
      MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc]
    simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight]
    erw [Category.id_comp, Category.id_comp]
  have h1 := congrArg (fun k ↦ k.val.app U
    (CochainPullback.moduleTmul (P.X p) (Q.X q) U x y)) hι
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply] at h1
  exact h1.trans (congrArg ((HomologicalComplex.ιTensorObj P' Q' p q i h).val.app U)
    (CochainPullback.moduleTmul_map (f.f p) (g.f q) U x y))

end TotalTensor

/-- Degree-zero derived homology classes of cycles are natural in chain maps.
Source: Stacks 08JA (auxiliary; not a blueprint node). -/
theorem homologyFunctorFactors_inv_homologyπ_naturality
    {X Y : CochainComplex AddCommGrpCat.{w} ℤ} (φ : X ⟶ Y) (z : X.cycles 0) :
    (@DerivedCategory.homologyFunctor AddCommGrpCat.{w} _ _
      (HasDerivedCategory.standard _) 0).map
        ((@DerivedCategory.Q AddCommGrpCat.{w} _ _ (HasDerivedCategory.standard _)).map φ)
        ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{w} _ _
          (HasDerivedCategory.standard _) 0).inv.app X (X.homologyπ 0 z)) =
      (@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{w} _ _
          (HasDerivedCategory.standard _) 0).inv.app Y
        (Y.homologyπ 0 (HomologicalComplex.cyclesMap φ 0 z)) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{w}
  have h1 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ 0) z
  have h2 := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{w} 0).inv.naturality φ)
    (X.homologyπ 0 z)
  simp only [ConcreteCategory.comp_apply] at h1
  rw [← h1]
  exact h2.symm

section UnitClass

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The image of the unit class under a map out of the unit complex.
Source: Stacks 08JA, 079P (auxiliary; not a blueprint node). -/
theorem coefficientUnitClass_map
    (K : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (φ : coefficientUnitComplex.{u} J A ⟶ K) :
    (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).map
        ((coefficientGlobalSections.{u, c, v, w} J A).map (DerivedCategory.Q.map φ))
        (coefficientUnitClass.{u, c, v, w} J A) =
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
        (HasDerivedCategory.standard _) 0).map
        (coefficientSiteSectionsComparison.{u, c, v, w} J A K)
        ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0).inv.app _
          ((((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homologyπ 0 (HomologicalComplex.cyclesMap
            (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
              (ComplexShape.up ℤ)).map φ) 0 (coefficientUnitCycle.{u} J A)))) := by
  rw [← homologyFunctorFactors_inv_homologyπ_naturality, coefficientUnitClass,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, coefficientSiteSectionsComparison_naturality]

end UnitClass

end WeilConjectures
