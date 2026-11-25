/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.NormalizedKappaTransitions
import all WeilConjectures.SecSmoothPurity.NormalizedKappaTransitions
import all WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.SecSmoothPurity.CoefficientComparisonsBalancedConstruction
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Normalized scalar tensor transitions

Source: Stacks Project, Modules on Sites, Tags 03EK and 03EL, and
Cohomology on Sites, Tag 07A4.
(auxiliary; not a blueprint node).

Scalar tensor comparisons commute with arbitrary semilinear squares. Their
forward maps insert one and their inverse maps multiply the scalar coefficients.
-/

set_option Elab.async false
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation

attribute [local irreducible] extensionAdjunction
attribute [local irreducible] generator
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

open KappaCalculation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The normalized comparison of signed tensor totals.
Source: Stacks 03EL and 07A4 (auxiliary; not a blueprint node). -/
noncomputable def tensorComparison {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) : (pull f).obj (total P Q) ≅
      total ((pull f).obj P) ((pull f).obj Q) := comparison f c P Q

/-- The ordinary tensor map on the signed direct-sum total.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable def tensorTotalMap {A : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q') :
    total P Q ⟶ total P' Q' := totalMap f g

/-- The homogeneous inclusion into the signed direct-sum total.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable def tensorι {A : Sheaf J CommRingCat.{w}}
    (P Q : Complex A) (p q n : ℤ) (h : p + q = n) :
    P.X p ⊗ Q.X q ⟶ (total P Q).X n := by
  have : ∀ (I₁ I₂ : Type w), HasColimitsOfShape (Discrete I₂)
      (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj) :=
    fun _ _ ↦ PresheafOfModules.hasColimitsOfShape _ _
  have : HasCoproducts.{0} (Modules A) := fun I ↦ by
    have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A).obj) :=
      PresheafOfModules.hasColimitsOfShape _ _
    exact
      SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  have : HasFiniteCoproducts (Modules A) :=
    hasFiniteCoproducts_of_hasCoproducts (C := Modules A)
  exact CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules A)) p q n h

/-- Auxiliary formula for scalar tensor transitions. Source: Stacks 03EK, 03EL, 07A4
(auxiliary; not a blueprint node). -/
def totalPure {A : Sheaf J CommRingCat.{w}} (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
    (y : (Q.X q).val.obj U) : ((total P Q).X n).val.obj U :=
  (tensorι P Q p q n h).val.app U
    (ringedComparisonPure A (P.X p) (Q.X q) U x y)

@[no_expose] private noncomputable instance tensorCoproducts (R : Sheaf J CommRingCat.{w}) :
    HasCoproducts.{0} (Modules R) := by
  intro I
  have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

@[no_expose] private noncomputable instance hasTensorTotal (R : Sheaf J CommRingCat.{w})
    (P Q : Complex R) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (Modules R)) (.up ℤ) :=
  inferInstance

attribute [local irreducible] tensorComparison tensorTotalMap comparison

@[no_expose] private def identityCoefficientSquare {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    CoefficientComparisonsBalanced.Square (𝟭 (Sheaf J (Type w))) :=
  { R0 := A, R1 := B, B0 := A, B1 := B, A0 := A, A1 := B
    iY := a, iX := a, j := a, phi0 := 𝟙 A, phi1 := 𝟙 B
    I0 := identityAlgebraicInverseImage A
    I1 := identityAlgebraicInverseImage B
    graph := by simp [identityAlgebraicInverseImage]
    commutes := by simp }

private theorem scalarConstruction {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B) :
    CoefficientComparisonsBalanced.ScalarTensorConstruction a :=
  (CoefficientComparisonsBalanced.coefficientComparisons_balanced_construction
    (identityCoefficientSquare a) (𝟭 _) Adjunction.id).2.1

private theorem scalarTensorFormulas {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (c : Comparison (extensionPullback a)) :
    CoefficientComparisonsBalanced.ScalarTensorFormulas a c.mu := by
  obtain ⟨m, hm, _⟩ := scalarConstruction a
  let c' : CanonicalRingedTensorComparisonOnSmallSites A B A (𝟭 _)
      (identityAlgebraicInverseImage A) a (extensionFunctor a) (fun _ ↦ rfl) :=
    { q := c.q, q_one := c.q_one, mu := c.mu,
      naturality := c.naturality, pure := c.pure }
  have h : c.mu = m := hm.2.2 c'
  exact h.symm ▸ hm.1

@[reassoc]
private theorem tensorComparison_ι {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (h : p + q = n) :
    f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h) ≫
        (tensorComparison f c P Q).hom.f n =
      (c.mu (P.X p) (Q.X q)).hom ≫
        CochainComplex.ιMapBifunctor ((pull f).obj P) ((pull f).obj Q)
          (curriedTensor (Modules S)) p q n h := by
  unfold tensorComparison
  exact CategoryTheory.CochainPullback.comparison_ι f c P Q p q n h

@[reassoc]
private theorem totalMap_ι {R : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex R} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) :
    CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n h ≫
        (tensorTotalMap a b).f n =
      (a.f p ⊗ₘ b.f q) ≫
        CochainComplex.ιMapBifunctor P' Q' (curriedTensor (Modules R)) p q n h := by
  unfold tensorTotalMap
  change _ ≫ (HomologicalComplex.mapBifunctorMap a b _ _).f n = _
  simp only [HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app,
    curriedTensor_obj_map, tensorHom_def, Category.assoc]

private theorem totalMap_pure {A : Sheaf J CommRingCat.{w}}
    {P Q P' Q' : Complex A} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorTotalMap a b).f n).val.app U (totalPure P Q p q n h U x y) =
      totalPure P' Q' p q n h U ((a.f p).val.app U x) ((b.f q).val.app U y) := by
  have ht := congrArg (fun z ↦ z.val.app U (moduleTmul (P.X p) (Q.X q) U x y))
    (totalMap_ι a b p q n h)
  change ((tensorTotalMap a b).f n).val.app U
    ((tensorι P Q p q n h).val.app U
      (moduleTmul (P.X p) (Q.X q) U x y)) =
    (CochainComplex.ιMapBifunctor P' Q' (curriedTensor (Modules A)) p q n h).val.app U
      ((a.f p ⊗ₘ b.f q).val.app U (moduleTmul (P.X p) (Q.X q) U x y)) at ht
  erw [moduleTmul_map] at ht
  exact ht

private theorem scalarTotal_hom {A B : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (c : Comparison (extensionPullback a)) (P Q : Complex A)
    (p q n : ℤ) (h : p + q = n) (U : Cᵒᵖ) (b : B.obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorComparison (extensionPullback a) c P Q).hom.f n).val.app U
      (extensionTmul a ((total P Q).X n) U b (totalPure P Q p q n h U x y)) =
    totalPure ((extend a).obj P) ((extend a).obj Q) p q n h U
      (extensionTmul a (P.X p) U b x) (extensionTmul a (Q.X q) U 1 y) := by
  have ht := congrArg (fun z ↦ z.val.app U
    (extensionTmul a (P.X p ⊗ Q.X q) U b
      (ringedComparisonPure A (P.X p) (Q.X q) U x y)))
    (tensorComparison_ι (extensionPullback a) c P Q p q n h)
  change ((tensorComparison (extensionPullback a) c P Q).hom.f n).val.app U
    (((extensionFunctor a).map
      (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules A)) p q n h)).val.app U
      _) = _ at ht
  change _ = (CochainComplex.ιMapBifunctor ((extend a).obj P) ((extend a).obj Q)
    (curriedTensor (Modules B)) p q n h).val.app U
      (((c.mu (P.X p) (Q.X q)).hom).val.app U _) at ht
  erw [extension_map, (scalarTensorFormulas a c).1] at ht
  exact ht

attribute [local irreducible] extensionFunctor
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem tensor_hom_ext {A : Sheaf J CommRingCat.{w}}
    (M N H : Modules A) {f g : M ⊗ N ⟶ H}
    (h : ∀ U x y, f.val.app U (moduleTmul M N U x y) =
      g.val.app U (moduleTmul M N U x y)) : f = g := by
  exact CochainScalarConstruction.pure_hom_ext A M N H h

attribute [local irreducible] totalPure ringedComparisonPure extensionTmul

end CategoryTheory.CochainPullback.StrictCoefficient.ScalarCalculation
