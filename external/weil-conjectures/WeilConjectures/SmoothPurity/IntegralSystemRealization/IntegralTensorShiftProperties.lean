/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.SixFunctors.Completed.CompletedTensorShiftRight

/-! # Representative formulas for the two tensor slots

Source: blueprint chap-Smooth-purity, theorem-smooth-purity-all-admissible-coefficients, Step 2;
cochain tensor and mapping-cone conventions of Stacks 011G, 014E and 0941
(blueprint: def-pur-integral-tensor-shift-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.IntegralSystemRealization

/-- Shift only the first operand of a bifunctor.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev tensorShiftFirst (A : Type v) [Category.{w} A] [HasShift A ℤ] (r : ℤ) :
    A × A ⥤ A × A := (shiftFunctor A r).prod (𝟭 A)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual total tensor on complexes of strict systems.
Source: blueprint Step 2 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev systemTotalTensor (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

/-- K-flatness on the actual sequence site.
Source: Stacks 06YN (blueprint: def-pur-integral-operation-shift-data). -/
abbrev systemKFlat (W : Scheme.{u})
    (P : CochainComplex (coefficientSequenceModules l E W) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
    (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
    (R := coefficientSequenceCommRingSheaf l E W) P

/-- The unsigned first-slot formula on every strict-system tensor generator.
The tower site includes quotient-linear transitions, so the cochain isomorphism
also fixes all transition squares.
Source: Stacks 011G, 012Z (blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorLeftFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ)
    (α : (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i + r)).val.obj U) (y : (Q.X (j)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (P⟦r⟧) (Q) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      r (i + j) ((i + r) + (j)) (by omega)).inv.val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q (i + r) (j)
          ((i + r) + (j)) rfl U x y)

/-- Descent of the specified cochain shift on every K-flat pair.
Source: Stacks 06YU and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ (hS : systemKFlat l E W (P⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P⟦r⟧, Q) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorLeftFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj (P⟦r⟧), DerivedCategory.Q.obj Q))
        (Y := ((DerivedCategory.Q.obj P)⟦r⟧, DerivedCategory.Q.obj Q))
        (((DerivedCategory.Q.commShiftIso r).hom.app P), 𝟙 (DerivedCategory.Q.obj Q)) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P⟦r⟧) (Q) hS hQ).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom)

/-- The signed second-slot formula on every strict-system tensor generator.
The tower site includes quotient-linear transitions, so the cochain isomorphism
also fixes all transition squares.
Source: Stacks 011G, 012Z (blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorRightFormula (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ)
    (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
      ((systemTotalTensor l E W).obj (P, Q))⟦r⟧) : Prop :=
  ∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X (i)).val.obj U) (y : (Q.X (j + r)).val.obj U),
    ((α.hom.f (i + j)).val.app U)
      (coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (P) (Q⟦r⟧) i j (i + j) rfl U x y) =
    ((CochainComplex.shiftFunctorObjXIso ((systemTotalTensor l E W).obj (P, Q))
      r (i + j) ((i) + (j + r)) (by omega)).inv.val.app U)
      ((r * i).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q (i) (j + r)
          ((i) + (j + r)) rfl U x y)

/-- Descent of the specified cochain shift on every K-flat pair.
Source: Stacks 06YU and blueprint Step 2
(blueprint: def-pur-integral-operation-shift-data). -/
def systemTensorRightProperty (W : Scheme.{u}) (r : ℤ)
    (σ : completedTensorShiftSecond (System l E W) r ⋙ (calculus l E W).systemClosed.tensor ≅
      (calculus l E W).systemClosed.tensor ⋙ shiftFunctor (System l E W) r) : Prop :=
  ∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ (hS : systemKFlat l E W (Q⟦r⟧))
      (α : (systemTotalTensor l E W).obj (P, Q⟦r⟧) ≅
        ((systemTotalTensor l E W).obj (P, Q))⟦r⟧),
      systemTensorRightFormula l E W P Q r α ∧
      (calculus l E W).systemClosed.tensor.map
        (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦r⟧)))
        (Y := (DerivedCategory.Q.obj P, (DerivedCategory.Q.obj Q)⟦r⟧))
        (𝟙 (DerivedCategory.Q.obj P), ((DerivedCategory.Q.commShiftIso r).hom.app Q)) ≫
          σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        (P) (Q⟦r⟧) hP hS).inv ≫
      DerivedCategory.Q.map α.hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app ((systemTotalTensor l E W).obj (P, Q)) ≫
      (shiftFunctor (System l E W) r).map
        (((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          P Q hP hQ).hom)

/-- The first-slot finite tensor formula, before the fixed product/cone passage.
Source: Stacks 011G (blueprint: def-pur-integral-operation-shift-data). -/
def integralTensorLeftFormula (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (r : ℤ)
    (α : (integralOperationsTensorTowerFunctor l E W).obj (P⟦r⟧, Q) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) ⋙
        shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r) : Prop :=
  ∀ (n : ℕ) (i j : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P).X (i + r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q).X j).val.obj U),
    (((α.hom.app (op n)).f (i + j)).val.app U)
      (integralOperationsTotalTensorSection l E W n (P⟦r⟧) Q i j U x y) =
    ((CochainComplex.shiftFunctorObjXIso
      ((integralOperationsTensorLevel l E W n).obj (P, Q))
        r (i + j) ((i + r) + j) (by omega)).inv.val.app U)
      (integralOperationsTotalTensorSection l E W n P Q (i + r) j U x y)

/-- First-slot normalization with abstract coefficient and model data.
The canonical predicate below specializes every parameter to the recorded construction.
Source: Stacks 014E, 0941 (blueprint: def-pur-integral-tensor-shift-properties). -/
def integralTensorLeftModelProperty {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (r : ℤ) (Good : ObjectProperty (CochainComplex A ℤ))
    (T : CochainComplex A ℤ × CochainComplex A ℤ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (Φ : ∀ P Q : CochainComplex A ℤ,
      (T.obj (P⟦r⟧, Q) ≅ T.obj (P, Q) ⋙ shiftFunctor (CochainComplex A ℤ) r) → Prop)
    {D : Type c} [Category.{d} D] (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S) (G : D × D ⥤ D)
    (ε : ((Good.ι ⋙ F).prod (Good.ι ⋙ F)) ⋙ G ≅
      (Good.ι.prod Good.ι) ⋙ (T ⋙ integralOperationsRoosFunctor) ⋙ F)
    (σ : S.prod (𝟭 D) ⋙ G ≅ G ⋙ S) : Prop :=
  ∀ (P Q : Good.FullSubcategory),
    ∃ (hP : Good (P.obj⟦r⟧))
      (α : T.obj (P.obj⟦r⟧, Q.obj) ≅
        T.obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (A) ℤ) r),
      Φ P.obj Q.obj α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            (T.obj (P.obj⟦r⟧, Q.obj))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            (T.obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            (T.obj (P.obj, Q.obj))
            (T.obj (P.obj⟦r⟧, Q.obj)) r α δ ∧
        G.map
            ((γ.hom.app P.obj),
              𝟙 (F.obj Q.obj)) ≫
          σ.hom.app (F.obj P.obj, F.obj Q.obj) ≫
          S.map
            (ε.hom.app (P, Q)) =
        ε.hom.app (⟨P.obj⟦r⟧, hP⟩, Q) ≫
          F.map
            (completedTensorShiftRoosIso
              (T.obj (P.obj, Q.obj))
              (T.obj (P.obj⟦r⟧, Q.obj)) r δ).hom ≫
          γ.hom.app
            ((T ⋙ integralOperationsRoosFunctor).obj (P.obj, Q.obj))

/-- First-slot descent through exactly the recorded finite tower and Roos cone.
Source: Stacks 014E, 0941 (blueprint: def-pur-integral-operation-shift-data). -/
abbrev integralTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r) : Prop :=
  integralTensorLeftModelProperty r (integralOperationsGoodComplex l E W)
    (integralOperationsTensorTowerFunctor l E W)
    (fun P Q ↦ integralTensorLeftFormula l E W P Q r) DerivedCategory.Q
    (shiftFunctor (Integral l E W) r) (DerivedCategory.Q.commShiftIso r)
    (integralCompletedTensor l E W) (integralCompletedTensorComparison l E W) σ

end WeilConjectures.IntegralSystemRealization
