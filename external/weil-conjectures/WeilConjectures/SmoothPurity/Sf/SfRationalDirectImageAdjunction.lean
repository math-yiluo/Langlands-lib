/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.SmoothPurity.Sf.SfIntegralPullbackLinearAdjunction
import WeilConjectures.SmoothPurity.Sf.SfRationalDirectImageCoefficientCompatibility
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Finite rational derived adjunctions

Source: Bhatt--Scholze 6.7.2, 6.8.14(2), Remark 6.8.15.
(blueprint: lem-sf-rational-direct-image-adjunctions).
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TensorProduct
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A]
  {B : Type u₄} [Category.{v₄} B]
  {P : Type u₅} [Category.{v₅} P]
  {Q : Type u₆} [Category.{v₆} Q]

variable [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [G.Additive]

private theorem additiveLeftOfLinearRight (a : F ⊣ G) : F.Additive where
  map_add {X Y} f g := by
    apply (a.homEquiv _ _).injective
    have hh (v : X ⟶ Y) : a.homEquiv _ _ (F.map v) = v ≫ a.unit.app Y := by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality v).symm
    rw [hh, a.homEquiv_unit, G.map_add, Preadditive.comp_add, ← a.homEquiv_unit,
      ← a.homEquiv_unit, hh, hh, Preadditive.add_comp]

omit [G.Additive] in
private theorem linearLeftOfLinearRight (R : Type*) [CommRing R] [Linear R C] [Linear R D]
    [G.Linear R] (a : F ⊣ G) : F.Linear R where
  map_smul {X Y} f r := by
    apply (a.homEquiv _ _).injective
    have hh (v : X ⟶ Y) : a.homEquiv _ _ (F.map v) = v ≫ a.unit.app Y := by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality v).symm
    rw [hh, a.homEquiv_unit, G.map_smul, Linear.comp_smul, ← a.homEquiv_unit,
      hh, Linear.smul_comp]

end CategoryTheory

universe r u v w x
namespace CategoryTheory.ScalarLocalization
variable (R : Type r) [CommRing R] (p : R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type w} [Category.{x} D] [Preadditive D] [Linear R D]

private def liftLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} := (F.mapLinearMap R).baseChange (Localization.Away p)
  map_id X := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (1 ⊗ₜ[R] 𝟙 X.obj) = _
    rw [LinearMap.baseChange_tmul]
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 X.obj) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj X.obj)
    rw [F.map_id]
  map_comp {X Y Z} f g := by
    change (F.mapLinearMap R).baseChange (Localization.Away p)
      (composition R C p X.obj Y.obj Z.obj g f) =
      composition R D p _ _ _
        ((F.mapLinearMap R).baseChange (Localization.Away p) g)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp only [composition_tmul, LinearMap.baseChange_tmul,
          Functor.coe_mapLinearMap]
        change (b * a) ⊗ₜ[R] F.map (f ≫ g) =
          (b * a) ⊗ₜ[R] (F.map f ≫ F.map g)
        rw [F.map_comp]
      | add f g hf hg => simp only [_root_.map_add, hf, hg]
    | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

@[simp] private theorem liftLinear_tmul (F : C ⥤ D) [F.Additive] [F.Linear R]
    {X Y : ScalarLocalization R C p} (a : Localization.Away p) (f : X.obj ⟶ Y.obj) :
    (liftLinear R p F).map (a ⊗ₜ[R] f) = a ⊗ₜ[R] F.map f := by
  change (F.mapLinearMap R).baseChange (Localization.Away p) (a ⊗ₜ[R] f) = _
  simpa only [Functor.coe_mapLinearMap] using
    (LinearMap.baseChange_tmul (F.mapLinearMap R) a f)

private instance liftLinear_additive (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (liftLinear R p F).Additive where
  map_add {X Y f g} := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (f + g) = _
    exact _root_.map_add _ f g

private def liftAdjunction (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (adj : F ⊣ G) :
    liftLinear R p F ⊣ liftLinear R p G where
  unit :=
    { app X := 1 ⊗ₜ[R] adj.unit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, Functor.id_obj, Functor.comp_obj]
        change composition R C p _ _ _
          (1 ⊗ₜ[R] adj.unit.app Y.obj) f =
          composition R C p _ _ _
            ((G.mapLinearMap R).baseChange (Localization.Away p)
              ((F.mapLinearMap R).baseChange (Localization.Away p) f))
            (1 ⊗ₜ[R] adj.unit.app X.obj)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.unit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app X := 1 ⊗ₜ[R] adj.counit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, Functor.id_obj, Functor.comp_obj]
        change composition R D p _ _ _
          (1 ⊗ₜ[R] adj.counit.app Y.obj)
            ((F.mapLinearMap R).baseChange (Localization.Away p)
              ((G.mapLinearMap R).baseChange (Localization.Away p) f)) =
          composition R D p _ _ _ f (1 ⊗ₜ[R] adj.counit.app X.obj)
        induction f using TensorProduct.inductionOn with
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.counit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components X := by
    change composition R D p _ _ _ (1 ⊗ₜ[R] adj.counit.app (F.obj X.obj))
      ((liftLinear R p F).map (1 ⊗ₜ[R] adj.unit.app X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.left_triangle_components X.obj)
  right_triangle_components X := by
    change composition R C p _ _ _
      ((liftLinear R p G).map (1 ⊗ₜ[R] adj.counit.app X.obj))
      (1 ⊗ₜ[R] adj.unit.app (G.obj X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.right_triangle_components X.obj)
end CategoryTheory.ScalarLocalization

open AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

include K₀ hl in
private theorem rationalSystemPullback_isLeftAdjoint :
    (rationalDerivedPullback l E f).IsLeftAdjoint := by
  let I := constructibleIntegralPullback l E f
  obtain ⟨R, ⟨a⟩, hAdd, hLin⟩ := sfIntegralPullbackLinearAdjunction l E K₀ hl f
  have : R.Additive := hAdd
  have : R.Linear (Padic.coefficientExtensionIntegers l E) := hLin
  have : I.Additive := CategoryTheory.additiveLeftOfLinearRight a
  have : I.Linear (Padic.coefficientExtensionIntegers l E) :=
    CategoryTheory.linearLeftOfLinearRight _ a
  let p := Padic.coefficientExtensionUniformizer l E
  let O := Padic.coefficientExtensionIntegers l E
  let Lq := ScalarLocalization.liftLinear O p I
  have heq : Lq = rationalDerivedPullback l E f := by
    apply (rationalDerivedPullback_existsUnique l E f).unique _
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
    refine ⟨inferInstance, (fun _ ↦ rfl), ?_⟩
    intro K N b c
    exact heq_of_eq (ScalarLocalization.liftLinear_tmul O p I c b)
  let aq := ScalarLocalization.liftAdjunction O p I R a
  have : Lq.IsLeftAdjoint := ⟨_, ⟨aq⟩⟩
  rwa [← heq]

end WeilConjectures

namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

end WeilConjectures
