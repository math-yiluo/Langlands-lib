/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexStrictTensorAux
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorAssociativity
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleClosed
public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorNormalization
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTotalTensorMapGenerators

/-! # The pure-tensor formula of the strict reduction tensor map

Source: Stacks 03EK, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- An isomorphism of module sheaves is inverse on sections.
Source: Stacks 03CO. -/
theorem sheafOfModules_inv_hom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {A B : SheafOfModules.{u + 1} R} (e : A ≅ B) (U : Cᵒᵖ)
    (s : A.val.obj U) : e.inv.val.app U (e.hom.val.app U s) = s := by
  rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    e.hom_inv_id]
  rfl

/-- Sections of a composite of module-sheaf maps.
Source: Stacks 03CO. -/
theorem sheafOfModules_comp_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {A B D : SheafOfModules.{u + 1} R} (f : A ⟶ B) (g : B ⟶ D)
    (U : Cᵒᵖ) (s : A.val.obj U) : (f ≫ g).val.app U s = g.val.app U (f.val.app U s) :=
  rfl

/-- A natural isomorphism into module sheaves is inverse on sections.
Source: Stacks 03CO. -/
theorem sheafOfModules_natIso_inv_hom_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}} {D : Type*} [Category D]
    {F G : D ⥤ SheafOfModules.{u + 1} R} (e : F ≅ G) (X : D) (U : Cᵒᵖ)
    (s : (F.obj X).val.obj U) : (e.inv.app X).val.app U ((e.hom.app X).val.app U s) = s :=
  sheafOfModules_inv_hom_apply (e.app X) U s

/-- The ordinary unit section is the reduction of `1 ⊗ x`.
Source: Stacks 06YY. -/
theorem scalarUnitSection_eq (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    coefficientIntegralScalarUnitSection l E W n M U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x :=
  finiteAdjunction_unit_apply l E W n M U x

/-- The reduction unit, regarded as a section on the sequence site. -/
def reducedUnitSection (W : Scheme.{u}) (n : ℕ) (M : integralTowerModules l E W)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pullbackTensorOrdinaryReduction l E W).obj M).val.obj (op (n, U.unop)) :=
  ((pullbackTensorReductionEvaluation l E W n).hom.app M).val.app U
    (unrestrictedIntegralTensorSection l E W n M U 1 x)

private theorem evaluationSection_injective (W : Scheme.{u})
    (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ) :
    Function.Injective (coefficientEvaluationSection l E W M n U) :=
  (ConcreteCategory.bijective_of_isIso
    (eqToHom (coefficientSequenceEvaluationAb_eq l E W M n U).symm)).1

private theorem evaluation_reducedUnitSection (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) (U : W.ProEtᵒᵖ)
    (z : (C.X k).val.obj U) :
    (((pullbackTensorReductionEvaluationComplex l E W n).hom.app C).f k).val.app U
      (coefficientIntegralScalarUnitSection l E W n (C.X k) U z) =
    coefficientEvaluationSection l E W
      ((pullbackTensorOrdinaryReduction l E W).obj (C.X k)) n U
      (reducedUnitSection l E W n (C.X k) U z) := by
  rw [reductionEvaluationComplex_hom_f, scalarUnitSection_eq]
  rfl

private theorem reductionEvaluationComplex_inv_unitSection (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) (U : W.ProEtᵒᵖ)
    (z : (C.X k).val.obj U) :
    (((pullbackTensorReductionEvaluationComplex l E W n).inv.app C).f k).val.app U
      (coefficientEvaluationSection l E W
        ((pullbackTensorOrdinaryReduction l E W).obj (C.X k)) n U
        (reducedUnitSection l E W n (C.X k) U z)) =
      coefficientIntegralScalarUnitSection l E W n (C.X k) U z := by
  rw [← evaluation_reducedUnitSection]
  exact congrArg (fun φ ↦ (φ.f k).val.app U
    (coefficientIntegralScalarUnitSection l E W n (C.X k) U z))
    ((pullbackTensorReductionEvaluationComplex l E W n).app C).hom_inv_id

-- Retain the evaluation transports until both sides are sections of the same finite module.
private theorem tensorReductionFiniteComponent_generator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q k : ℤ)
    (hpq : p + q = k) (V : W.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    ((tensorReductionFiniteComponent l E W P Q n).f k).val.app (op V)
      (coefficientEvaluationSection l E W _ n (op V)
        (reducedUnitSection l E W n _ (op V)
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y))) =
      coefficientEvaluationSection l E W _ n (op V)
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k hpq (op (n, V))
          (reducedUnitSection l E W n (P.X p) (op V) x)
          (reducedUnitSection l E W n (Q.X q) (op V) y)) := by
  let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let T := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let e := pullbackTensorReductionEvaluationComplex l E W n
  let a := coefficientScalarTensorIso l E W n P Q
  let b := (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).map
      (Prod.mkHom (e.hom.app P) (e.hom.app Q))
  let c := coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)
  let z := coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y
  have hcancel := reductionEvaluationComplex_inv_unitSection l E W n T k (op V) z
  have hs := coefficientScalarTensorIso_hom_unitSection l E W n P Q p q k hpq (op V) x y
  have hm := coefficientTotalTensor_map_generator W (integralCoefficientCommRingSheaf l E W n)
    (e.hom.app P) (e.hom.app Q) p q k hpq (op V)
    (coefficientIntegralScalarUnitSection l E W n (P.X p) (op V) x)
    (coefficientIntegralScalarUnitSection l E W n (Q.X q) (op V) y)
  have hm' := hm.trans (congrArg₂
    (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj (G.obj P))
      (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj (G.obj Q))
      p q k hpq (op V))
    (evaluation_reducedUnitSection l E W n P p (op V) x)
    (evaluation_reducedUnitSection l E W n Q q (op V) y))
  have hi := coefficientEvaluationTensorIso_inv_generator l E W n
    (G.obj P) (G.obj Q) p q k hpq (op V)
    (reducedUnitSection l E W n (P.X p) (op V) x)
    (reducedUnitSection l E W n (Q.X q) (op V) y)
  exact (congrArg (fun s ↦ (c.inv.f k).val.app (op V)
    ((b.f k).val.app (op V) ((a.hom.f k).val.app (op V) s))) hcancel).trans
      ((congrArg (fun s ↦ (c.inv.f k).val.app (op V) ((b.f k).val.app (op V) s)) hs).trans
        ((congrArg ((c.inv.f k).val.app (op V)) hm').trans hi))

/-- The strict reduction map on sequence-site unit generators. -/
theorem strictMap_reducedUnit_generator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q k : ℤ)
    (hpq : p + q = k) (V : W.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    ((tensorReductionStrictMap l E W P Q).f k).val.app (op (n, V))
      (reducedUnitSection l E W n _ (op V)
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k hpq (op (n, V))
        (reducedUnitSection l E W n (P.X p) (op V) x)
        (reducedUnitSection l E W n (Q.X q) (op V) y) := by
  apply evaluationSection_injective l E W _ n (op V)
  have hc := congrArg (fun φ ↦ (φ.f k).val.app (op V)
    (coefficientEvaluationSection l E W _ n (op V)
      (reducedUnitSection l E W n _ (op V)
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y))))
    (tensorReductionStrictMap_component l E W P Q n)
  exact (coefficientEvaluationSection_map l E W ((tensorReductionStrictMap l E W P Q).f k)
    n (op V) _).symm.trans
      (hc.trans (tensorReductionFiniteComponent_generator l E W P Q n p q k hpq V x y))

-- The finite component unfolds four transported tensor comparisons.
/-- The strict reduction tensor map sends the reduction of `1 ⊗ (x ⊗ y)` to the tensor of the
reductions of `1 ⊗ x` and `1 ⊗ y`.
Source: Stacks 03EK, 07A4 and 0941. -/
theorem strictMap_generator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q k : ℤ)
    (hpq : p + q = k) (V : W.ProEt)
    (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)) :
    ((tensorReductionStrictMap l E W P Q).f k).val.app (op (n, V))
      (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app (op V)
        (unrestrictedIntegralTensorSection l E W n _ (op V) 1
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y))) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k hpq (op (n, V))
        (((pullbackTensorReductionEvaluation l E W n).hom.app (P.X p)).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1 x))
        (((pullbackTensorReductionEvaluation l E W n).hom.app (Q.X q)).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1 y)) := by
  exact strictMap_reducedUnit_generator l E W P Q n p q k hpq V x y

end WeilConjectures.PodReductionRepresentatives
