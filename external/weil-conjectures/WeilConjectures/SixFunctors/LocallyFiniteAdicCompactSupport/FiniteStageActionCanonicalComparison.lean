/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import WeilConjectures.CategoryTheory.ArrowHEq.ArrowHEq

/-! The normalized natural comparison at one raw rational coefficient stage. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient)
open ConstructibleExceptionalCoefficients

private def iso_cast
    {A B : Type*} [Category A] [Category B]
    {F F' H : A ⥤ B} (h : F = F') (e : F' ≅ H) : F ≅ H :=
  h.symm ▸ e

/-- The canonical comparison of a stage action with a specified finite action.
Source: Bhatt--Scholze, Proposition 6.8.14; stage inclusion and equality transport
(blueprint: def-sf-finite-stage-action-canonical-comparison). -/
def finiteStageActionComparison
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (E : Index l Ω)
    (F H : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (h : HEq (S.Φ E) F) (e : F ≅ H) :
    GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E ⋙ S.functor ≅
      H ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E := by
  let H' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E := H
  let e' : S.Φ E ≅ H' := by
    have hh := h
    dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
      GeneralAlgebraicallyClosedCoefficients.stageCategory] at hh ⊢
    exact (eq_of_heq hh).symm ▸ e
  exact S.ιCompFunctorIso E ≪≫ Functor.isoWhiskerRight e'
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).ι E)

private theorem map_iso_cast_heq
    {C D' T : Type*} [Category C] [Category D'] [Category T]
    {F F' H : C ⥤ D'} (h : F = F') (e : F' ≅ H) (J : D' ⥤ T) (A : C) :
    ArrowHEq (J.map ((iso_cast h e).hom.app A)) (J.map (e.hom.app A)) := by
  subst F'
  exact ArrowHEq.refl _

/-- The canonical stage comparison has the prescribed endpoint-recorded component.
Source: stage inclusion and equality transport
(blueprint: def-sf-finite-stage-action-canonical-comparison). -/
theorem finiteStageActionComparison_map
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (E : Index l Ω)
    (F H : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (h : HEq (S.Φ E) F) (e : F ≅ H)
    {T : Type*} [Category T]
    (J : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y ⥤ T)
    (A : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) :
    ArrowHEq (J.map ((finiteStageActionComparison l Ω X Y S E F H h e).hom.app A))
      (J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E).map
        (e.hom.app A))) := by
  have hh := h
  dsimp only [GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory] at hh
  change ArrowHEq (J.map (𝟙 _ ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E).map
      ((iso_cast (eq_of_heq hh) e).hom.app A))) _
  rw [Category.id_comp]
  exact map_iso_cast_heq (eq_of_heq hh) e
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E ⋙ J) A

/-- Canonical stage comparison with operation-category aliases kept abstract.
Source: Bhatt--Scholze, Proposition 6.8.14; equality transport of the finite action
(blueprint: def-sf-finite-stage-action-canonical-comparison). -/
def finiteStageActionComparisonOfOperations
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [IsAlgClosure (Padic l) (ULift.{u} Ω)]
    (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (O : ∀ E : Index l Ω, Operation l (ULift.{u} Ω) X Y
      (.rational ({ carrier := Coefficient.{u} l Ω E } : FieldStage.{u} l)))
    (H : ∀ E : Index l Ω, sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (e : ∀ E, (O E).F ≅ H E)
    (hf : ∀ E, HEq (S.Φ E) (O E).F) (E : Index l Ω)
 :
    GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) E ⋙ S.functor ≅
      H E ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E := by
  have hh := hf E
  let ee := e E
  dsimp only [C, category] at hh ee ⊢
  exact finiteStageActionComparison l Ω X Y S E (O E).F (H E) hh ee

/-- Endpoint-recorded component formula for the operation-level canonical stage map.
Source: equality transport and stage inclusion
(blueprint: def-sf-finite-stage-action-canonical-comparison). -/
theorem finiteStageActionComparisonOfOperations_map
    (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [IsAlgClosure (Padic l) (ULift.{u} Ω)]
    (X Y : Scheme.{u})
    (S : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y))
    (O : ∀ E : Index l Ω, Operation l (ULift.{u} Ω) X Y
      (.rational ({ carrier := Coefficient.{u} l Ω E } : FieldStage.{u} l)))
    (H : ∀ E : Index l Ω, sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X ⥤
      sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (e : ∀ E, (O E).F ≅ H E)
    (hf : ∀ E, HEq (S.Φ E) (O E).F) (E : Index l Ω)
    {T : Type*} [Category T]
    (J : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y ⥤ T)
    (A : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) :
    ArrowHEq (J.map ((finiteStageActionComparisonOfOperations l Ω X Y S O H e hf E).hom.app A))
      (J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) E).map
        ((e E).hom.app A))) := by
  have hh := hf E
  let ee := e E
  dsimp only [C, category] at hh ee ⊢
  exact finiteStageActionComparison_map l Ω X Y S E (O E).F (H E) hh ee J A

end WeilConjectures.LocallyFiniteAdicCompactSupport
