/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalCompletionSectionTransport
import all WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-! # The transported strict positive quotient tower

Source: integral-models proof (1), Stacks Tags 099L, 099M and 0941.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
open IntegralModelsStacks
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

local instance towerModelDerived : HasDerivedCategory (ConstantCompletion.Mod (ring l E X)) :=
  HasDerivedCategory.standard _

attribute [local irreducible] IntegralConstantModel.pointComparison upperStarFromPoint

/-- Exact scalar restriction and the section equivalence before localization.
Source: integral-models proof (1), Stacks 00YV and 099L.
(auxiliary; not a blueprint node). -/
@[irreducible] def modules : AdicCompletion.Modules l E X ⥤ ConstantCompletion.Mod (ring l E X) :=
  Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X) ⋙
    Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (scalarMap l E X) ⋙
      smallModules X (constantRing l E X)

instance modules_additive : (modules l E X).Additive := by
  unfold modules
  infer_instance

instance modules_preservesFiniteLimits : PreservesFiniteLimits (modules l E X) := by
  unfold modules
  infer_instance

instance modules_preservesFiniteColimits : PreservesFiniteColimits (modules l E X) := by
  unfold modules
  infer_instance

attribute [local semireducible] modules

/-- Termwise application of the prescribed transport.
Source: integral-models proof (1), Stacks 00YV and 099L.
(auxiliary; not a blueprint node). -/
abbrev complex (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :=
  ((modules l E X).mapHomologicalComplex (.up ℤ)).obj P

/-- Localization of the ordinary transport is the previously specified derived transport.
Source: Stacks 05RU. Proof: compose the two canonical exact-functor composition
isomorphisms and then the localization factorization of their composite.
(auxiliary; not a blueprint node). -/
def complexIso (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (functor l E X).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (complex l E X P) :=
  let A := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
  let B := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (scalarMap l E X)
  let C := smallModules X (constantRing l E X)
  letI : (A ⋙ B ⋙ C).Additive := inferInstance
  (Functor.isoWhiskerLeft A.mapDerivedCategory (Functor.mapDerivedCategoryCompIso B C) ≪≫
    Functor.mapDerivedCategoryCompIso A (B ⋙ C)).app
      (DerivedCategory.Q.obj P) ≪≫ (modules l E X).mapDerivedCategoryFactors.app P

/-- The actual reductions, with every quotient transition retained.
Source: Stacks 099M and 0941 (auxiliary; not a blueprint node). -/
def quotients (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ConstantCompletion.Mod (ring l E X)) ℤ :=
  Functor.ofOpSequence (X := fun n ↦ (AdicCompletion.level l E X n).obj P)
    (AdicCompletion.levelStep l E X P) ⋙
    (modules l E X).mapHomologicalComplex (.up ℤ)

/-- The actual positive quotient units commute with the successor transition.
Source: Stacks 099M. Proof: apply the coefficient quotient identity termwise.
(auxiliary; not a blueprint node). -/
theorem quotient_levelUnit_step (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (n : ℕ) : AdicCompletion.levelUnit l E X P (n + 1) ≫
      AdicCompletion.levelStep l E X P n = AdicCompletion.levelUnit l E X P n := by
  exact AdicCompletion.levelUnit_step l E X P n

/-- The strict quotient unit, transported before localization.
Source: Stacks 099M (auxiliary; not a blueprint node). -/
def quotientUnits (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (Functor.const ℕᵒᵖ).obj (complex l E X P) ⟶ quotients l E X P :=
  NatTrans.ofOpSequence
    (fun n ↦ ((modules l E X).mapHomologicalComplex (.up ℤ)).map
      (AdicCompletion.levelUnit l E X P n)) (fun n ↦ by
        change 𝟙 _ ≫ _ = _ ≫
          ((modules l E X).mapHomologicalComplex (.up ℤ)).map
            ((Functor.ofOpSequence
              (X := fun n ↦ (AdicCompletion.level l E X n).obj P)
              (AdicCompletion.levelStep l E X P)).map
                (homOfLE (Nat.le_add_right n 1)).op)
        rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp, ← Functor.map_comp,
          quotient_levelUnit_step])

/-- The transposed actual quotient tower.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def quotientComplex (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) ℤ :=
  (HomologicalComplex.functorEquivalence _ (.up ℤ) ℕᵒᵖ).inverse.obj (quotients l E X P)

/-- The cone obtained by evaluating a compatible family of chain maps.
Source: the universal property of limits; Stacks 0941.
(auxiliary; not a blueprint node). -/
def strictTowerUnitCone {C : Type*} [Category C] [HasZeroMorphisms C]
    (T : ℕᵒᵖ ⥤ CochainComplex C ℤ) (P : CochainComplex C ℤ)
    (v : (Functor.const ℕᵒᵖ).obj P ⟶ T) (i : ℤ) :
    Cone (T ⋙ HomologicalComplex.eval C (.up ℤ) i) where
  pt := P.X i
  π := Functor.whiskerRight v (HomologicalComplex.eval C (.up ℤ) i)

/-- A compatible family of chain maps induces a chain map to the termwise limit.
Source: the universal property of limits; Stacks 0941.
(auxiliary; not a blueprint node). -/
def strictTowerLimitUnit {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasLimitsOfShape ℕᵒᵖ C] (T : ℕᵒᵖ ⥤ CochainComplex C ℤ)
    (P : CochainComplex C ℤ) (v : (Functor.const ℕᵒᵖ).obj P ⟶ T) :
    P ⟶ ((lim : (ℕᵒᵖ ⥤ C) ⥤ C).mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.functorEquivalence C (.up ℤ) ℕᵒᵖ).inverse.obj T) where
  f i := limit.lift (T ⋙ HomologicalComplex.eval C (.up ℤ) i)
    (strictTowerUnitCone T P v i)
  comm' i j _ := by
    change limit.lift (T ⋙ HomologicalComplex.eval C (.up ℤ) i)
        (strictTowerUnitCone T P v i) ≫
          limMap (Functor.whiskerLeft T (HomologicalComplex.dNatTrans C (.up ℤ) i j)) =
      P.d i j ≫ limit.lift (T ⋙ HomologicalComplex.eval C (.up ℤ) j)
        (strictTowerUnitCone T P v j)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limMap_π, ← Category.assoc, limit.lift_π,
      Category.assoc, limit.lift_π]
    exact (v.app n).comm i j

/-- Compatible quotient units induce the ordinary inverse-limit unit.
Source: Stacks 0941 (auxiliary; not a blueprint node). -/
def quotientLimitUnit (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    complex l E X P ⟶
      ((lim : (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ring l E X)) ⥤ _).mapHomologicalComplex
        (.up ℤ)).obj (quotientComplex l E X P) :=
  strictTowerLimitUnit (quotients l E X P) (complex l E X P) (quotientUnits l E X P)

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
