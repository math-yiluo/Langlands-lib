/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientNative

/-! # Original presentation of the input quotient laws

Source: the current blueprint finite-level coefficient comparison
(blueprint: lem-coef-compact-support-quotient-raw-input).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.scalarReductionDerivedExtension WeilConjectures.compactSupportReductionMap
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.scalarReductionTargetDerived
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem nativeLevel_eq (X : Scheme.{u}) (n : ℕ) :
    compactSupportQuotientNativeLevel l E X n =
      scalarReductionDerivedExtension.{u, u} l E X n := by rfl

private theorem nativeRestriction_eq (X : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    compactSupportQuotientNativeRestriction l E X m n h =
      (proEtaleCoefficientRestrictScalars X
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory := by rfl

private theorem nativeMap_eq (X : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    compactSupportQuotientNativeMap l E X m n h K =
      compactSupportReductionMap l E X m n h K := by rfl

private theorem nativeResId_eq (X : Scheme.{u}) (n : ℕ) :
    compactSupportQuotientNativeResId l E X n = compactSupportQuotientResId l E X n := by
  rfl

private theorem nativeResComp_eq (X : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m) :
    compactSupportQuotientNativeResComp l E X r m n hrm hmn =
      compactSupportQuotientResComp l E X r m n hrm hmn := by rfl

private theorem nativeObj_eq (X : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (compactSupportQuotientNativeLevel l E X n).obj K =
      (scalarReductionDerivedExtension.{u, u} l E X n).obj K := by
  exact congrArg (fun F ↦ F.obj K) (nativeLevel_eq l E X n)

-- Transport dependent terms without reducing the quotient comparison casts.
private theorem dependent_congr {α : Sort _} {β : α → Sort _}
    (f : ∀ a, β a) {a b : α} (e : a = b) : HEq (f a) (f b) := by
  cases e
  rfl

private theorem isoApp_heq
    {C C' D D' : Type (u + 2)}
    [cC : Category.{u + 2} C] [cC' : Category.{u + 2} C']
    [cD : Category.{u + 2} D] [cD' : Category.{u + 2} D']
    (eC : C = C') (eD : D = D') (ecC : HEq cC cC') (ecD : HEq cD cD')
    {F G : C ⥤ D} {F' G' : C' ⥤ D'} (eF : HEq F F') (eG : HEq G G')
    {α : F ≅ G} {α' : F' ≅ G'} (eα : HEq α α')
    {x : C} {x' : C'} (ex : HEq x x') : HEq (α.hom.app x) (α'.hom.app x') := by
  cases eC
  cases eD
  cases eq_of_heq ecC
  cases eq_of_heq ecD
  cases eq_of_heq eF
  cases eq_of_heq eG
  cases eq_of_heq eα
  cases eq_of_heq ex
  rfl

private theorem nativeResId_app_heq (X : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HEq ((compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K))
      ((compactSupportQuotientResId l E X n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) := by
  exact isoApp_heq rfl rfl HEq.rfl HEq.rfl
    (heq_of_eq (nativeRestriction_eq l E X n n le_rfl)) HEq.rfl
    (heq_of_eq (nativeResId_eq l E X n)) (heq_of_eq (nativeObj_eq l E X n K))

private theorem nativeResComp_app_heq (X : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HEq ((compactSupportQuotientNativeResComp l E X r m n hrm hmn).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K))
      ((compactSupportQuotientResComp l E X r m n hrm hmn).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) := by
  exact isoApp_heq rfl rfl HEq.rfl HEq.rfl HEq.rfl
    (heq_of_eq (nativeRestriction_eq l E X r n (hmn.trans hrm)))
    (heq_of_eq (nativeResComp_eq l E X r m n hrm hmn))
    (heq_of_eq (nativeObj_eq l E X n K))

private theorem functorObj_heq
    {C C' D D' : Type (u + 2)}
    [cC : Category.{u + 2} C] [cC' : Category.{u + 2} C']
    [cD : Category.{u + 2} D] [cD' : Category.{u + 2} D']
    (eC : C = C') (eD : D = D') (ecC : HEq cC cC') (ecD : HEq cD cD')
    {F : C ⥤ D} {F' : C' ⥤ D'} (eF : HEq F F')
    {x : C} {x' : C'} (ex : HEq x x') : HEq (F.obj x) (F'.obj x') := by
  cases eC
  cases eD
  cases eq_of_heq ecC
  cases eq_of_heq ecD
  cases eq_of_heq eF
  cases eq_of_heq ex
  rfl

private theorem comp_heq
    {C C' : Type (u + 2)} [cC : Category.{u + 2} C] [cC' : Category.{u + 2} C']
    (eC : C = C') (ecC : HEq cC cC')
    {x y z : C} {x' y' z' : C'}
    (ex : HEq x x') (ey : HEq y y') (ez : HEq z z')
    {f : x ⟶ y} {f' : x' ⟶ y'} {g : y ⟶ z} {g' : y' ⟶ z'}
    (ef : HEq f f') (eg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases eC
  cases eq_of_heq ecC
  cases eq_of_heq ex
  cases eq_of_heq ey
  cases eq_of_heq ez
  cases eq_of_heq ef
  cases eq_of_heq eg
  rfl

private theorem tripleComp_heq
    {C C' : Type (u + 2)} [cC : Category.{u + 2} C] [cC' : Category.{u + 2} C']
    (eC : C = C') (ecC : HEq cC cC')
    {x y z w : C} {x' y' z' w' : C'}
    (ex : HEq x x') (ey : HEq y y') (ez : HEq z z') (ew : HEq w w')
    {f : x ⟶ y} {f' : x' ⟶ y'} {g : y ⟶ z} {g' : y' ⟶ z'}
    {h : z ⟶ w} {h' : z' ⟶ w'}
    (ef : HEq f f') (eg : HEq g g') (eh : HEq h h') :
    HEq (f ≫ g ≫ h) (f' ≫ g' ≫ h') := by
  cases eC
  cases eq_of_heq ecC
  cases eq_of_heq ex
  cases eq_of_heq ey
  cases eq_of_heq ez
  cases eq_of_heq ew
  cases eq_of_heq ef
  cases eq_of_heq eg
  cases eq_of_heq eh
  rfl

private theorem equation_eq {α β : Type (u + 2)} {a b : α} {a' b' : β}
    (ha : HEq a a') (hb : HEq b b') : (a = b) = (a' = b') := by
  cases ha
  cases eq_of_heq hb
  rfl

private theorem nativeRestriction_obj_heq (X : Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HEq ((compactSupportQuotientNativeRestriction l E X m n h).obj
        ((compactSupportQuotientNativeLevel l E X n).obj K))
      ((proEtaleCoefficientRestrictScalars X
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory.obj
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) := by
  exact functorObj_heq rfl rfl HEq.rfl HEq.rfl
    (heq_of_eq (nativeRestriction_eq l E X m n h)) (heq_of_eq (nativeObj_eq l E X n K))

private theorem nativeRestriction_double_obj_heq (X : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HEq ((compactSupportQuotientNativeRestriction l E X r m hrm).obj
        ((compactSupportQuotientNativeRestriction l E X m n hmn).obj
          ((compactSupportQuotientNativeLevel l E X n).obj K)))
      ((proEtaleCoefficientRestrictScalars X
        (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.obj
          ((proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E m n hmn)).mapDerivedCategory.obj
              ((scalarReductionDerivedExtension.{u, u} l E X n).obj K))) := by
  exact functorObj_heq rfl rfl HEq.rfl HEq.rfl
    (heq_of_eq (nativeRestriction_eq l E X r m hrm))
    (nativeRestriction_obj_heq l E X m n hmn K)

private theorem nativeIdentity_eq (X : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    𝟙 ((compactSupportQuotientNativeLevel l E X n).obj K) =
      𝟙 ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) := by
  exact eq_of_heq (dependent_congr (fun O ↦ 𝟙 O) (nativeObj_eq l E X n K))

private theorem nativeRestriction_map_eq (X : Scheme.{u})
    (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (compactSupportQuotientNativeRestriction l E X r m hrm).map
        (compactSupportQuotientNativeMap l E X m n hmn K) =
      (proEtaleCoefficientRestrictScalars X
        (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
          (compactSupportReductionMap l E X m n hmn K) := by
  calc
    _ = (compactSupportQuotientNativeRestriction l E X r m hrm).map
        (compactSupportReductionMap l E X m n hmn K) :=
      congrArg _ (nativeMap_eq l E X m n hmn K)
    _ = _ := eq_of_heq (dependent_congr
      (fun F ↦ F.map (compactSupportReductionMap l E X m n hmn K))
      (nativeRestriction_eq l E X r m hrm))

/-- The input laws in the original scalar-reduction presentation.
Source: the specified quotient unit and coefficient comparisons
(blueprint: lem-coef-compact-support-quotient-raw-input).
Proof: the native wrappers have exactly the original functors and arrows as values. -/
theorem compactSupportQuotient_raw_input
    (X : Scheme.{u}) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hi :
    (∀ n : ℕ, compactSupportQuotientNativeMap l E X n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportQuotientNativeMap l E X r m hrm K ≫
          (compactSupportQuotientNativeRestriction l E X r m hrm).map
              (compactSupportQuotientNativeMap l E X m n hmn K) ≫
          (compactSupportQuotientNativeResComp l E X r m n hrm hmn).hom.app
            ((compactSupportQuotientNativeLevel l E X n).obj K) =
        compactSupportQuotientNativeMap l E X r n (hmn.trans hrm) K)) :
    (∀ n : ℕ, compactSupportReductionMap l E X n n le_rfl K ≫
      (compactSupportQuotientResId l E X n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) = 𝟙 _) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      compactSupportReductionMap l E X r m hrm K ≫
          (proEtaleCoefficientRestrictScalars X
            (compactSupportLevelQuotient l E r m hrm)).mapDerivedCategory.map
              (compactSupportReductionMap l E X m n hmn K) ≫
          (compactSupportQuotientResComp l E X r m n hrm hmn).hom.app
            ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) =
    compactSupportReductionMap l E X r n (hmn.trans hrm) K) := by
  constructor
  · intro n
    have hc := comp_heq
      (C := proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
      (C' := DerivedCategory (scalarReductionTarget.{u, u} l E X n))
      rfl HEq.rfl (heq_of_eq (nativeObj_eq l E X n K))
      (nativeRestriction_obj_heq l E X n n le_rfl K)
      (heq_of_eq (nativeObj_eq l E X n K))
      (heq_of_eq (nativeMap_eq l E X n n le_rfl K)) (nativeResId_app_heq l E X n K)
    exact Eq.mp (equation_eq hc (heq_of_eq (nativeIdentity_eq l E X n K))) (hi.1 n)
  · intro r m n hrm hmn
    have hc := tripleComp_heq
      (C := proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (r + 1)))
      (C' := DerivedCategory (scalarReductionTarget.{u, u} l E X r))
      rfl HEq.rfl (heq_of_eq (nativeObj_eq l E X r K))
      (nativeRestriction_obj_heq l E X r m hrm K)
      (nativeRestriction_double_obj_heq l E X r m n hrm hmn K)
      (nativeRestriction_obj_heq l E X r n (hmn.trans hrm) K)
      (heq_of_eq (nativeMap_eq l E X r m hrm K))
      (heq_of_eq (nativeRestriction_map_eq l E X r m n hrm hmn K))
      (nativeResComp_app_heq l E X r m n hrm hmn K)
    exact Eq.mp (equation_eq hc (heq_of_eq (nativeMap_eq l E X r n (hmn.trans hrm) K)))
      (hi.2 r m n hrm hmn)

end WeilConjectures
