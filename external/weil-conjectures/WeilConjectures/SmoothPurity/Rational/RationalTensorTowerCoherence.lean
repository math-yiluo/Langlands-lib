/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.CategoryTheory.Tensor.TensorTowerDatum

/-! # Tensor coherence for successive rational scalar extensions

Source: the common-stage tensor argument of prose-03-02,
using the normalized scalar-extension comparisons of
lem-pur-integral-operations-scalar-extension; Stacks Project, Tags 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w u₁ v₁ u₂ v₂
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension
  rationalTensorScalarComparison HasDerivedCategory.standard integralCoefficientLinear
  ObjectProperty.FullSubcategory.category

section ProofHelpers

set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.FullSubcategory.category ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition

/-- Conjugating a tensor tower by component isomorphisms preserves its equation. -/
private theorem tensorTower_conjugate
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : C × C ⥤ C) (V : D × D ⥤ D) (B : E × E ⥤ E)
    (F F' : C ⥤ D) (G G' : D ⥤ E) (H H' : C ⥤ E)
    (a : F ⋙ G ≅ H)
    (p : U ⋙ F ≅ F.prod F ⋙ V) (q : V ⋙ G ≅ G.prod G ⋙ B)
    (r : U ⋙ H ≅ H.prod H ⋙ B) (X Y : C)
    (cX : F.obj X ≅ F'.obj X) (cY : F.obj Y ≅ F'.obj Y)
    (cT : F.obj (U.obj (X, Y)) ≅ F'.obj (U.obj (X, Y)))
    (dX : G.obj (F'.obj X) ≅ G'.obj (F'.obj X))
    (dY : G.obj (F'.obj Y) ≅ G'.obj (F'.obj Y))
    (dT : G.obj (F'.obj (U.obj (X, Y))) ≅ G'.obj (F'.obj (U.obj (X, Y))))
    (dV : G.obj (V.obj (F'.obj X, F'.obj Y)) ≅
      G'.obj (V.obj (F'.obj X, F'.obj Y)))
    (eX : H.obj X ≅ H'.obj X) (eY : H.obj Y ≅ H'.obj Y)
    (eT : H.obj (U.obj (X, Y)) ≅ H'.obj (U.obj (X, Y)))
    (hd : G.map (cT.inv ≫ p.hom.app (X, Y) ≫ V.map (Prod.mkHom cX.hom cY.hom)) ≫ dV.hom =
      dT.hom ≫ G'.map (cT.inv ≫ p.hom.app (X, Y) ≫ V.map (Prod.mkHom cX.hom cY.hom)))
    (ht : G.map (p.hom.app (X, Y)) ≫ q.hom.app (F.obj X, F.obj Y) ≫
      B.map (Prod.mkHom (a.hom.app X) (a.hom.app Y)) =
      a.hom.app (U.obj (X, Y)) ≫ r.hom.app (X, Y)) :
    G'.map (cT.inv ≫ p.hom.app (X, Y) ≫ V.map (Prod.mkHom cX.hom cY.hom)) ≫
      (dV.inv ≫ q.hom.app (F'.obj X, F'.obj Y) ≫ B.map (Prod.mkHom dX.hom dY.hom)) ≫
      B.map (Prod.mkHom (dX.inv ≫ G.map cX.inv ≫ a.hom.app X ≫ eX.hom)
        (dY.inv ≫ G.map cY.inv ≫ a.hom.app Y ≫ eY.hom)) =
    (dT.inv ≫ G.map cT.inv ≫ a.hom.app (U.obj (X, Y)) ≫ eT.hom) ≫
      (eT.inv ≫ r.hom.app (X, Y) ≫ B.map (Prod.mkHom eX.hom eY.hom)) := by
  have hq := q.hom.naturality (Prod.mkHom cX.hom cY.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hq
  apply (cancel_epi dT.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  simp only [← Category.assoc] at hd
  rw [← hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hq]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc, prod_comp,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id]
  rw [G.map_id, G.map_id]
  simp only [Category.id_comp]
  rw [show Prod.mkHom (a.hom.app X ≫ eX.hom) (a.hom.app Y ≫ eY.hom) =
    Prod.mkHom (a.hom.app X) (a.hom.app Y) ≫ Prod.mkHom eX.hom eY.hom from rfl]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ht]

variable (l : ℕ) [Fact l.Prime]
  (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]

private theorem morphismMap_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX; cases hY; cases h; rfl

private theorem morphismComp_heq {C : Type*} [Category C]
    {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hX; cases hY; cases hZ; cases hf; cases hg; rfl

private theorem morphismPair_heq {C : Type u₁} [instC : Category.{v₁} C]
    {X X' Y Y' Z Z' T T' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hT : T = T')
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Z ⟶ T} {g' : Z' ⟶ T'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (@Prod.mkHom C instC.toCategoryStruct C instC.toCategoryStruct X Y Z T f g)
      (@Prod.mkHom C instC.toCategoryStruct C instC.toCategoryStruct X' Y' Z' T' f' g') := by
  cases hX; cases hY; cases hZ; cases hT; cases hf; cases hg; rfl

private theorem morphismApp_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (a : F ⟶ G) {X X' : C} (h : X = X') :
    HEq (a.app X) (a.app X') := by cases h; rfl

section IntegralTower
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem integralOrdinaryComparison_hom
    (K : sfIntegralConstructibleCategory l E W) :
    (sfIntegralOrdinaryComparison l E L ι W).hom.app K =
      (scalarCompletion l E L ι W).app K.obj := by
  let c : (sfIntegralConstructible l E W).ι ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (sfIntegralConstructible l E W).ι ⋙ integralScalarExtension l E L ι W :=
    NatIso.ofComponents (fun K ↦ scalarCompletionIso l E L ι W K.obj K.property.1)
      (fun f ↦ (scalarCompletion l E L ι W).naturality f.hom)
  have hc : c = sfIntegralOrdinaryComparison l E L ι W :=
    (sfIntegralOrdinaryComparison_existsUnique l E L ι W).unique
      (fun P hP ↦ (scalarCompletion_existsUnique l E L ι W).exists.choose_spec.1 P)
      (sfIntegralOrdinaryComparison_existsUnique l E L ι W).exists.choose_spec
  exact (congrArg (fun a ↦ a.hom.app K) hc).symm

omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem integralOrdinaryComparison_component
    (K : sfIntegralConstructibleCategory l E W) :
    (sfIntegralOrdinaryComparison l E L ι W).app K =
      scalarCompletionIso l E L ι W K.obj K.property.1 := by
  apply Iso.ext
  exact integralOrdinaryComparison_hom l W E L ι K

private theorem integralTensor_tower
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (X Y : sfIntegralConstructibleCategory l E W) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      L M j W).map (integralTensorScalarComparison l E L ι W X Y).hom ≫
      (integralTensorScalarComparison l L M j W
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj X)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj Y)).hom ≫
      (constructibleIntegralTensor l M W).map
        (Prod.mkHom ((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app X)
         ((sfIntegralScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app Y)) =
    (sfIntegralScalarComp l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((constructibleIntegralTensor l E W).obj (X, Y)) ≫
      (integralTensorScalarComparison l E M (j.comp ι) W X Y).hom := by
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  have hi (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
      (f : A →ₐ[ℚ_[l]] B) (K : sfIntegralConstructibleCategory l A W) :
      (sfIntegralOrdinaryComparison l A B f W).inv.app K =
        (scalarCompletionIso l A B f W K.obj K.property.1).inv := by
    exact congrArg Iso.inv (integralOrdinaryComparison_component l W A B f K)
  have ha (K : sfIntegralConstructibleCategory l E W) :
      ((sfIntegralScalarComp l E L ι W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K).hom =
      (scalarCompletionIso l L M j W (S.obj K).obj (S.obj K).property.1).inv ≫
        (integralOrdinaryDerivedScalar l L M j W).map
          (scalarCompletionIso l E L ι W K.obj K.property.1).inv ≫
        (integralOrdinaryDerivedScalarComp l E L ι W M j).hom.app K.obj ≫
        (scalarCompletionIso l E M (j.comp ι) W K.obj K.property.1).hom := by
    have hc := (sfIntegralScalarComp_existsUnique l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec K
    change ((sfIntegralScalarComp l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app K).hom = _ at hc
    rw [hc, hi, hi, integralOrdinaryComparison_hom]
    rfl
  apply ObjectProperty.hom_ext
  change (integralScalarExtension l L M j W).map
      (scalarTensorCompleted l E L ι W X.obj Y.obj X.property.1 Y.property.1
        ((constructibleIntegralTensor l E W).obj (X, Y)).property.1).hom ≫
    (scalarTensorCompleted l L M j W (S.obj X).obj (S.obj Y).obj
      (S.obj X).property.1 (S.obj Y).property.1
      ((constructibleIntegralTensor l L W).obj (S.obj X, S.obj Y)).property.1).hom ≫
    (integralCompletedTensor l M W).map (Prod.mkHom
      (((sfIntegralScalarComp l E L ι W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app X).hom)
      (((sfIntegralScalarComp l E L ι W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app Y).hom)) =
    ((sfIntegralScalarComp l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((constructibleIntegralTensor l E W).obj (X, Y))).hom ≫
    (scalarTensorCompleted l E M (j.comp ι) W X.obj Y.obj X.property.1 Y.property.1
      ((constructibleIntegralTensor l E W).obj (X, Y)).property.1).hom
  rw [ha X, ha Y, ha]
  dsimp only [scalarTensorCompleted, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.prod_hom]
  apply tensorTower_conjugate
    (integralCompletedTensor l E W) (integralCompletedTensor l L W)
    (integralCompletedTensor l M W)
    (integralOrdinaryDerivedScalar l E L ι W) (integralScalarExtension l E L ι W)
    (integralOrdinaryDerivedScalar l L M j W) (integralScalarExtension l L M j W)
    (integralOrdinaryDerivedScalar l E M (j.comp ι) W)
    (integralScalarExtension l E M (j.comp ι) W)
    (integralOrdinaryDerivedScalarComp l E L ι W M j)
    (scalarTensorOrdinary l E L ι W) (scalarTensorOrdinary l L M j W)
    (scalarTensorOrdinary l E M (j.comp ι) W) X.obj Y.obj
    (scalarCompletionIso l E L ι W X.obj X.property.1)
    (scalarCompletionIso l E L ι W Y.obj Y.property.1)
    (scalarCompletionIso l E L ι W _
      ((constructibleIntegralTensor l E W).obj (X, Y)).property.1)
    (scalarCompletionIso l L M j W (S.obj X).obj (S.obj X).property.1)
    (scalarCompletionIso l L M j W (S.obj Y).obj (S.obj Y).property.1)
    (scalarCompletionIso l L M j W _
      (S.obj ((constructibleIntegralTensor l E W).obj (X, Y))).property.1)
    (scalarCompletionIso l L M j W _
      ((constructibleIntegralTensor l L W).obj (S.obj X, S.obj Y)).property.1)
    (scalarCompletionIso l E M (j.comp ι) W X.obj X.property.1)
    (scalarCompletionIso l E M (j.comp ι) W Y.obj Y.property.1)
    (scalarCompletionIso l E M (j.comp ι) W _
      ((constructibleIntegralTensor l E W).obj (X, Y)).property.1)
  · exact (scalarCompletion l L M j W).naturality _
  · exact (scalarOperationsOrdinary_tower l E L ι M j (𝟙 W) W).2.1 X.obj Y.obj

private theorem rationalTensor_obj (X Y : sfRationalConstructibleCategory l E W) :
    (rationalDerivedTensor l E W).obj (X, Y) =
      ⟨(constructibleIntegralTensor l E W).obj (X.obj, Y.obj)⟩ := by
  simpa only [rationalDerivedTensor] using
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (X, Y)

private theorem rationalTensor_map_localization
    {X X' Y Y' : sfIntegralConstructibleCategory l E W}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    HEq ((rationalDerivedTensor l E W).map (Prod.mkHom
      ((sfRationalConstructibleLocalization l E W).map f)
      ((sfRationalConstructibleLocalization l E W).map g)))
      ((sfRationalConstructibleLocalization l E W).map
        ((constructibleIntegralTensor l E W).map (Prod.mkHom f g))) := by
  obtain ⟨b, hb, hm⟩ :=
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2 ⟨X⟩ ⟨X'⟩ ⟨Y⟩ ⟨Y'⟩
  simpa only [rationalDerivedTensor, hb, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, one_mul] using hm f g 1 1

omit [∀ w : W, Invertible (l : W.residueField w)] in
private theorem rationalScalar_map_localization
    {X Y : sfIntegralConstructibleCategory l E W} (f : X ⟶ Y) :
    HEq ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
      ((sfRationalConstructibleLocalization l E W).map f))
      ((sfRationalConstructibleLocalization l L W).map
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map f)) := by
  have h := (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.2 X Y f 1
  simp only [sfRationalScalarExtension, sfRationalConstructibleLocalization,
    ScalarLocalization.localization, map_one] at h ⊢
  exact h.trans (by rfl)

private theorem rationalTensor_component (X Y : sfRationalConstructibleCategory l E W) :
    HEq ((rationalTensorScalarComparison l E L ι W).hom.app (X, Y))
      ((sfRationalConstructibleLocalization l L W).map
        (integralTensorScalarComparison l E L ι W X.obj Y.obj).hom) := by
  simpa only [rationalTensorScalarComparison] using
    (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec X Y

section RationalTower
attribute [local simp] sfRationalScalarExtension_obj rationalTensor_obj
  sfRationalConstructibleLocalization ScalarLocalization.localization

/-- Tensor coherence after completion and rationalization.
Source: scalarOperationsOrdinary_tower, tensor clause, conjugated by scalarCompletionIso
and mapped through raw rational localization. Naturality cancels adjacent completion
inverses; the rational component specifications identify all three factors.
(blueprint: lem-weil-rational-tensor-tower-coherence). -/
private theorem rationalTensor_tower_components
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) (X Y : sfRationalConstructibleCategory l E W) :
    (sfRationalScalarExtension l L W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).map
        ((rationalTensorScalarComparison l E L ι W).hom.app (X, Y)) ≫
      (rationalTensorScalarComparison l L M j W).hom.app
        ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj X,
         (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj Y) ≫
      (rationalDerivedTensor l M W).map (Prod.mkHom
        ((sfRationalScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app X)
        ((sfRationalScalarComp l E L ι W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app Y)) =
    (sfRationalScalarComp l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom.app
        ((rationalDerivedTensor l E W).obj (X, Y)) ≫
      (rationalTensorScalarComparison l E M (j.comp ι) W).hom.app (X, Y) := by
  let G := sfRationalScalarExtension l L W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j
  let S := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let a := sfRationalScalarComp l E L ι W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j
  let b := sfIntegralScalarComp l E L ι W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j
  have ha := morphismMap_heq G (by simp) (by simp)
    (rationalTensor_component l W E L ι X Y)
  have ha' := rationalScalar_map_localization l W L M j
    (integralTensorScalarComparison l E L ι W X.obj Y.obj).hom
  have hb := (morphismApp_heq (rationalTensorScalarComparison l L M j W).hom
    (congrArg₂ Prod.mk
      (sfRationalScalarExtension_obj l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι X)
      (sfRationalScalarExtension_obj l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι Y))).trans
    (rationalTensor_component l W L M j ⟨S.obj X.obj⟩ ⟨S.obj Y.obj⟩)
  have hbX := (sfRationalScalarComp_existsUnique l E L ι W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec X
  have hbY := (sfRationalScalarComp_existsUnique l E L ι W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec Y
  have hc := (morphismMap_heq (rationalDerivedTensor l M W) (by simp) (by simp)
    (morphismPair_heq (by simp) (by simp) (by simp) (by simp) hbX hbY)).trans
    (rationalTensor_map_localization l W M (b.hom.app X.obj) (b.hom.app Y.obj))
  have hd := (morphismApp_heq a.hom (rationalTensor_obj l W E X Y)).trans
    ((sfRationalScalarComp_existsUnique l E L ι W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec
      ⟨(constructibleIntegralTensor l E W).obj (X.obj, Y.obj)⟩)
  have he := rationalTensor_component l W E M (j.comp ι) X Y
  have hl := morphismComp_heq (by simp [G]) (by simp [G]) (by simp) (ha.trans ha')
    (morphismComp_heq (by simp [G]) (by simp [S]) (by simp) hb hc)
  have hr := morphismComp_heq (by simp) (by simp) (by simp) hd he
  have hi := congrArg (fun f ↦ (sfRationalConstructibleLocalization l M W).map f)
    (integralTensor_tower l W E L ι M j X.obj Y.obj)
  simp only [Functor.map_comp] at hi
  exact eq_of_heq (hl.trans ((heq_of_eq hi).trans hr.symm))

/-- The three raw coefficient categories and their prescribed tensor comparisons.
Source: the normalized rational scalar-tower construction.
(blueprint: lem-weil-rational-tensor-tower-coherence). -/
def rationalTensorTowerDatum
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) :
    TensorTowerDatum (sfRationalConstructibleCategory l E W)
      (sfRationalConstructibleCategory l L W) (sfRationalConstructibleCategory l M W) where
  catC := inferInstance
  catD := inferInstance
  catE := inferInstance
  U := rationalDerivedTensor l E W
  V := rationalDerivedTensor l L W
  B := rationalDerivedTensor l M W
  F := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  G := sfRationalScalarExtension l L W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j
  H := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M (j.comp ι)
  a := sfRationalScalarComp l E L ι W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j
  p := rationalTensorScalarComparison l E L ι W
  q := rationalTensorScalarComparison l L M j W
  r := rationalTensorScalarComparison l E M (j.comp ι) W

/-- The normalized rational tensor scalar tower is coherent.
Source: scalarOperationsOrdinary_tower, tensor clause, followed by completion
conjugation and rational localization. The component proof cancels completion
inverses and identifies localized arrows by their prescribed formulas.
(blueprint: lem-weil-rational-tensor-tower-coherence). -/
theorem rationalTensor_tower
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) :
    (rationalTensorTowerDatum l W E L ι M j).Coherent := by
  unfold TensorTowerDatum.Coherent
  intro X Y
  exact rationalTensor_tower_components l W E L ι M j X Y

end RationalTower
end IntegralTower
end ProofHelpers
end WeilConjectures
