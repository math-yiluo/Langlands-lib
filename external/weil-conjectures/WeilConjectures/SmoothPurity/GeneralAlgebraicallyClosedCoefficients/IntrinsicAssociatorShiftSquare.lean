/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages

import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.IntrinsicScalarNormalizationFormulas

/-! # The intrinsic scalar associator commutes with integer shifts

Source: blueprint order 1462, common-stage shift clause, and
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-derived-extend-comp-iso.proof.md`,
exact derived scalar composition, with the intrinsic normalization specified in
`SfScalarExtensionComposition.lean` and `GeneralAlgebraicallyClosedCoefficientStages.lean`
(blueprint: lem-pur-intrinsic-associator-shift-square).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory TensorProduct

namespace WeilConjectures.GeneralAlgebraicallyClosedCoefficients

open CategoryTheory.Limits
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Keep the coefficient constructions behind their published normalization interfaces.
attribute [local irreducible] ScalarLocalization.composition
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

attribute [local irreducible] sfIntegralOrdinaryComparison sfIntegralScalarComp
  sfRationalScalarComp sfRationalTriangulationDatum sfRationalScalarExtension

private theorem normalized_comparison_commShift
    {C D A : Type*} [Category C] [Category D] [Category A]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift A ℤ]
    (F : C ⥤ D) (I : D ⥤ A) (H : C ⥤ A)
    [F.CommShift ℤ] [I.CommShift ℤ] [H.CommShift ℤ]
    (e : H ≅ F ⋙ I)
    (h : ∀ (n : ℤ) (X : C),
      I.map ((F.commShiftIso n).hom.app X) ≫
          (I.commShiftIso n).hom.app (F.obj X) =
        e.inv.app (X⟦n⟧) ≫ (H.commShiftIso n).hom.app X ≫
          (shiftFunctor A n).map (e.hom.app X)) :
    NatTrans.CommShift e.hom ℤ := by
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app]
  have hh := congrArg (fun f ↦ e.hom.app (X⟦n⟧) ≫ f) (h n X)
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hh.symm

section Integral

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

@[instance_reducible]
private noncomputable def normalizedIntegralShift :
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y).CommShift ℤ :=
  (integralScalarCommShift_existsUnique l E L i Y).exists.choose

attribute [local instance] normalizedIntegralShift

private noncomputable def normalizedComparison :
    (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L i Y ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y ⋙ (sfIntegralConstructible l L Y).ι :=
  sfIntegralOrdinaryComparison l E L i Y

attribute [local irreducible] normalizedComparison

private theorem integral_comparison_commShift :
    NatTrans.CommShift (normalizedComparison l E L i Y).hom ℤ := by
  apply normalized_comparison_commShift
    (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y)
    (sfIntegralConstructible l L Y).ι
    ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L i Y)
    (normalizedComparison l E L i Y)
  intro n K
  simp only [normalizedComparison, ObjectProperty.ι_map, ObjectProperty.ι_obj]
  exact eq_of_heq ((integralScalarCommShift_existsUnique l E L i Y).exists.choose_spec n K)

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

private theorem ordinary_comp_commShift :
    NatTrans.CommShift (integralOrdinaryDerivedScalarComp l E L i Y M j).hom ℤ := by
  have := Functor.commShift_mapDerivedCategoryCompIso_hom
    (integralOrdinaryScalar l E L i Y) (integralOrdinaryScalar l L M j Y)
  have := Functor.commShift_mapDerivedCategoryNatIso_hom
    (integralOrdinaryScalarComp l E L i Y M j)
  change NatTrans.CommShift
    ((Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L i Y)
      (integralOrdinaryScalar l L M j Y)).hom ≫
      (Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarComp l E L i Y M j)).hom) ℤ
  infer_instance

private theorem integral_comp_commShift :
    NatTrans.CommShift (sfIntegralScalarComp l E L i Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom ℤ := by
  have := integral_comparison_commShift l E L i Y
  have := integral_comparison_commShift l L M j Y
  have := integral_comparison_commShift l E M (j.comp i) Y
  have := ordinary_comp_commShift l E L i Y M j
  have he : Functor.whiskerRight
      (sfIntegralScalarComp l E L i Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom
      (sfIntegralConstructible l M Y).ι =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (normalizedComparison l L M j Y).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (normalizedComparison l E L i Y).inv
          (integralOrdinaryDerivedScalar l L M j Y) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (integralOrdinaryDerivedScalarComp l E L i Y M j).hom ≫
        (normalizedComparison l E M (j.comp i) Y).hom := by
    ext K
    simp only [sfIntegralScalarComp, normalizedComparison, ObjectProperty.ι_map,
      ObjectProperty.ι_obj, Functor.comp_obj, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    exact (sfIntegralScalarComp_existsUnique l E L i Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).exists.choose_spec K
  have : NatTrans.CommShift (Functor.whiskerRight
      (sfIntegralScalarComp l E L i Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j).hom
      (sfIntegralConstructible l M Y).ι) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ (sfIntegralConstructible l M Y).ι

private theorem integral_corrected_comp_commShift
    (q : E →ₐ[Padic l] M) (hq : j.comp i = q) :
    NatTrans.CommShift
      (sfIntegralScalarComp l E L i Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) M j ≪≫
        eqToIso (congrArg (fun f ↦ sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E M f Y) hq)).hom ℤ := by
  subst q
  simpa only [eqToIso_refl, Iso.trans_refl] using integral_comp_commShift l E L i Y M j

private theorem rationalLocalization_eq :
    sfRationalConstructibleLocalization l E Y =
      ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
        (sfIntegralConstructibleCategory l E Y)
        (Padic.coefficientExtensionUniformizer l E) := rfl

private theorem rational_map_one_tmul
    (K K' : sfIntegralConstructibleCategory l E Y) (f : K ⟶ K') :
    HEq ((sfRationalScalarExtension l E Y 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).map
      (show (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
          (sfIntegralConstructibleCategory l E Y)
          (Padic.coefficientExtensionUniformizer l E)).obj K ⟶
        (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
          (sfIntegralConstructibleCategory l E Y)
          (Padic.coefficientExtensionUniformizer l E)).obj K' from
        (1 : Localization.Away (Padic.coefficientExtensionUniformizer l E))
          ⊗ₜ[Padic.coefficientExtensionIntegers l E] f))
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
        ⊗ₜ[Padic.coefficientExtensionIntegers l L]
        (sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y).map f :
        (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l L)
          (sfIntegralConstructibleCategory l L Y)
          (Padic.coefficientExtensionUniformizer l L)).obj
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y).obj K) ⟶
        (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l L)
          (sfIntegralConstructibleCategory l L Y)
          (Padic.coefficientExtensionUniformizer l L)).obj
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L i Y).obj K')) := by
  have h := sfRationalScalarExtension_map_tmul l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i K K' f 1
  simp only [rationalLocalization_eq, ScalarLocalization.localization, map_one] at h
  convert h using 1; rfl

end Integral

private theorem commShiftCore_neg
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (n : ℤ) (h : NatTrans.CommShiftCore τ n) :
    NatTrans.CommShiftCore τ (-n) := by
  constructor
  ext X
  apply (shiftFunctor D n).map_injective
  have hz : NatTrans.CommShiftCore τ (-n + n) := by
    simpa only [neg_add_cancel] using NatTrans.CommShiftCore.zero (τ := τ) ℤ
  have hs := hz.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Category.assoc] at hs
  rw [← NatTrans.naturality_assoc] at hs
  have hD := (shiftFunctorAdd D (-n) n).inv.naturality (τ.app X)
  dsimp only [Functor.comp_map] at hD
  rw [← hD] at hs
  apply (cancel_epi (F.map ((shiftFunctorAdd C (-n) n).hom.app X) ≫
    (F.commShiftIso n).hom.app (X⟦-n⟧))).mp
  apply (cancel_mono ((shiftFunctorAdd D (-n) n).inv.app (G.obj X))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, h.shift_app_comm_assoc τ] using hs

private theorem commShift_of_one
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) (h : NatTrans.CommShiftCore τ (1 : ℤ)) :
    NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn := commShiftCore_neg τ 1 h
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero (τ := τ) ℤ
  | @succ n ih => exact ih.add h
  | @pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

private theorem map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem map_app_heq {C D A : Type*}
    [Category C] [Category D] [Category A]
    (Q : D ⥤ A) {F G : C ⥤ D} (τ : F ⟶ G)
    {X Y : C} (h : X = Y) : HEq (Q.map (τ.app X)) (Q.map (τ.app Y)) := by
  cases h
  rfl

section LocalizationSquare

variable {R₀ R₁ R₂ : Type*} [CommRing R₀] [CommRing R₁] [CommRing R₂]
  {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Preadditive C₀] [Preadditive C₁] [Preadditive C₂]
  [Linear R₀ C₀] [Linear R₁ C₁] [Linear R₂ C₂]
  [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [(shiftFunctor C₀ (1 : ℤ)).Additive] [(shiftFunctor C₁ (1 : ℤ)).Additive]
  [(shiftFunctor C₂ (1 : ℤ)).Additive]
  [(shiftFunctor C₀ (1 : ℤ)).Linear R₀] [(shiftFunctor C₁ (1 : ℤ)).Linear R₁]
  [(shiftFunctor C₂ (1 : ℤ)).Linear R₂]
  (p₀ : R₀) (p₁ : R₁) (p₂ : R₂)

local notation "D₀" => ScalarLocalization R₀ C₀ p₀
local notation "D₁" => ScalarLocalization R₁ C₁ p₁
local notation "D₂" => ScalarLocalization R₂ C₂ p₂
local notation "Q₀" => ScalarLocalization.localization R₀ C₀ p₀
local notation "Q₁" => ScalarLocalization.localization R₁ C₁ p₁
local notation "Q₂" => ScalarLocalization.localization R₂ C₂ p₂

variable [s₀ : HasShift (ScalarLocalization R₀ C₀ p₀) ℤ]
  [s₁ : HasShift (ScalarLocalization R₁ C₁ p₁) ℤ]
  [s₂ : HasShift (ScalarLocalization R₂ C₂ p₂) ℤ]

private theorem localized_comp_core
    (IE : C₀ ⥤ C₁) (IL : C₁ ⥤ C₂) (IM : C₀ ⥤ C₂)
    [IE.CommShift ℤ] [IL.CommShift ℤ] [IM.CommShift ℤ]
    (RE : D₀ ⥤ D₁) (RL : D₁ ⥤ D₂) (RM : D₀ ⥤ D₂)
    [cRE : RE.CommShift ℤ] [cRL : RL.CommShift ℤ] [cRM : RM.CommShift ℤ]
    (α : IE ⋙ IL ≅ IM) [NatTrans.CommShift α.hom ℤ] (β : RE ⋙ RL ≅ RM)
    (hsE : shiftFunctor D₀ (1 : ℤ) = ScalarLocalization.map R₀ C₀ p₀
      (shiftFunctor C₀ (1 : ℤ)))
    (hsL : shiftFunctor D₁ (1 : ℤ) = ScalarLocalization.map R₁ C₁ p₁
      (shiftFunctor C₁ (1 : ℤ)))
    (hsM : shiftFunctor D₂ (1 : ℤ) = ScalarLocalization.map R₂ C₂ p₂
      (shiftFunctor C₂ (1 : ℤ)))
    (hRE : ∀ X, RE.obj X = (Q₁).obj (IE.obj X.obj))
    (hRL : ∀ X, RL.obj X = (Q₂).obj (IL.obj X.obj))
    (hRM : ∀ X, RM.obj X = (Q₂).obj (IM.obj X.obj))
    (hFs : ∀ X, HEq ((RE.commShiftIso (1 : ℤ)).hom.app X)
      ((Q₁).map ((IE.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hGs : ∀ X, HEq ((RL.commShiftIso (1 : ℤ)).hom.app X)
      ((Q₂).map ((IL.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hHs : ∀ X, HEq ((RM.commShiftIso (1 : ℤ)).hom.app X)
      ((Q₂).map ((IM.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hmapR : ∀ (X Y : C₁) (f : X ⟶ Y),
      HEq (RL.map (show (Q₁).obj X ⟶ (Q₁).obj Y from
        (1 : Localization.Away p₁) ⊗ₜ[R₁] f))
        ((1 : Localization.Away p₂) ⊗ₜ[R₂] IL.map f :
          (Q₂).obj (IL.obj X) ⟶ (Q₂).obj (IL.obj Y)))
    (hAs : ∀ X, HEq (β.hom.app X) ((Q₂).map (α.hom.app X.obj))) :
    NatTrans.CommShiftCore β.hom (1 : ℤ) := by
  constructor
  apply NatTrans.ext
  funext K
  let QE := Q₀
  let QL := Q₁
  let QM := Q₂
  have hc (X : D₀) : X⟦(1 : ℤ)⟧ = QE.obj (X.obj⟦(1 : ℤ)⟧) :=
    Functor.congr_obj hsE X
  have hd (X : D₁) : X⟦(1 : ℤ)⟧ = QL.obj (X.obj⟦(1 : ℤ)⟧) :=
    Functor.congr_obj hsL X
  have he (X : D₂) : X⟦(1 : ℤ)⟧ = QM.obj (X.obj⟦(1 : ℤ)⟧) :=
    Functor.congr_obj hsM X
  have hobj : (RE.obj K).obj = IE.obj K.obj :=
    congrArg ScalarLocalization.obj (hRE K)
  have hcomp (X : D₀) :
      (RE ⋙ RL).obj X = QM.obj ((IE ⋙ IL).obj X.obj) := by
    dsimp only [Functor.comp_obj]
    rw [hRL, hRE]
    rfl
  have hF := hFs K
  have hG := (hGs (RE.obj K)).trans
    (map_app_heq QM (IL.commShiftIso (1 : ℤ)).hom hobj)
  have hH := hHs K
  have hA := hAs K
  have hm : HEq ((shiftFunctor D₂ (1 : ℤ)).map (β.hom.app K))
      (QM.map ((shiftFunctor C₂ (1 : ℤ)).map (α.hom.app K.obj))) := by
    refine (map_heq (shiftFunctor D₂ (1 : ℤ)) (hcomp K) (hRM K) hA).trans ?_
    have hh := Functor.hcongr_hom hsM (QM.map (α.hom.app K.obj))
    refine hh.trans (heq_of_eq ?_)
    change ScalarLocalization.mapHom _ _ _ (shiftFunctor C₂ (1 : ℤ)) _ _
      (1 ⊗ₜ α.hom.app K.obj) = _
    simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
    rfl
  have hn : HEq (β.hom.app (K⟦(1 : ℤ)⟧))
      (QM.map (α.hom.app (K.obj⟦(1 : ℤ)⟧))) := by
    exact (hAs (K⟦(1 : ℤ)⟧)).trans
      (map_app_heq QM α.hom (congrArg ScalarLocalization.obj (hc K)))
  have hmap : HEq (RL.map ((RE.commShiftIso (1 : ℤ)).hom.app K))
      (QM.map (IL.map ((IE.commShiftIso (1 : ℤ)).hom.app K.obj))) := by
    have hs : RE.obj (K⟦(1 : ℤ)⟧) = QL.obj (IE.obj (K.obj⟦(1 : ℤ)⟧)) := by
      rw [hRE, hc]
      rfl
    have ht : (RE.obj K)⟦(1 : ℤ)⟧ = QL.obj ((IE.obj K.obj)⟦(1 : ℤ)⟧) := by
      rw [hd, hobj]
    refine (map_heq RL hs ht hF).trans ?_
    dsimp only [QL, QM, ScalarLocalization.localization]
    exact hmapR _ _ ((IE.commShiftIso (1 : ℤ)).hom.app K.obj)
  have hs : (RE ⋙ RL).obj (K⟦(1 : ℤ)⟧) =
      QM.obj ((IE ⋙ IL).obj (K.obj⟦(1 : ℤ)⟧)) := by
    rw [hcomp, hc]
    rfl
  have hi : RL.obj ((RE.obj K)⟦(1 : ℤ)⟧) =
      QM.obj (IL.obj ((IE.obj K.obj)⟦(1 : ℤ)⟧)) := by
    rw [hRL, hd, hobj]
    rfl
  have ht : ((RE ⋙ RL).obj K)⟦(1 : ℤ)⟧ =
      QM.obj (((IE ⋙ IL).obj K.obj)⟦(1 : ℤ)⟧) := by
    rw [he, hcomp]
    rfl
  have hu : (RM.obj K)⟦(1 : ℤ)⟧ = QM.obj ((IM.obj K.obj)⟦(1 : ℤ)⟧) := by
    rw [he, hRM]
    rfl
  have hv : RM.obj (K⟦(1 : ℤ)⟧) = QM.obj (IM.obj (K.obj⟦(1 : ℤ)⟧)) := by
    rw [hRM, hc]
    rfl
  have hleft₁ := heq_comp hs hi ht hmap hG
  have hleft := heq_comp hs ht hu hleft₁ hm
  have hright := heq_comp hs hv hu hn hH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  apply eq_of_heq
  rw [Category.assoc] at hleft
  refine hleft.trans (HEq.trans ?_ hright.symm)
  apply heq_of_eq
  change (QM.map _ ≫ QM.map _) ≫ QM.map _ = QM.map _ ≫ QM.map _
  rw [← QM.map_comp, ← QM.map_comp, ← QM.map_comp]
  exact congrArg QM.map (by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm α.hom (1 : ℤ) K.obj)

private theorem localized_comp_core_with_Q
    (A₀ : C₀ ⥤ D₀) (A₁ : C₁ ⥤ D₁) (A₂ : C₂ ⥤ D₂)
    (e₀ : A₀ = Q₀) (e₁ : A₁ = Q₁) (e₂ : A₂ = Q₂)
    (IE : C₀ ⥤ C₁) (IL : C₁ ⥤ C₂) (IM : C₀ ⥤ C₂)
    [IE.CommShift ℤ] [IL.CommShift ℤ] [IM.CommShift ℤ]
    (RE : D₀ ⥤ D₁) (RL : D₁ ⥤ D₂) (RM : D₀ ⥤ D₂)
    [cRE : RE.CommShift ℤ] [cRL : RL.CommShift ℤ] [cRM : RM.CommShift ℤ]
    (α : IE ⋙ IL ≅ IM) [NatTrans.CommShift α.hom ℤ] (β : RE ⋙ RL ≅ RM)
    (hsE : shiftFunctor D₀ (1 : ℤ) = ScalarLocalization.map R₀ C₀ p₀
      (shiftFunctor C₀ (1 : ℤ)))
    (hsL : shiftFunctor D₁ (1 : ℤ) = ScalarLocalization.map R₁ C₁ p₁
      (shiftFunctor C₁ (1 : ℤ)))
    (hsM : shiftFunctor D₂ (1 : ℤ) = ScalarLocalization.map R₂ C₂ p₂
      (shiftFunctor C₂ (1 : ℤ)))
    (hRE : ∀ X, RE.obj X = A₁.obj (IE.obj X.obj))
    (hRL : ∀ X, RL.obj X = A₂.obj (IL.obj X.obj))
    (hRM : ∀ X, RM.obj X = A₂.obj (IM.obj X.obj))
    (hFs : ∀ X, HEq ((RE.commShiftIso (1 : ℤ)).hom.app X)
      (A₁.map ((IE.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hGs : ∀ X, HEq ((RL.commShiftIso (1 : ℤ)).hom.app X)
      (A₂.map ((IL.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hHs : ∀ X, HEq ((RM.commShiftIso (1 : ℤ)).hom.app X)
      (A₂.map ((IM.commShiftIso (1 : ℤ)).hom.app X.obj)))
    (hmapR : ∀ (X Y : C₁) (f : X ⟶ Y),
      HEq (RL.map (show (Q₁).obj X ⟶ (Q₁).obj Y from
        (1 : Localization.Away p₁) ⊗ₜ[R₁] f))
        ((1 : Localization.Away p₂) ⊗ₜ[R₂] IL.map f :
          (Q₂).obj (IL.obj X) ⟶ (Q₂).obj (IL.obj Y)))
    (hAs : ∀ X : C₀, HEq (β.hom.app (A₀.obj X)) (A₂.map (α.hom.app X))) :
    NatTrans.CommShiftCore β.hom (1 : ℤ) := by
  subst A₀
  subst A₁
  subst A₂
  apply localized_comp_core p₀ p₁ p₂ IE IL IM RE RL RM α β
  · exact hsE
  · exact hsL
  · exact hsM
  · exact hRE
  · exact hRL
  · exact hRM
  · exact hFs
  · exact hGs
  · exact hHs
  · exact hmapR
  · intro X
    simpa only [ScalarLocalization.localization] using hAs X.obj

end LocalizationSquare

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual intrinsic tensor associator preserves the uniquely integral-image-normalized
coherent integer shifts. The composite functor has the composite shift comparison.
Thus at every integer `n` and object `K`, its hom at `K[n]` followed by the direct
transition's comparison equals the composite comparison followed by its shifted hom.
Repeated fields are permitted, with the actual coefficient-composition equality transports.

Source: blueprint order 1462, retained common-stage shift clause, and
`def-sfb-derived-extend-comp-iso.proof.md`, exact derived scalar composition
(blueprint: lem-pur-intrinsic-associator-shift-square).

Proof: (1) Apply lem-pur-intrinsic-scalar-normalization-formulas to the three actual
coefficient inclusions. Its formulas fix the ordinary, integral and rational associators
and the ordinary-to-completed integral shifts, including the endpoint transports.
(2) On a cochain representative, the ordinary associator at `P[n]` has degree `r`
component the ordinary associator at `P^(r+n)`: both send `c ⊗ (b ⊗ x)` to
`c j(b) ⊗ x`. The termwise comparisons are identities and both differentials have
sign `(-1)^n`. The shift-compatible exact-functor factorization and uniqueness of
localization descent (situation-conventions and
lem-weil-pbc-localization-universal-property) give the ordinary derived square.
(3) The normalization formula makes the ordinary-to-completed comparison and its
inverse shift-compatible. Composition and whiskering preserve this property by
lem-weil-pbc-commshift-nattrans-comp-whisker. Apply the faithful full integral inclusion
to the required integral square, expand its shift comparison, and cancel the final
invertible inclusion comparison. The remainder is the ordinary square from (2).
(4) Conjugate the localized integral shift by the localization comparisons `q`:
`q_L ∘ Q_L(τ) ∘ T(q_E⁻¹)` in right-to-left mathematical composition order.
Integral naturality gives naturality on `f ⊗ 1`; scalar multiplication and addition
give it on every rational arrow. Localized inverses give inverses. The zero and
addition equations follow by cancelling adjacent `q⁻¹ q` and using the corresponding
equations for `q` and the integral shifts. At shift one the normalization is the
specified integral image, so transitionCommShift_existsUnique identifies this coherent
datum with the published transitionCommShift in every degree. This uses
lem-weil-linear-scalar-localization-triangulated, def-weil-linear-scalar-localization,
def-weil-rationalization-karoubi and lem-general-algebraically-closed-coefficient-stages.
(5) Apply rationalization to (3). The normalization formulas identify the localized
integral associator with the actual rational associator. Precompose the proposed square
by the invertible composite transition applied to `q_E`. Substitute (4); naturality of
the associator and `q_M` cancels the intermediate comparisons. The two paths become
`q_M` after the rationalization of the two sides of (3), so they agree. Cancel the
invertible precomposition. Every rational object is an integral object, so this proves
the asserted square on the entire raw rational category. Keep the inclusion equality
casts throughout, also for repeated indices; no finite-field datum or hypothesis on
`Y` is used. -/
theorem associator_commShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (E L M : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L) (k : L ≤ M) :
    NatTrans.CommShift (associator l Ω Y E L M h k).hom ℤ := by
  let α := sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
      eqToIso (congrArg
        (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω M) i Y)
        ((coefficientInclusion_laws l Ω).2 E L M h k))
  have : NatTrans.CommShift α.hom ℤ :=
    integral_corrected_comp_commShift l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k) (coefficientInclusion l Ω E M (h.trans k))
      ((coefficientInclusion_laws l Ω).2 E L M h k)
  apply commShift_of_one
  apply localized_comp_core_with_Q
    (s₀ := stageShift l Ω Y E) (s₁ := stageShift l Ω Y L) (s₂ := stageShift l Ω Y M)
    (cRE := transitionCommShift l Ω Y E L h) (cRL := transitionCommShift l Ω Y L M k)
    (cRM := transitionCommShift l Ω Y E M (h.trans k))
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω L))
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω M))
    (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y)
    (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y)
    (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω M) Y)
    (rationalLocalization_eq l (Coefficient.{u} l Ω E) Y)
    (rationalLocalization_eq l (Coefficient.{u} l Ω L) Y)
    (rationalLocalization_eq l (Coefficient.{u} l Ω M) Y)
    (integralTransition l Ω Y E L h) (integralTransition l Ω Y L M k)
    (integralTransition l Ω Y E M (h.trans k))
    (transition l Ω Y E L h) (transition l Ω Y L M k)
    (transition l Ω Y E M (h.trans k))
    α (associator l Ω Y E L M h k)
  · exact (sfRationalTriangulationDatum l (Coefficient.{u} l Ω E) Y)
      |>.choose_spec.choose_spec.1
  · exact (sfRationalTriangulationDatum l (Coefficient.{u} l Ω L) Y)
      |>.choose_spec.choose_spec.1
  · exact (sfRationalTriangulationDatum l (Coefficient.{u} l Ω M) Y)
      |>.choose_spec.choose_spec.1
  · exact sfRationalScalarExtension_obj l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h)
  · exact sfRationalScalarExtension_obj l (Coefficient.{u} l Ω L) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k)
  · exact sfRationalScalarExtension_obj l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω E M (h.trans k))
  · exact (transitionCommShift_existsUnique l Ω Y E L h).exists.choose_spec
  · exact (transitionCommShift_existsUnique l Ω Y L M k).exists.choose_spec
  · exact (transitionCommShift_existsUnique l Ω Y E M (h.trans k)).exists.choose_spec
  · intro X Z f
    dsimp only [transition, integralTransition]
    exact rational_map_one_tmul l (Coefficient.{u} l Ω L) (Coefficient.{u} l Ω M)
      (coefficientInclusion l Ω L M k) Y X Z f
  · exact intrinsicRationalScalarAssociator_image l Ω Y E L M h k

end WeilConjectures.GeneralAlgebraicallyClosedCoefficients
