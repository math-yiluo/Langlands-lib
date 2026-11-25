/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExact
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Shift compatibility of the normalized coefficient associators -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u
open CategoryTheory TensorProduct
namespace WeilConjectures

attribute [local irreducible] rationalTriangulationDatum
attribute [local semireducible] ObjectProperty.hasShift

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility at an invertible shift implies compatibility at its inverse. -/
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coherence extends the degree-one square to every integral shift. -/
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

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

private theorem integral_comp_commShift :
    NatTrans.CommShift (integralConstructibleScalarComp l E L i Y M j D hl).hom ℤ := by
  have : NatTrans.CommShift (integralOrdinaryDerivedScalarComp l E L i Y M j).hom ℤ := by
    have hc := Functor.commShift_mapDerivedCategoryCompIso_hom
      (integralOrdinaryScalar l E L i Y) (integralOrdinaryScalar l L M j Y)
    have hn := Functor.commShift_mapDerivedCategoryNatIso_hom
      (integralOrdinaryScalarComp l E L i Y M j)
    let := hc
    let := hn
    change NatTrans.CommShift
      ((Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L i Y)
        (integralOrdinaryScalar l L M j Y)).hom ≫
        (Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarComp l E L i Y M j)).hom) ℤ
    infer_instance
  constructor
  intro n
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, ObjectProperty.FullSubcategory.comp_hom]
  have hF := (integralConstructibleScalarCommShift_existsUnique D l hl E Y L i).exists.choose_spec
    n K
  have hG := (integralConstructibleScalarCommShift_existsUnique D l hl L Y M j).exists.choose_spec
    n ((integralConstructibleScalarExtension D l hl E L i Y).obj K)
  have hH := (integralConstructibleScalarCommShift_existsUnique
    D l hl E Y M (j.comp i)).exists.choose_spec
    n K
  have hA := (integralConstructibleScalarComp_existsUnique l E L i Y M j D hl).exists.choose_spec K
  have hB := (integralConstructibleScalarComp_existsUnique l E L i Y M j D hl).exists.choose_spec
    ((shiftFunctor _ n).obj K)
  dsimp only [integralConstructibleScalarComp] at hA hB ⊢
  simp only [Category.assoc]
  have hm : ∀ {X Z : boundedConstructibleDerivedCompleteIntegralCategory D l hl M Y}
      (f : X ⟶ Z),
      ((shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl M Y) n).map
        f).hom = (shiftFunctor (completedIntegralDerivedCategory l M Y D hl) n).map f.hom := by
    intro X Z f
    change ((@shiftFunctor _ _ _ _ (ObjectProperty.hasShift _ (A := ℤ)) n).map f).hom = _
    rfl
  rw [hm, hA, hB, eq_of_heq hH, eq_of_heq hG]
  change (integralOrdinaryDerivedScalar l L M j Y).map _ ≫ _ ≫ _ = _
  dsimp only [ObjectProperty.ι, inducedFunctor] at hF ⊢
  rw [eq_of_heq hF]
  have ho (X : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :
      ((shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) n).obj
        X).obj = (shiftFunctor (completedIntegralDerivedCategory l E Y D hl) n).obj X.obj := by
    change ((@shiftFunctor _ _ _ _ (ObjectProperty.hasShift _ (A := ℤ)) n).obj X).obj = _
    rfl
  have hom (X : boundedConstructibleDerivedCompleteIntegralCategory D l hl M Y) :
      ((shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl M Y) n).obj
        X).obj = (shiftFunctor (completedIntegralDerivedCategory l M Y D hl) n).obj X.obj := by
    change ((@shiftFunctor _ _ _ _ (ObjectProperty.hasShift _ (A := ℤ)) n).obj X).obj = _
    rfl
  convert NatTrans.shift_app_comm
    (integralOrdinaryDerivedScalarComp l E L i Y M j).hom n K.obj using 1 <;>
    dsimp only [Functor.commShiftIso_comp_hom_app, Category.assoc,
      integralConstructibleScalarExtension, ObjectProperty.lift, Functor.comp_obj,
      ObjectProperty.ι_obj, ObjectProperty.hasShift, Functor.FullyFaithful.hasShift,
      shiftFunctor, shiftMonoidalFunctor, hasShiftMk] <;>
    first | rfl | simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]

private theorem map_heq {C C' : Type*} [Category C] [Category C']
    (F : C ⥤ C') {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'
  subst Y'
  exact heq_of_eq (congrArg F.map (eq_of_heq hf))

private theorem rational_comp_commShift :
    NatTrans.CommShift (rationalOrdinaryScalarComp l E L i Y M j D hl).hom ℤ := by
  apply commShift_of_one
  constructor
  apply NatTrans.ext
  funext K
  let := integralConstructibleShift_linear l M Y D hl (1 : ℤ)
  let IE := integralConstructibleScalarExtension D l hl E L i Y
  let IL := integralConstructibleScalarExtension D l hl L M j Y
  let IM := integralConstructibleScalarExtension D l hl E M (j.comp i) Y
  let RE := rationalOrdinaryScalarExtension D l hl E Y L i
  let RL := rationalOrdinaryScalarExtension D l hl L Y M j
  let RM := rationalOrdinaryScalarExtension D l hl E Y M (j.comp i)
  let QE := rationalConstructibleLocalization D l hl E Y
  let QL := rationalConstructibleLocalization D l hl L Y
  let QM := rationalConstructibleLocalization D l hl M Y
  let α := integralConstructibleScalarComp l E L i Y M j D hl
  let β := rationalOrdinaryScalarComp l E L i Y M j D hl
  have hshiftE := (rationalTriangulationDatum D l hl E Y).choose_spec.choose_spec.1
  have hshiftL := (rationalTriangulationDatum D l hl L Y).choose_spec.choose_spec.1
  have hshiftM := (rationalTriangulationDatum D l hl M Y).choose_spec.choose_spec.1
  have hc (X : rationalConstructibleCategory D l hl E Y) :
      (shiftFunctor _ (1 : ℤ)).obj X = QE.obj ((shiftFunctor _ (1 : ℤ)).obj X.obj) :=
    Functor.congr_obj hshiftE X
  have hd (X : rationalConstructibleCategory D l hl L Y) :
      (shiftFunctor _ (1 : ℤ)).obj X = QL.obj ((shiftFunctor _ (1 : ℤ)).obj X.obj) :=
    Functor.congr_obj hshiftL X
  have he (X : rationalConstructibleCategory D l hl M Y) :
      (shiftFunctor _ (1 : ℤ)).obj X = QM.obj ((shiftFunctor _ (1 : ℤ)).obj X.obj) :=
    Functor.congr_obj hshiftM X
  have hF := (rationalOrdinaryScalarCommShift_existsUnique D l hl E Y L i).exists.choose_spec K
  have hG := (rationalOrdinaryScalarCommShift_existsUnique D l hl L Y M j).exists.choose_spec
    (RE.obj K)
  have hH := (rationalOrdinaryScalarCommShift_existsUnique
    D l hl E Y M (j.comp i)).exists.choose_spec K
  have hA := (rationalOrdinaryScalarComp_existsUnique l E L i Y M j D hl).exists.choose_spec K
  have hB := (rationalOrdinaryScalarComp_existsUnique l E L i Y M j D hl).exists.choose_spec
    ((shiftFunctor _ (1 : ℤ)).obj K)
  have hm : HEq ((shiftFunctor (rationalConstructibleCategory D l hl M Y) (1 : ℤ)).map
      (β.hom.app K)) (QM.map ((shiftFunctor _ (1 : ℤ)).map (α.hom.app K.obj))) := by
    change HEq ((shiftFunctor (rationalConstructibleCategory D l hl M Y) (1 : ℤ)).map
      ((rationalOrdinaryScalarComp_existsUnique l E L i Y M j D hl).exists.choose.hom.app K)) _
    rw [hA]
    have h := Functor.hcongr_hom hshiftM (QM.map (α.hom.app K.obj))
    refine h.trans ?_
    apply heq_of_eq
    change ScalarLocalization.mapHom _ _ _ (shiftFunctor _ (1 : ℤ)) _ _
      (1 ⊗ₜ α.hom.app K.obj) = _
    simp only [ScalarLocalization.mapHom, LinearMap.baseChange_tmul]
    rfl
  have hn : HEq (β.hom.app ((shiftFunctor _ (1 : ℤ)).obj K))
      (QM.map (α.hom.app ((shiftFunctor _ (1 : ℤ)).obj K.obj))) := by
    rw [hc]
    exact heq_of_eq ((rationalOrdinaryScalarComp_existsUnique
      l E L i Y M j D hl).exists.choose_spec _)
  have hmap : HEq (RL.map ((RE.commShiftIso (1 : ℤ)).hom.app K))
      (QM.map (IL.map ((IE.commShiftIso (1 : ℤ)).hom.app K.obj))) := by
    have hh := map_heq RL (congrArg RE.obj (hc K)) (hd (RE.obj K)) hF
    refine hh.trans (heq_of_eq ?_)
    change rationalScalarHom D l hl L Y M j _ _ (1 ⊗ₜ _) = 1 ⊗ₜ _
    exact (rationalScalarHom_existsUnique D l hl L Y M j _ _).exists.choose_spec
      1 ((IE.commShiftIso (1 : ℤ)).hom.app K.obj) |>.trans (by rw [map_one])
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc]
  have hleft₁ := heq_comp
    (congrArg (RE ⋙ RL).obj (hc K)) (congrArg RL.obj (hd (RE.obj K)))
    (he ((RE ⋙ RL).obj K)) hmap hG
  have hleft := heq_comp (congrArg (RE ⋙ RL).obj (hc K))
    (he ((RE ⋙ RL).obj K)) (he (RM.obj K)) hleft₁ hm
  have hright := heq_comp (congrArg (RE ⋙ RL).obj (hc K))
    (congrArg RM.obj (hc K)) (he (RM.obj K)) hn hH
  have : NatTrans.CommShift α.hom ℤ := integral_comp_commShift D l hl E Y L i M j
  apply eq_of_heq
  rw [Category.assoc] at hleft
  apply hleft.trans
  apply HEq.trans _ hright.symm
  apply heq_of_eq
  change (QM.map _ ≫ QM.map _) ≫ QM.map _ = QM.map _ ≫ QM.map _
  rw [← QM.map_comp, ← QM.map_comp, ← QM.map_comp]
  exact congrArg QM.map (by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc, RE, IE, IL,
      rationalOrdinaryScalarExtension, Functor.comp_obj] using
      NatTrans.shift_app_comm α.hom (1 : ℤ) K.obj)

/-- The normalized completed tensor associator preserves the signed integer shift.
Source: blueprint order 1469, composition of scalar extension, and order 1883,
exactness of scalar extension (blueprint: lem-weil-scalar-associator-shifts).
Proof: the ordinary exact derived tensor associator commutes with shift, because
its chain-level associator is a natural transformation of exact functors. The full
integral subcategory inherits this equation. At degree one the rational associator
and shift comparison are the integral maps tensored with one, so their square is
the localization image of the integral square. Zero, addition and inverse-shift
coherence extend the square to every integer. Finally the completed associator is
conjugate to this ordinary associator by the normalized completion comparisons,
which commute with all shifts by their specification. -/
theorem rationalConstructibleScalarComp_commShift :
    NatTrans.CommShift (rationalConstructibleScalarComp l E L i Y M j D hl).hom ℤ := by
  have : NatTrans.CommShift (rationalOrdinaryComparison D l hl E Y L i).hom ℤ :=
    (rationalConstructibleScalarCommShift_existsUnique D l hl E Y L i).exists.choose_spec
  have : NatTrans.CommShift (rationalOrdinaryComparison D l hl L Y M j).hom ℤ :=
    (rationalConstructibleScalarCommShift_existsUnique D l hl L Y M j).exists.choose_spec
  have : NatTrans.CommShift
      (rationalOrdinaryComparison D l hl E Y M (j.comp i)).hom ℤ :=
    (rationalConstructibleScalarCommShift_existsUnique
      D l hl E Y M (j.comp i)).exists.choose_spec
  have : NatTrans.CommShift (rationalOrdinaryScalarComp l E L i Y M j D hl).hom ℤ :=
    rational_comp_commShift D l hl E Y L i M j
  dsimp only [rationalConstructibleScalarComp, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  infer_instance

end WeilConjectures
