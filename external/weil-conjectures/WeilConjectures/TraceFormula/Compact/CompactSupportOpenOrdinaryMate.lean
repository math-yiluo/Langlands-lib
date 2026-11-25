/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions

/-! # Ordinary open evaluation mate for compact support

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI, 03DJ, 07A4, 0941.
This module specializes the ordinary system calculus to the actual pro-etale functors.
(blueprint: lem-trf-compact-support-open-ordinary-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.constantSheaf

universe t u c₁ c₂ d₁ d₂ v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.TwoSquare

namespace WeilConjectures

private theorem inverseMateFromUnit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (δ : TwoSquare R₁ H G R₂) (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (hn : ∀ M, G.map (a.unit.app M) ≫ δ.app (L₁.obj M) ≫
      R₂.map (e.hom.app M) = b.unit.app (G.obj M)) :
    ((mateEquiv a b).symm δ) = e.inv := by
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu := unit_mateEquiv_symm a b δ M
  dsimp only [Functor.id_obj] at hu
  rw [← hu]
  apply (cancel_mono (R₂.map (e.hom.app M))).1
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [R₂.map_id, Category.comp_id]
  exact hn M

private theorem pastedInverse
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {L₂ : D ⥤ E} {L₃ : B ⥤ C} {L₄ : E ⥤ F}
    {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
    (e₁ : L₁ ⋙ H ≅ G ⋙ L₂) (e₂ : L₃ ⋙ K ≅ H ⋙ L₄) :
    ((TwoSquare.mk G L₁ L₂ H e₁.inv) ≫ᵥ
      (TwoSquare.mk H L₃ L₄ K e₂.inv)) =
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ e₂ ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ L₄ ≪≫
        Functor.associator _ _ _).inv := by
  apply NatTrans.ext
  funext M
  simp only [TwoSquare.vComp, TwoSquare.mk,
    Functor.isoWhiskerRight, Functor.isoWhiskerLeft, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp]
  rfl

private theorem equivalenceMateIsIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (f : C ≌ D) {G : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G e.functor f.functor H) [IsIso α] :
    IsIso (mateEquiv e.toAdjunction f.toAdjunction α) := by
  dsimp only [mateEquiv, Equiv.coe_fn_mk]
  infer_instance

private theorem pastedMateIsIso
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
    {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (d : L₄ ⊣ R₄)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    [IsIso (mateEquiv a b α)] [IsIso (mateEquiv c d β)] :
    IsIso (mateEquiv (a.comp c) (b.comp d) (α ≫ᵥ β)) := by
  rw [mateEquiv_hcomp]
  dsimp only [TwoSquare.hComp]
  infer_instance

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary open restriction-evaluation square has the specified inverse
mate. This is an underived assertion for a single coefficient level; it asserts
no derived comparison, direct image, or coefficient transition compatibility.
Source: Stacks 03DI--03DJ and 0941; Zheng Construction 4.1
(blueprint: lem-trf-compact-support-open-ordinary-mate).
Proof: transport restriction to the open slice using the inverse of the system
coefficient equivalence and the inverse finite coefficient equivalence. The
transportEvaluation comparison identifies their evaluations. Compose this with
the given openSystems.restrictionEvaluation. The resulting right square is an
isomorphism, since each of its factors is. The equivalence adjunctions have the
usual evaluation and coevaluation as unit and counit. The ordinary localized
extension adjunction is normalized by its summand Hom correspondence. Substitute
the openSystems unit_evaluation formula in the unit of the composite system
adjunction, then cancel the coefficient equivalence unit/counit pairs. The result
is the unit equation characterizing the inverse mate of the constructed right
square as extensionEvaluation.inv. Injectivity of the finite adjunction Hom
bijection proves the equation. The empty and identity open, and level zero,
use the same summand calculation. -/
theorem compactSupportOpenOrdinaryMate
    {X Z : Scheme.{t}} (j : X ⟶ Z) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations l E j) (n : ℕ) :
    ∃ d : IntegralOpenReduction.systemRestriction l E j o ⋙
          coefficientSequenceEvaluation l E X n ≅
        coefficientSequenceEvaluation l E Z n ⋙
          IntegralOpenReduction.finiteRestriction l E j o n,
      ((mateEquiv (IntegralOpenReduction.ordinarySystemAdjunction l E j o)
        ((o.finite n).toAdjunction.comp
          (SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
            (integralCoefficientCommRingSheaf l E Z n)
            (IntegralOpenReduction.openObject j)))).symm
        (TwoSquare.mk _ _ _ _ d.hom)) =
          (IntegralOpenReduction.extensionEvaluation l E j o n).inv := by
  let a := o.openSystems.ordinaryAdjunction
  let b := SheafOfModules.localizedSystemAdjunction.{t+1, t, max u (t+1)}
    (integralCoefficientCommRingSheaf l E Z n) (IntegralOpenReduction.openObject j)
  let α := TwoSquare.mk _ _ _ _ (o.transportEvaluation n).inv
  let β := TwoSquare.mk _ _ _ _ (o.openSystems.extensionEvaluation n).inv
  let δ := TwoSquare.mk _ _ _ _ (o.openSystems.restrictionEvaluation n).hom
  have hβ : ((mateEquiv a b).symm δ) = β :=
    inverseMateFromUnit a b δ (o.openSystems.extensionEvaluation n)
      (o.openSystems.unit_evaluation n)
  have hβ' : (mateEquiv a b β) = δ := by
    have hsq : (mateEquiv a b).symm δ = β := hβ
    exact
      (((Equiv.symm_apply_eq (mateEquiv a b)).mp hsq).symm)
  have iα : IsIso (mateEquiv o.systems.toAdjunction (o.finite n).toAdjunction α) :=
    equivalenceMateIsIso o.systems (o.finite n) α
  have iβ : IsIso (mateEquiv a b β) := by
    rw [hβ']
    exact inferInstanceAs (IsIso (o.openSystems.restrictionEvaluation n).hom)
  let γ := α ≫ᵥ β
  have iγ : IsIso (mateEquiv (o.systems.toAdjunction.comp a)
      ((o.finite n).toAdjunction.comp b) γ) :=
    pastedMateIsIso o.systems.toAdjunction (o.finite n).toAdjunction a b α β
  let d := asIso (mateEquiv (o.systems.toAdjunction.comp a)
    ((o.finite n).toAdjunction.comp b) γ)
  refine ⟨d, ?_⟩
  change ((mateEquiv (o.systems.toAdjunction.comp a)
    ((o.finite n).toAdjunction.comp b)).symm
    (mateEquiv (o.systems.toAdjunction.comp a)
      ((o.finite n).toAdjunction.comp b) γ)) = _
  rw [Equiv.symm_apply_apply]
  exact pastedInverse (o.transportEvaluation n) (o.openSystems.extensionEvaluation n)

end WeilConjectures
