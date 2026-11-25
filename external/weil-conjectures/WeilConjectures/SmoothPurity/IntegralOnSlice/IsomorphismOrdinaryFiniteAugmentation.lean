/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
public import WeilConjectures.TraceFormula.QuotientTensor.QuotientTensorInsertion

/-! # Finite-level normalization of the ordinary completion augmentation

Source: Stacks Tags 03D2 and 03EL; expanded clause 4 of
prose-10-21.
(blueprint: lem-pur-isomorphism-ordinary-finite-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralOnSlice

attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted
attribute [local instance_reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.restrict IntegralOnSlice.ring
attribute [local instance_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem mapCompIdApply
    {C D : Type*} [Category C] [Category D] {FC : D → D → Type*} {CC : D → Type*}
    [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory D FC] (F : C ⥤ D) {A B : C}
    (f : A ⟶ B) (h : B ⟶ A) (hcomp : f ≫ h = 𝟙 _) (x : CC (F.obj A)) :
    (F.map h) ((F.map f) x) = x := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp, F.map_id,
    ConcreteCategory.id_apply]

private theorem finitePullbackGenerator_counit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (M : integralOperationsFiniteModules l E Y n) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    ((integralOperationsLevelPullback l E g n).obj M).val.map
        (proEtaleIsoCommaArrow g ((proEtaleBaseChange g).obj V)).op
      (integralOperationsPullbackGenerator l E g n M
        ((proEtaleIsoPostcompose g).obj ((proEtaleBaseChange g).obj V))
        (M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
          (inferInstance : WeaklyEtale g) trivial).counit.app V).op x)) =
      integralOperationsPullbackGenerator l E g n M V x := by
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let c := adj.counit.app V
  let N := (integralOperationsLevelPullback l E g n).obj M
  let η := (coefficientProEtaleModuleAdjunction.{u, u} g
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).unit.app M
  have hη := PresheafOfModules.naturality_apply η.val c.op x
  change integralOperationsPullbackGenerator l E g n M
      ((proEtaleIsoPostcompose g).obj ((proEtaleBaseChange g).obj V)) (M.val.map c.op x) =
    N.val.map ((proEtaleBaseChange g).map c).op
      (integralOperationsPullbackGenerator l E g n M V x) at hη
  rw [hη]
  have ht : ((proEtaleBaseChange g).map c).op ≫
      (proEtaleIsoCommaArrow g ((proEtaleBaseChange g).obj V)).op = 𝟙 _ := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (adj.right_triangle_components V)
  exact mapCompIdApply N.val.presheaf _ _ ht _

/-- The finite quotient augmentation agrees on each degree after the two comparisons.
Source: Stacks Tags 03D2 and 03EL; expanded clause 4 of the coefficient-twist definition.
(blueprint: lem-pur-isomorphism-ordinary-finite-augmentation).
Proof: test equality on an ordinary adjunction-unit section. The normalized module
comparison restricts it along the site counit. Naturality of the quotient augmentation
moves this restriction to the reduced section. The insertion formula and naturality
of the finite pullback unit then cancel the site unit and counit by the right triangle.
Both remaining sections are the finite pullback generator of the unit tensor. -/
theorem isomorphismOrdinaryFiniteAugmentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (b : ordinaryPull l E g ≅ inverseImageIntegralModules l E g)
    (hb :
    ∀ (M : integralTowerModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)),
      (b.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (((ordinaryAdjunction l E g).unit.app M).val.app (op V) x) =
      M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
        (inferInstance : WeaklyEtale g) trivial).counit.app V).op x)
    (P : Cx l E Y none) (n : ℕ)
    (a : (tower l E Y none).obj P ⋙ trfInverseImageComplex l E g ≅
      (integralOperationsPullbackTowerFunctor l E g).obj P)
    (ha : ∀ k : ℕ, a.hom.app (op k) = QuotientTensor.insertion l E g k
      ((unrestrictedIntegralFiniteComplex l E Y k).obj P)) (i : ℤ) :
    b.hom.app (P.X i) ≫ (inverseImageIntegralModules l E g).map
        ((((augmentation l E Y none).app P).app (op n)).f i) ≫
          (a.hom.app (op n)).f i =
      (((ordinaryQuotientAugmentation l E g).app P).app (op n)).f i := by
  apply ((ordinaryAdjunction l E g).homEquiv _ _).injective
  dsimp only [Adjunction.homEquiv, Equiv.coe_fn_mk]
  ext V x
  dsimp only [ordinaryPush]
  change (((a).hom.app (op n)).f i).val.app
      (op ((proEtaleBaseChange g).obj V.unop))
      (((((augmentation l E Y none).app P).app (op n)).f i).val.app
        (op ((proEtaleIsoPostcompose g).obj ((proEtaleBaseChange g).obj V.unop)))
        (((b).hom.app (P.X i)).val.app
          (op ((proEtaleBaseChange g).obj V.unop))
          (((ordinaryAdjunction l E g).unit.app (P.X i)).val.app V x))) = _
  erw [hb, ha]
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let c := adj.counit.app V.unop
  let r := (((augmentation l E Y none).app P).app (op n)).f i
  have hr := PresheafOfModules.naturality_apply r.val c.op x
  erw [hr]
  have hins := (QuotientTensor.insertion_existsUnique l E g n
    ((unrestrictedIntegralFiniteComplex l E Y n).obj P)).exists.choose_spec i
  erw [hins]
  simp only [QuotientTensor.tensorSection, one_smul]
  let M := ((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i
  erw [finitePullbackGenerator_counit l E g n M V.unop (r.val.app V x)]
  have haug := (augmentation_existsUnique l E Y none).exists.choose_spec P n i V x
  have hord := (ordinaryQuotientAugmentation_existsUnique l E g).exists.choose_spec
    P n i V.unop x
  exact (congrArg (integralOperationsPullbackGenerator l E g n M V.unop) haug).trans hord.symm

end WeilConjectures.IntegralOnSlice
