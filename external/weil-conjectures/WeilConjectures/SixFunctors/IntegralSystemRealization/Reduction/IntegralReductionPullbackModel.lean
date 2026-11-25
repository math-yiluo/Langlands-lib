/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.IntegralOrdinaryLimitModel
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Normalized reduction and geometric pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem cancellation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B H I : D} {M N : C} (a : A ⟶ B) (b : B ⟶ H) (c : H ⟶ I)
    (d : F.obj N ≅ I) (e : M ≅ N) :
    (a ≫ b ≫ c ≫ d.inv ≫ F.map e.inv) ≫ F.map e.hom ≫ d.hom = a ≫ b ≫ c := by
  simp only [Category.assoc, ← F.map_comp_assoc, e.inv_hom_id,
    F.map_id, Category.id_comp, d.inv_hom_id, Category.comp_id]

private theorem pull_good {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    integralOperationsGoodComplex l E X
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj) := by
  exact AlgebraicGeometry.ProEtale.VaryingRing.ringPull_preserves_flat f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f) P.obj P.property.1 P.property.2

private theorem realization_of_ordinary (o : Operations l E) (a : OrdinaryLimitModel l E) :
    Nonempty (RealizationModel l E o) := by
  let goodY := fun Y : Scheme.{u} ↦ integralOperationsGoodComplex l E Y
  have derived {X Y : Scheme.{u}} (f : X ⟶ Y) :
      ∃ r : PurCompactSupport.pull (PurCompactSupport.completed l E) f ⋙
          (calculus l E X).reduction ≅ (calculus l E Y).reduction ⋙ pull l E f,
        ∀ (P : (goodY Y).FullSubcategory)
          (h : integralOperationsGoodComplex l E X
            (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj)),
          r.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (pull l E f).map ((pullbackTensorReductionModel l E Y).hom.app P) ≫
            (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
              (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj
                P.obj) =
          (calculus l E X).reduction.map
            ((integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app P.obj) ≫
            (pullbackTensorReductionModel l E X).hom.app
              ⟨((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj, h⟩ ≫
            DerivedCategory.Q.map (a.reductionPullComplex l E f P.obj) := by
    let F := integralOrdinaryPull l E f
    let S := pullbackTensorSequenceInverse l E f
    let RY := pullbackTensorOrdinaryReduction l E Y
    let RX := pullbackTensorOrdinaryReduction l E X
    let G : (goodY Y).FullSubcategory ⥤ (goodY X).FullSubcategory :=
      ObjectProperty.lift (goodY X) ((goodY Y).ι ⋙ F.mapHomologicalComplex (.up ℤ))
        (fun P ↦ pull_good l E f P)
    let L := integralOperationsGoodLocalization l E Y
    let W := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
      (goodY Y).ι
    let : L.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E Y
    let ec : F.mapHomologicalComplex (.up ℤ) ⋙ RX.mapHomologicalComplex (.up ℤ) ≅
        RY.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
      NatIso.ofComponents (fun P ↦
        { hom := a.reductionPullComplex l E f P
          inv :=
            { f i := (a.reductionPull l E f).inv.app (P.X i)
              comm' i j _ := ((a.reductionPull l E f).inv.naturality (P.d i j)).symm }
          hom_inv_id := by
            apply HomologicalComplex.Hom.ext
            funext i
            exact (a.reductionPull l E f).hom_inv_id_app (P.X i)
          inv_hom_id := by
            apply HomologicalComplex.Hom.ext
            funext i
            exact (a.reductionPull l E f).inv_hom_id_app (P.X i) })
        (by
          intro P Q g
          apply HomologicalComplex.Hom.ext
          funext i
          exact (a.reductionPull l E f).hom.naturality (g.f i))
    let b : L ⋙ (F.mapDerivedCategory ⋙ (calculus l E X).reduction) ≅
        L ⋙ ((calculus l E Y).reduction ⋙ S.mapDerivedCategory) :=
      Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft (goodY Y).ι F.mapDerivedCategoryFactors)
            (calculus l E X).reduction ≪≫
        Functor.isoWhiskerLeft G (pullbackTensorReductionModel l E X) ≪≫
        Functor.isoWhiskerRight (Functor.isoWhiskerLeft (goodY Y).ι ec) DerivedCategory.Q ≪≫
        Functor.isoWhiskerLeft ((goodY Y).ι ⋙ RY.mapHomologicalComplex (.up ℤ))
          S.mapDerivedCategoryFactors.symm ≪≫
        Functor.isoWhiskerRight (pullbackTensorReductionModel l E Y).symm S.mapDerivedCategory
    let r := Localization.liftNatIso L W _ _
      (F.mapDerivedCategory ⋙ (calculus l E X).reduction)
      ((calculus l E Y).reduction ⋙ S.mapDerivedCategory) b
    refine ⟨r, ?_⟩
    intro P h
    have hr : r.hom.app (L.obj P) = b.hom.app P := by
      dsimp only [r, Localization.liftNatIso]
      simp only [Localization.liftNatTrans_app, Localization.Lifting.iso,
        Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]
    change r.hom.app (L.obj P) ≫ _ ≫ _ = _
    rw [hr]
    change (_ ≫ _ ≫ _ ≫ S.mapDerivedCategoryFactors.inv.app _ ≫
      S.mapDerivedCategory.map ((pullbackTensorReductionModel l E Y).inv.app P)) ≫
        S.mapDerivedCategory.map ((pullbackTensorReductionModel l E Y).hom.app P) ≫
          S.mapDerivedCategoryFactors.hom.app _ = _
    exact cancellation S.mapDerivedCategory _ _ _
      (S.mapDerivedCategoryFactors.app _)
      ((pullbackTensorReductionModel l E Y).app P)
  choose r hr using @derived
  exact ⟨⟨a, @r, @hr⟩⟩

/-- The ordinary sectionwise limit comparison descends to coherent derived reduction.
Source: Stacks 03D7, 07A6, 07A7 and 0941; primitive realization Step 3
(blueprint: lem-sf-integral-reduction-pullback-model).

Proof: commute geometric direct image with the ordinary limit of restricted modules.
The comparison is identity on the compatible families of sections, and its projections
are precisely the finite direct-image comparisons. Take its ordinary left-adjoint
conjugate. On flat-term K-flat representatives it commutes with quotient reduction.
The adjunction-normalized reduction models identify this cochain comparison with the
specified derived reductions. Localize the good representatives, using their functorial
K-flat resolutions. Full faithfulness of restriction along that localization gives a
natural derived isomorphism and its displayed whole-system representative equation.
No faithfulness of finite derived evaluation is used. -/
theorem integralReductionPullbackModel (o : Operations l E) :
    Nonempty (RealizationModel l E o) := by
  obtain ⟨a⟩ := integralOrdinaryLimitModel l E
  exact realization_of_ordinary l E o a

end WeilConjectures.IntegralSystemRealization
