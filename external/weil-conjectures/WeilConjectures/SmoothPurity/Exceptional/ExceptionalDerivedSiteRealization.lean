/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalSiteRealization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
/-! # Derived realization of the actual etale/pro-etale system comparison
Source: blueprint theorem-f-shriek-finite-coefficients. All ordinary maps are fixed on
sections or by adjunction transposes; their derived maps retain the localization units.
(blueprint: def-pur-adic-derived-site-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
  AlgebraicGeometry SheafOfModules
namespace WeilConjectures

-- Since build 2026-10-28 another derived-category instance of the strict levels is in scope here;
-- keep the ones this module was written against.
attribute [local instance 5000] AlgebraicGeometry.strictEtaleSystemDerived
  AlgebraicGeometry.strictEtaleLevelDerived
private theorem localizationSquare
    {C D T : Type*} [Category C] [Category D] [Category T]
    (L : C ⥤ D) (S : MorphismProperty C) [L.IsLocalization S]
    (F G : D ⥤ T) (H K : C ⥤ T)
    (φ : L ⋙ F ≅ H) (ψ : L ⋙ G ≅ K) (α : H ≅ K) :
    ∃! δ : F ≅ G, ∀ X,
      δ.hom.app (L.obj X) ≫ ψ.hom.app X = φ.hom.app X ≫ α.hom.app X := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L S T
  let τ := φ ≪≫ α ≪≫ ψ.symm
  let δ := ff.preimageIso τ
  have hd X : δ.hom.app (L.obj X) = τ.hom.app X :=
    congr_app (ff.map_preimage τ.hom) X
  refine ⟨δ, ?_, ?_⟩
  · intro X
    rw [hd]
    simp [τ]
  · intro δ' hδ'
    apply Iso.ext
    apply Localization.natTrans_ext L S
    intro X
    apply (cancel_mono (ψ.hom.app X)).1
    rw [hd]
    simpa [τ] using hδ' X

section ExactSquare
universe a av aw b bv bw c cv cw d dv dw
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{aw} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{bw} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{cw} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dw} D]

private theorem exactSquare
    (F : A ⥤ B) (G : A ⥤ C) (H : B ⥤ D) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory A ⥤ DerivedCategory C)
    (HD : DerivedCategory B ⥤ DerivedCategory D)
    (ID : DerivedCategory C ⥤ DerivedCategory D)
    (φG : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φH : DerivedCategory.Q ⋙ HD ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φI : DerivedCategory.Q ⋙ ID ≅ I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α : F ⋙ H ≅ G ⋙ I) :
    ∃! δ : FD ⋙ HD ≅ GD ⋙ ID,
      ∀ J, δ.hom.app (DerivedCategory.Q.obj J) ≫
        ID.map (φG.hom.app J) ≫
        φI.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) =
      HD.map (φF.hom.app J) ≫
        φH.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app J) := by
  let φ : DerivedCategory.Q ⋙ (FD ⋙ HD) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φF _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φH
  let ψ : DerivedCategory.Q ⋙ (GD ⋙ ID) ≅
      G.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight φG _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ φI
  let β := isoWhiskerRight (Functor.mapHomologicalComplexCompIso α (.up ℤ))
    DerivedCategory.Q
  obtain ⟨δ, hδ, hu⟩ := localizationSquare DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ _ _ φ ψ β
  -- The universal unit equation is the required square after cancelling factorizations.
  have hiff (e : FD ⋙ HD ≅ GD ⋙ ID) :
      (∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫
        ID.map (φG.hom.app J) ≫
        φI.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) =
      HD.map (φF.hom.app J) ≫
        φH.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app J)) ↔
      (∀ J, e.hom.app (DerivedCategory.Q.obj J) ≫ ψ.hom.app J =
        φ.hom.app J ≫ β.hom.app J) := by
    dsimp only [φ, ψ, β, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.assoc]
    rfl
  exact ⟨δ, (hiff δ).mpr hδ, fun e he ↦ hu e ((hiff e).mp he)⟩
end ExactSquare

section CochainRightUnit
universe a av aw b bv bw
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{aw} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{bw} B]
  [Abelian.HasKInjectiveResolutions A]

private def cochainRightUnit (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app J :=
    (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj J) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app J)
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

private theorem cochainRightUnit_computes (F : A ⥤ B) [F.Additive]
    (J : CochainComplex A ℤ) (hJ : J.IsKInjective) :
    IsIso ((cochainRightUnit F).app J) := by
  change IsIso (F.rightDerivedFunctorUnitQ J)
  rw [F.rightDerivedFunctorUnitQ_eq]
  infer_instance
end CochainRightUnit

section RightSquare
universe a av aw b bv bw c cv cw d dv dw
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{aw} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{bw} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{cw} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dw} D]
  [Abelian.HasKInjectiveResolutions A]

private theorem rightSquare
    (F : A ⥤ B) (G : A ⥤ C) (H : B ⥤ D) (I : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [G.PreservesKInjectiveComplexes]
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory A ⥤ DerivedCategory C)
    (HD : DerivedCategory B ⥤ DerivedCategory D)
    (ID : DerivedCategory C ⥤ DerivedCategory D)
    (ηF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ FD)
    (hF : ∀ J : CochainComplex A ℤ, J.IsKInjective → IsIso (ηF.app J))
    (ηI : I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ ID)
    (hI : ∀ J : CochainComplex C ℤ, J.IsKInjective → IsIso (ηI.app J))
    (φG : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (φH : DerivedCategory.Q ⋙ HD ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α : F ⋙ H ≅ G ⋙ I) :
    ∃! δ : FD ⋙ HD ≅ GD ⋙ ID,
      ∀ J, HD.map (ηF.app J) ≫ δ.hom.app (DerivedCategory.Q.obj J) ≫
        ID.map (φG.hom.app J) =
      φH.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app J) ≫
        ηI.app ((G.mapHomologicalComplex (.up ℤ)).obj J) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let Ic := I.mapHomologicalComplex (.up ℤ)
  let β : Fc ⋙ Hc ≅ Gc ⋙ Ic := Functor.mapHomologicalComplexCompIso α (.up ℤ)
  -- Compare units with the same source, so right-derived uniqueness fixes the map.
  let η : Fc ⋙ Hc ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (FD ⋙ HD) :=
    whiskerLeft Fc φH.inv ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight ηF HD ≫ (Functor.associator _ _ _).hom
  let θ : Fc ⋙ Hc ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (GD ⋙ ID) :=
    (Functor.associator _ _ _).inv ≫ whiskerRight β.hom DerivedCategory.Q ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft Gc ηI ≫
      (Functor.associator _ _ _).inv ≫ whiskerRight φG.inv ID ≫
      (Functor.associator _ _ _).hom
  have hη : (FD ⋙ HD).IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (CochainComplex.KInjectives.localizerMorphism A)
      |>.isRightDerivedFunctor_of_isRightDerivabilityStructure η
    intro J
    have := hF J.obj J.property
    dsimp only [η, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    change IsIso (φH.inv.app (Fc.obj J.obj) ≫ HD.map (ηF.app J.obj))
    infer_instance
  have hθ : (GD ⋙ ID).IsRightDerivedFunctor θ
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (CochainComplex.KInjectives.localizerMorphism A)
      |>.isRightDerivedFunctor_of_isRightDerivabilityStructure θ
    intro J
    have : J.obj.IsKInjective := J.property
    have := hI (Gc.obj J.obj) inferInstance
    dsimp only [θ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id]
    change IsIso (DerivedCategory.Q.map (β.hom.app J.obj) ≫
      ηI.app (Gc.obj J.obj) ≫ ID.map (φG.inv.app J.obj))
    infer_instance
  let δ := Functor.rightDerivedUnique (FD ⋙ HD) (GD ⋙ ID) η θ
    (HomologicalComplex.quasiIso A (.up ℤ))
  -- The universal unit equation is the required square after cancelling factorizations.
  have hiff (e : FD ⋙ HD ≅ GD ⋙ ID) :
      (∀ J, HD.map (ηF.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
        ID.map (φG.hom.app J) =
      φH.hom.app (Fc.obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app J) ≫
        ηI.app (Gc.obj J)) ↔
      (η ≫ whiskerLeft DerivedCategory.Q e.hom = θ) := by
    constructor
    · intro he
      ext J
      dsimp only [η, θ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      apply (cancel_mono (ID.map (φG.hom.app J))).1
      simp only [Category.assoc, ← ID.map_comp, Iso.inv_hom_id_app, ID.map_id]
      erw [Category.comp_id]
      rw [he J]
      simp only [Iso.inv_hom_id_app_assoc]
      rfl
    · intro he J
      have hj := congr_app he J
      dsimp only [η, θ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.associator_hom_app, Functor.associator_inv_app] at hj
      simp only [Category.id_comp, Category.comp_id, Category.assoc] at hj
      have hj' := congrArg (fun f ↦ φH.hom.app (Fc.obj J) ≫ f ≫
        ID.map (φG.hom.app J)) hj
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← ID.map_comp,
        Iso.inv_hom_id_app, ID.map_id] at hj'
      erw [Category.comp_id] at hj'
      exact hj'
  refine ⟨δ, (hiff δ).mpr ?_, ?_⟩
  · simp [δ]
  · intro e he
    apply Iso.ext
    apply Functor.rightDerived_ext (FD ⋙ HD) η
      (HomologicalComplex.quasiIso A (.up ℤ))
    exact ((hiff e).mp he).trans (by simp [δ])
end RightSquare

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  (P : StrictEtaleEvaluation W (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E))
  (B : IntegralExceptionalComparison l E W P)

/-- The complete inverse realization normalization on all cochain complexes.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def IsIntegralExceptionalSiteDerivedInverse (n : ℕ)
    (e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory) :
            Prop :=
      ∀ J : CochainComplex (strictEtaleLevel W (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory.map
              ((integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors.hom.app
                 J) ≫
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              W).mapDerivedCategoryFactors.hom.app
                (((integralExceptionalEtaleRealization l E W n).mapHomologicalComplex
                   (.up ℤ)).obj J) =
        (integralExceptionalProRealization l E W n).mapDerivedCategory.map
          ((B.derived.level n).inverseFactors.hom.app J) ≫
        (integralExceptionalProRealization l E W n).mapDerivedCategoryFactors.hom.app
          ((((B.ordinary.lift n).modules).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalSiteInverse l E W P B n).hom (.up ℤ)).app J)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The exact derived site inverse comparison, fixed on every cochain representative.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization).
Proof: apply exact localization to the preceding ordinary inverse comparison and
compose the two specified factorization isomorphisms. Their square is the displayed
condition. Every derived arrow is represented by a roof, proving uniqueness. -/
theorem integralExceptionalSiteDerivedInverse_existsUnique (n : ℕ) :
    ∃! e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory,
      IsIntegralExceptionalSiteDerivedInverse l E W P B n e := by
  exact exactSquare (B.ordinary.lift n).modules
    (integralExceptionalEtaleRealization l E W n)
    (integralExceptionalProRealization l E W n)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).inverse
    (integralExceptionalEtaleRealization l E W n).mapDerivedCategory
    (integralExceptionalProRealization l E W n).mapDerivedCategory
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory
    (integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors
    (integralExceptionalProRealization l E W n).mapDerivedCategoryFactors
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategoryFactors
    (B.derived.level n).inverseFactors
    (integralExceptionalSiteInverse l E W P B n)

/-- The exact inverse comparison, fixed by its universal representative square.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
@[no_expose] def integralExceptionalSiteDerivedInverse (n : ℕ) :
    (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory :=
  (integralExceptionalSiteDerivedInverse_existsUnique l E W P B n).choose

/-- The actual cochain-level unit of derived site direct image.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
def integralExceptionalSiteFixedRightUnit (n : ℕ)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    DerivedCategory.Q.obj
      (((ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapHomologicalComplex
           (.up ℤ)).obj J) ⟶
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.obj
         (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctorUnit.app
         ((HomotopyCategory.quotient _ _).obj J) ≫
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.map
         ((DerivedCategory.quotientCompQhIso _).hom.app J)

/-- The complete right realization normalization on all cochain complexes.
Source: blueprint integral exceptional image
(blueprint: def-pur-adic-derived-site-realization). -/
def IsIntegralExceptionalSiteDerivedRight (n : ℕ)
    (e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor) :
            Prop :=
      ∀ J : CochainComplex (coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) ℤ,
        (integralExceptionalEtaleRealization l E W n).mapDerivedCategory.map
          ((B.derived.level n).directUnit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.map
          ((integralExceptionalProRealization l E W n).mapDerivedCategoryFactors.hom.app J) =
        (integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors.hom.app
          (((B.ordinary.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalSiteRight l E W P B n).hom (.up ℤ)).app J) ≫
        integralExceptionalSiteFixedRightUnit l E W n
          (((integralExceptionalProRealization l E W n).mapHomologicalComplex
             (.up ℤ)).obj J)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived site direct comparison is fixed by both universal right-derived units.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization).
Proof: on K-injective representatives both derived units are invertible and the
ordinary section comparison determines the map. Exact realization is an equivalence,
so it preserves K-injective representatives. Universal right derivation extends this
map uniquely and gives the displayed square on all complexes. -/
theorem integralExceptionalSiteDerivedRight_existsUnique (n : ℕ) :
    ∃! e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor,
      IsIntegralExceptionalSiteDerivedRight l E W P B n e := by
  let F := B.ordinary.right n
  let G := integralExceptionalProRealization l E W n
  let H := integralExceptionalEtaleRealization l E W n
  let I := ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W
  let : IsGrothendieckAbelian.{u + 1}
      (coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) :=
    IsGrothendieckAbelian.of_equivalence G.asEquivalence.symm
  exact rightSquare F G H I (B.derived.level n).direct G.mapDerivedCategory
    H.mapDerivedCategory I.rightDerivedFunctor
    (B.derived.level n).directUnit (B.derived.level n).computes
    (cochainRightUnit I) (cochainRightUnit_computes I)
    G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors
    (integralExceptionalSiteRight l E W P B n)

/-- The universal-unit-normalized derived site direct comparison.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-derived-site-realization). -/
@[no_expose] def integralExceptionalSiteDerivedRight (n : ℕ) :
    (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor :=
  (integralExceptionalSiteDerivedRight_existsUnique l E W P B n).choose
end WeilConjectures
