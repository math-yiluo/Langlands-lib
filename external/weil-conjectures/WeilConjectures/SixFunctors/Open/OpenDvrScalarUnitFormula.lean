/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Open.OpenQuotientKoszulModels
public import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels

/-! # Total-limit normalization of the ordinary scalar augmentation

Source: Stacks Tags 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-scalar-unit-formula).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.rightDerivedFunctor

local instance (priority := 10000) scalarUnitSequenceSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × T.ProEt) :=
  coefficientSequenceEssentiallySmall.{u, 0} T

/-- The ordinary constant/limit adjunct of the quotient-system unit, on complexes.
Source: Stacks Tag 07A6
(blueprint: lem-sf-open-dvr-scalar-unit-formula). -/
def openScalarComplexAugmentation (T : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E T)
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ) :
    ((Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _).mapHomologicalComplex
      (.up ℤ)).obj Q ⟶
    (CompletionUnit.tower l E T).obj ((M.quotient l E T).obj Q) :=
  ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
    lim).mapHomologicalComplex (.up ℤ)).homEquiv Q _ |>.symm
      (((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (CompletionUnit.ordinaryLimit l E T)) (.up ℤ)).inv.app
            ((M.quotient l E T).obj Q))

/-- Canonical right-derived limit comparison, with the localization factors retained. -/
private theorem openDvrCanonicalLimitFormula (T : Scheme.{u})
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ) :
    DerivedCategory.Q.map
        ((CompletionUnit.termwiseLimitComparison.{u, u} l E T).hom.app Z) ≫
      (CompletionUnit.constantLimitUnit.{u, u} l E T).app Z =
        derivedLimitComplexComparison
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
          (coefficientConstantTowerLimit.{u, u} l E T)
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit Z := by
  let R :=
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctor
  let γ := CompletionUnit.termwiseLimitComparison.{u, u} l E T
  let ηL : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R :=
    CompletionUnit.constantLimitUnit.{u, u} l E T
  change DerivedCategory.Q.map (γ.hom.app Z) ≫ ηL.app Z =
    derivedLimitComplexComparison
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _) R
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit Z
  dsimp only [ηL, γ, CompletionUnit.constantLimitUnit, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp_assoc,
    Iso.hom_inv_id_app, Category.id_comp]
  have hidL := (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E T)).map_id
    (((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
      (.up ℤ)).obj Z)
  rw [hidL]
  change 𝟙 _ ≫ derivedLimitComplexComparison
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _) R
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit Z = _
  exact Category.id_comp _

/-- A normalized derived Hom formula gives the ordinary constant/limit adjunct.
Source: Stacks Tags 07A6, 0D6E and 0941
(blueprint: lem-sf-open-dvr-scalar-unit-formula).

Proof: expand the Hom equivalence as the adjunction unit followed by the right
adjoint on f, then compose with the exact restriction localization comparison.
Its inverse in systemLimitUnit cancels. Ordinary limit projections identify the
model's limitComparison with the composite-functor comparison followed by c.
The const/limit Hom equivalence takes the explicitly defined augmentation back
to the ordinary model's unit. Finally hη cancels the termwise comparison in the
total derived limit. These are equalities of total derived-limit maps; finite
projections are used only for the ordinary limit identity. -/
theorem openDvrScalarUnitFormula (T : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E T)
    (M : CompletionUnit.OrdinaryModel l E T)
    (Q : CochainComplex (scalarReductionSource.{u, u} l E T) ℤ)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
      (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ)
      (n : ℕ) (i : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f i = limit.π (Z.X i) (op n))
    (η : roosLimitFunctor ⋙
        (DerivedCategory.Q (C := scalarReductionSource.{u, u} l E T)) ⟶
      (DerivedCategory.Q (C := ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T)) ⋙
        coefficientConstantTowerLimit.{u, u} l E T)
    (hη : ∀ Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ℤ,
      DerivedCategory.Q.map (c.hom.app Z) ≫ η.app Z =
        derivedLimitComplexComparison
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
          (coefficientConstantTowerLimit.{u, u} l E T)
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit Z)
    (f : S.reduction.obj (DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj ((M.quotient l E T).obj Q))
    (he : S.adjunction.homEquiv _ _ f =
      DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (CompletionUnit.systemLimitUnit l E T M
          η).app ((M.quotient l E T).obj Q)) :
    S.adjunction.unit.app (DerivedCategory.Q.obj Q) ≫
        (coefficientConstantTowerLimit.{u, u} l E T).map
          ((coefficientSequenceDerivedRestriction.{u, u} l E T).map f ≫
            (Functor.mapDerivedCategoryFactors
              (coefficientSequenceRestriction.{u, u} l E T)).hom.app
                ((M.quotient l E T).obj Q)) =
      DerivedCategory.Q.map
        (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
          lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
            ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
              (.up ℤ)).map (openScalarComplexAugmentation l E T M Q)) ≫
        derivedLimitComplexComparison
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _)
          (coefficientConstantTowerLimit.{u, u} l E T)
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit
          ((CompletionUnit.tower l E T).obj ((M.quotient l E T).obj Q)) := by
  let I := (M.quotient l E T).obj Q
  let B := (CompletionUnit.tower l E T).obj I
  let a := openScalarComplexAugmentation l E T M Q
  let U := coefficientSequenceRestriction.{u, u} l E T
  let := coefficientSequenceHasDerived.{u, u} l E T
  let := coefficientConstantTowerDerived.{u, u} l E T
  let : U.Additive := coefficientSequenceRestriction_additive.{u, u} l E T
  let : PreservesFiniteLimits U := coefficientSequenceRestriction_limits.{u, u} l E T
  let : PreservesFiniteColimits U := coefficientSequenceRestriction_colimits.{u, u} l E T
  let R :=
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctor
  let sunit : DerivedCategory.Q.obj Q ⟶
      R.obj ((coefficientSequenceDerivedRestriction.{u, u} l E T).obj
        (S.reduction.obj (DerivedCategory.Q.obj Q))) :=
    S.adjunction.unit.app (DerivedCategory.Q.obj Q)
  let rhs := DerivedCategory.Q.map
    (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
      lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
          (.up ℤ)).map a) ≫
    derivedLimitComplexComparison
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _) R
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B
  change sunit ≫ R.map (U.mapDerivedCategory.map f ≫
    U.mapDerivedCategoryFactors.hom.app I) = rhs
  let δ := Functor.mapHomologicalComplexCompIso
    (Iso.refl (CompletionUnit.ordinaryLimit l E T)) (.up ℤ)
  let γ := c
  let ηL : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R :=
    η
  have hu : S.adjunction.homEquiv _ (DerivedCategory.Q.obj I) f =
      DerivedCategory.Q.map ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (CompletionUnit.systemLimitUnit l E T M
          η).app I := he
  rw [S.adjunction.homEquiv_unit] at hu
  change sunit ≫ R.map (U.mapDerivedCategory.map f) = _ at hu
  have hu' := congrArg (fun f ↦ f ≫ R.map (U.mapDerivedCategoryFactors.hom.app I)) hu
  have hcancelR : R.map (U.mapDerivedCategoryFactors.inv.app I) ≫
      R.map (U.mapDerivedCategoryFactors.hom.app I) =
        𝟙 (R.obj (DerivedCategory.Q.obj B)) :=
    (R.mapIso (U.mapDerivedCategoryFactors.app I)).inv_hom_id
  have hs : sunit ≫ R.map (U.mapDerivedCategory.map f ≫ U.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map
        (((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
          M.limitComparison.hom.app I) ≫ ηL.app B := by
    simpa only [CompletionUnit.systemLimitUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Functor.comp_map,
      Category.assoc, hcancelR, Category.comp_id, coefficientConstantTowerLimit,
      R, U, ηL, B, Functor.comp_obj] using hu'
  have hd : δ.inv.app I ≫ γ.hom.app B = M.limitComparison.hom.app I := by
    apply limit.hom_ext
    intro n
    apply HomologicalComplex.hom_ext
    intro i
    rw [Category.assoc, HomologicalComplex.comp_f]
    erw [hc B n.unop i]
    change (𝟙 _ ≫ _) = _
    rw [Category.id_comp]
    exact (M.limitComparison_projection I n.unop i).symm
  have ha :
      ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
        lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
          (.up ℤ)).map a =
      ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫ δ.inv.app I := by
    change ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
      lim).mapHomologicalComplex (.up ℤ)).homEquiv Q B a = _
    exact ((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
      lim).mapHomologicalComplex (.up ℤ)).homEquiv Q B |>.apply_symm_apply _
  have hc' : DerivedCategory.Q.map (γ.hom.app B) ≫ ηL.app B =
      derivedLimitComplexComparison
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _) R
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B :=
    hη B
  have hf : sunit ≫ R.map (U.mapDerivedCategory.map f ≫ U.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map
        (((constLimAdj : (Functor.const ℕᵒᵖ : scalarReductionSource.{u, u} l E T ⥤ _) ⊣
          lim).mapHomologicalComplex (.up ℤ)).unit.app Q ≫
            ((lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).mapHomologicalComplex
              (.up ℤ)).map a) ≫
        derivedLimitComplexComparison
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _) R
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E T) ⥤ _).rightDerivedFunctorUnit B := by
    rw [hs, ← hd, ← Category.assoc, DerivedCategory.Q.map_comp, Category.assoc, hc', ← ha]
  exact hf

end WeilConjectures
