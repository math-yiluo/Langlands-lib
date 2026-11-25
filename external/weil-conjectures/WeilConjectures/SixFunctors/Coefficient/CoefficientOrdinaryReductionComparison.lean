/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryQuotientModel
import WeilConjectures.Algebra.Homology.RestrictedTowerResolution.RestrictedTowerResolutionAcyclicity
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Derived comparison for the ordinary quotient-system adjunction

Source: Stacks 06YY, 07A6, 09T5, 0941 and 0D6E.

The ordinary quotient-system adjunction of `OrdinaryQuotient.OrdinaryModel` is derived
on flat-term K-flat complexes and K-injective systems. Its derived left functor is left
adjoint to `coefficientSequenceLimit`. For every left adjoint of
`coefficientSequenceLimit` this gives the universal left-derived comparison with the
strict quotient systems, normalized by the derived Hom formula, and its finite values.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.OrdinaryQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-! ### Limit acyclicity of restricted K-injective systems -/

private abbrev limitComplex :=
  (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
    scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)

-- The coefficient-site identifications below follow the private construction in
-- WeilConjectures.SmoothPurity.SequenceKInjectiveComparison.SequenceKInjectiveComparisonShifts,
-- specialized to the present tower.
private def coefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l E W :=
  NatTrans.ofOpSequence (fun n ↦ completedIntegralCommRingProjectionUnrestricted l E W n)
    (by
      intro n
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map,
        coefficientSequenceCommRingSystem, Functor.ofOpSequence_obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp]
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      apply (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).map_injective
      change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app V =
        (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app V ≫
          (integralCoefficientSheafTransition l E W n).hom.app V
      have h := congrArg (fun k ↦ k.hom.app V)
        (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)

private abbrev strictEquivalence :=
  (SheafOfModules.strictSystemSequenceEquivalence (coefficientSequenceCommRingSystem l E W)).symm

private instance strictEquivalence_additive :
    (strictEquivalence l E W).functor.Additive where
  map_add := by
    intro M N f g
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    have h := (SheafOfModules.systemEvaluation
      (coefficientSequenceCommRingSystem l E W) n).map_add
        (f := (strictEquivalence l E W).functor.map f)
        (g := (strictEquivalence l E W).functor.map g)
    refine Eq.trans ?_ h.symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    rfl

private theorem restriction_as_strict :
    (strictEquivalence l E W).functor ⋙
      SheafOfModules.RestrictedTowerResolution.restrictionFunctor
        (completedIntegralCommRingSheafUnrestricted l E W)
        (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W) =
      coefficientSequenceRestriction l E W := by
  unfold coefficientSequenceRestriction
  apply (coefficientSequenceRestriction_exists l E W).unique ?_
    (coefficientSequenceRestriction_exists l E W).exists.choose_spec
  refine ⟨?_, ?_, ?_⟩
  · intro M n
    have hφ : SheafOfModules.systemSequenceVerticalRingMap
        (coefficientSequenceCommRingSystem l E W) n =
        eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl
    change (scalarReductionRestriction l E W n).obj
        ((SheafOfModules.pushforward
          (SheafOfModules.systemSequenceVerticalRingMap
            (coefficientSequenceCommRingSystem l E W) n)).obj M) = _
    rw [hφ]
    rfl
  · intro M m n h V
    rfl
  · intro M N f n V
    rfl

/-- Restriction of a K-injective coefficient system is acyclic for inverse limit.
Only its limit-acyclicity is asserted, not its K-injectivity.

Source: Stacks sites-cohomology.tex, lemma-derived-pushforward-composition (0D6E),
lemma-derived-limit-is-ok (0941), and the restriction-acyclicity part of step 1 of
lem-trf-completion-unit-derived-adjunction-comparison.
(blueprint: lem-trf-completion-unit-restriction-acyclicity).

Proof: Identify modules on the coefficient sequence site with strict semilinear
systems using the vertical-slice equivalence. This exact equivalence preserves
K-injectivity. Under it the specified coefficientSequenceRestriction is the
strict-system scalar-restriction tower: its objects, horizontal maps and maps of
systems agree by the three characterizing equations of its unique construction.
Apply lem-coef-restricted-tower-resolution-acyclicity to the identity resolution of
I and the given K-injective tower resolution j. Its first conclusion states exactly
that ordinary inverse limit sends j to a quasi-isomorphism. Transport this conclusion
through the natural isomorphism of restricted towers and their degreewise limits.
Equivalently factor the sequence projection through the constant ring sequence and
apply normalized derived pushforward composition. Exact restriction alone is not
used to claim that it preserves K-injectives. This works for the empty site and zero
complexes and uses neither boundedness nor any flatness of finite quotient rings. -/
theorem restricted_limit_acyclic
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (j : (tower l E W).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j) := by
  let F := (strictEquivalence l E W).functor
  let U := SheafOfModules.RestrictedTowerResolution.restrictionFunctor
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W)
  have hU : F ⋙ U = coefficientSequenceRestriction l E W := restriction_as_strict l E W
  let I' := (F.mapHomologicalComplex (.up ℤ)).obj I
  have : CochainComplex.IsKInjective I' := inferInstance
  let : (coefficientSequenceRestriction l E W).Additive :=
    coefficientSequenceRestriction_additive l E W
  let e : (U.mapHomologicalComplex (.up ℤ)).obj I' ≅ (tower l E W).obj I :=
    (NatIso.mapHomologicalComplex (F := F ⋙ U)
      (G := coefficientSequenceRestriction l E W) (eqToIso hU) (.up ℤ)).app I
  have := (SheafOfModules.RestrictedTowerResolution.acyclicity
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l E W) (coefficientCone l E W)
    (𝟙 I') (e.hom ≫ j)).1
  have hc : QuasiIso ((limitComplex l E W).map e.hom ≫
      (limitComplex l E W).map j) := by
    simpa only [limitComplex, Functor.map_comp] using this
  exact (quasiIso_iff_comp_left
    ((limitComplex l E W).map e.hom) ((limitComplex l E W).map j)).mp hc

/-! ### The constant-tower limit unit -/

/-- The canonical right-derived unit of the constant-tower inverse limit, in the
termwise-limit coordinates. Source: Stacks 0941, 07A6. -/
def constantLimitUnit :
    roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W := by
  let A := ℕᵒᵖ ⥤ scalarReductionSource l E W
  let B := scalarReductionSource l E W
  let F : A ⥤ B := lim
  let π := HomotopyCategory.quotient A (.up ℤ)
  let e : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      π ⋙ (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  exact (Functor.isoWhiskerRight (termwiseLimitComparison l E W).symm
      DerivedCategory.Q).hom ≫ e.hom ≫
    Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom

/-- The constant-tower limit unit is the inverse termwise comparison on K-injectives.
Source: Stacks 0941. -/
theorem constantLimitUnit_normalization
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective] :
    (constantLimitUnit l E W).app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
      DerivedCategory.Q.map ((termwiseLimitComparison l E W).inv.app J) := by
  dsimp only [coefficientConstantTowerLimit]
  have hqA : (DerivedCategory.quotientCompQhIso
      (ℕᵒᵖ ⥤ scalarReductionSource l E W)).hom.app J = 𝟙 _ := rfl
  have hqiB (K : CochainComplex (scalarReductionSource l E W) ℤ) :
      (DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app K =
        𝟙 _ := rfl
  have hf : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomotopyCategoryFactors (.up ℤ)).inv.app J =
        𝟙 _ := rfl
  dsimp only [constantLimitUnit, Functor.rightDerivedFunctorObjQIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, asIso_inv, Iso.app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [hqA, hqiB, hf]
  simp only [Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    IsIso.hom_inv_id_assoc, Category.comp_id]

/-- The constant-tower limit unit exhibits the right derived inverse limit.
Source: Stacks 0941, 07A6. -/
theorem constantLimitUnit_isRightDerived :
    (coefficientConstantTowerLimit l E W).IsRightDerivedFunctor
      (constantLimitUnit l E W)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ scalarReductionSource l E W) (.up ℤ)) := by
  let A := ℕᵒᵖ ⥤ scalarReductionSource l E W
  let F : A ⥤ scalarReductionSource l E W := lim
  let e := Functor.isoWhiskerRight (termwiseLimitComparison l E W) DerivedCategory.Q
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (roosLimitFunctor ⋙ DerivedCategory.Q) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerLeft (CochainComplex.KInjectives.localizerMorphism A).functor e)).mp
        (CategoryTheory.derives F)
  apply h.isRightDerivedFunctor_of_isIso (constantLimitUnit l E W)
  intro I
  have : I.obj.IsKInjective := I.property
  have hn := constantLimitUnit_normalization l E W I.obj
  have : IsIso ((constantLimitUnit l E W).app I.obj ≫
      (F.rightDerivedFunctorObjQIso I.obj).hom) := by
    rw [hn]
    infer_instance
  change IsIso ((constantLimitUnit l E W).app I.obj)
  exact IsIso.of_isIso_comp_right ((constantLimitUnit l E W).app I.obj)
    (F.rightDerivedFunctorObjQIso I.obj).hom

/-! ### The system limit unit -/


/-- The actual composite unit for exact scalar restriction followed by total limit.
Source: Stacks 0D6E
(blueprint: lem-trf-completion-unit-derived-adjunction-comparison). -/
def systemLimitUnit (M : OrdinaryModel l E W)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W) :
    (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit l E W :=
  Functor.whiskerRight M.limitComparison.hom DerivedCategory.Q ≫
    Functor.whiskerLeft (tower l E W) η ≫
    Functor.whiskerRight
      (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv
      (coefficientConstantTowerLimit l E W)

private instance systemKInjectives :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E W) := by
  have : LocallySmall.{max u (t + 1)} W.ProEt := locallySmall_max.{max u (t + 1), t, t + 1}
  let : IsGrothendieckAbelian.{max u (t + 1)} (coefficientSequenceModules l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).1
  infer_instance

/-- The system limit unit is invertible on K-injective systems. Source: Stacks 0D6E. -/
theorem systemLimitUnit_isIso
    (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) (hI : I.IsKInjective) :
    IsIso ((systemLimitUnit l E W M η).app I) := by
  let : I.IsKInjective := hI
  let K := (tower l E W).obj I
  obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  let : J.IsKInjective := hJ
  let : QuasiIso j := hj
  have : QuasiIso (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j) :=
    restricted_limit_acyclic l E W I J j
  have : IsIso ((roosLimitFunctor ⋙ DerivedCategory.Q).map j) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight c DerivedCategory.Q) j).1
      (by
        change IsIso (DerivedCategory.Q.map
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).map j))
        infer_instance)
  have hJnorm := hηnorm J
  have : IsIso (η.app J ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom) := by
    rw [hJnorm]
    infer_instance
  have : IsIso (η.app J) := IsIso.of_isIso_comp_right _
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom
  have : IsIso (η.app K ≫ (coefficientConstantTowerLimit l E W).map
      (DerivedCategory.Q.map j)) := by
    change IsIso (η.app K ≫ (DerivedCategory.Q ⋙
      coefficientConstantTowerLimit l E W).map j)
    rw [← η.naturality j]
    infer_instance
  have : IsIso (η.app K) := IsIso.of_isIso_comp_right _
    ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map j))
  dsimp only [systemLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- The derived system evaluations jointly detect isomorphisms. Source: Stacks 0941. -/
theorem coefficientSequence_isIso_iff_evaluations
    {M N : coefficientSequenceDerived l E W} (f : M ⟶ N) :
    IsIso f ↔ ∀ n : ℕ,
      IsIso ((coefficientSequenceDerivedEvaluation l E W n).map f) := by
  constructor
  · intro hf n
    have : IsIso f := hf
    infer_instance
  · intro hf
    obtain ⟨D⟩ := SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W)
    exact D.systems.detects f hf

private theorem tensor_inverts (M : OrdinaryModel l E W)
    {Q Q' : CochainComplex (scalarReductionSource l E W) ℤ} (f : Q ⟶ Q')
    (hQ : Q.IsKFlatIndependentCoefficients) (hQ' : Q'.IsKFlatIndependentCoefficients)
    (hf : QuasiIso f) :
    IsIso (DerivedCategory.Q.map ((M.quotient l E W).map f)) := by
  apply (coefficientSequence_isIso_iff_evaluations l E W _).2
  intro n
  have hpres :=
    (scalarReductionExistence l E W n).choose_spec.choose_spec.choose_spec.choose_spec.1
      f hQ hQ' hf
  let : QuasiIso (((scalarReductionExtension l E W n).mapHomologicalComplex
    (.up ℤ)).map f) := hpres
  let e := Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)) DerivedCategory.Q
  have he := NatIso.isIso_map_iff e f
  have : IsIso (((M.quotient l E W ⋙
      (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q).map f) := he.2
    (by
      change IsIso (DerivedCategory.Q.map
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map f))
      infer_instance)
  exact (NatIso.isIso_map_iff
    (Functor.isoWhiskerLeft (M.quotient l E W)
      (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors) f).2 this

/-- Every complex of completed-coefficient modules has a flat-term K-flat resolution.
Source: Stacks 06YF, 0FND. -/
theorem exists_flatTermKFlatResolution (X : CochainComplex (scalarReductionSource l E W) ℤ) :
    ∃ (Q : CochainComplex (scalarReductionSource l E W) ℤ) (q : Q ⟶ X),
      (Q.IsKFlatIndependentCoefficients ∧ ∀ p : ℤ, (Q.X p).IsFlatOnSite) ∧
        QuasiIso q := by
  obtain ⟨Q, q, hQ, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) X
  refine ⟨Q, q, ⟨hQ, fun p ↦ ?_⟩, hq⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso
      (completedIntegralCommRingSheafUnrestricted l E W) (Q.X p)).symm (hflat p)

private theorem tensor_derived_exists (M : OrdinaryModel l E W)
    (δ : (ordinaryLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit l E W)
    (hδ : (coefficientSequenceLimit l E W).IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))) :
    ∃ (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
      (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
      (a : L ⊣ coefficientSequenceLimit l E W),
      L.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) ∧
      (∀ Q : CochainComplex (scalarReductionSource l E W) ℤ,
        Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
          IsIso (ε.app Q)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (f : (M.quotient l E W).obj Q ⟶ I),
        a.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
          ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫ δ.app I) := by
  classical
  let A := scalarReductionSource l E W
  let B := coefficientSequenceModules l E W
  let q := HomotopyCategory.quotient A (.up ℤ)
  let H := M.tensor.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := B)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ Q : CochainComplex A ℤ,
      (Q.IsKFlatIndependentCoefficients ∧ ∀ p : ℤ, (Q.X p).IsFlatOnSite) ∧ q.obj Q = X
  have hr : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : HomotopyCategory A (.up ℤ)) (s : Y ⟶ X),
        Y ∈ P ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Q, f, hQ, hf⟩ := exists_flatTermKFlatResolution l E W X
    exact ⟨q.obj Q, q.map f, ⟨Q, hQ, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hi : ∀ X Y (f : X ⟶ Y), X ∈ P → Y ∈ P →
      HomotopyCategory.quasiIso A (.up ℤ) f → IsIso (H.map f) := by
    rintro _ _ f ⟨Q, hQ, rfl⟩ ⟨Q', hQ', rfl⟩ hf
    obtain ⟨f, rfl⟩ := q.map_surjective f
    have := tensor_inverts l E W M f hQ.1 hQ'.1
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf)
    change IsIso (DerivedCategory.Q.map ((M.quotient l E W).map f))
    infer_instance
  obtain ⟨_, L, εh, hL, _, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (coefficientSequenceDerived l E W) H P hr hi
  let := hL
  obtain ⟨ε, hε, he⟩ := CategoryTheory.leftDerivedOnComplexes M.tensor
    (𝟭 (coefficientSequenceDerived l E W)) L εh
  obtain ⟨a, ha⟩ := derivedAdjunctionOfResolvingClass M.tensor (ordinaryLimit l E W)
    M.adjunction P hr hi L εh hL (coefficientSequenceLimit l E W) δ hδ
  refine ⟨L, ε, a, hε, ?_, ?_⟩
  · intro Q hQ hf
    rw [he]
    exact hcomp (q.obj Q) ⟨Q, ⟨hQ, hf⟩, rfl⟩
  · intro Q I f
    rw [he]
    exact ha Q I f

/-! ### Finite evaluation of the derived comparison -/

section FiniteMate

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence


/-- Localization factors for the canonical square of exact functors. -/
private theorem square_factors
    {A B B' D : Type*} [Category* A] [Category* B] [Category* B'] [Category* D]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ B') (G₂ : B' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (I : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app I) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj I) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app I) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj I) =
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  apply (cancel_epi (F₂.mapDerivedCategoryFactors.inv.app
    ((F₁.mapHomologicalComplex (.up ℤ)).obj I))).mp
  rw [Iso.inv_hom_id_app_assoc]
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ I
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ I
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hG, Functor.mapDerivedCategoryNatIso_fac]
  rw [← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

/-- Localization of a termwise adjunction unit agrees in the two quotient coordinates. -/
private theorem localized_unit
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {F : A ⥤ B} {R : B ⥤ A} [F.Additive] [R.Additive] (a : F ⊣ R)
    (Q : CochainComplex A ℤ) :
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app Q) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

/-- The finite scalar unit on a K-flat complex in the cochain localization coordinates. -/
private theorem finiteModel_unit
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (n : ℕ) :
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          (coefficientFiniteReductionModel l E W Q hQ n).hom ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) := by
  have h := (derivedScalarExtensionRestrictionAdjunction l E W n).choose_spec Q hQ
  have hfac := (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh_hom_app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)
  have hfac' : (scalarReductionRestriction l E W n).mapDerivedCategoryFactorsh.hom.app
      (((scalarReductionExtension l E W n).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q) := by
    erw [hfac]
    change (scalarReductionDerivedRestriction l E W n).map (𝟙 _) ≫ _ ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [(scalarReductionRestriction l E W n).mapDerivedCategory.map_id,
      DerivedCategory.Qh.map_id, Category.id_comp, Category.comp_id]
  have hunit : DerivedCategory.Qh.map
      ((((scalarReductionExtension_adjunction l E W n).choose).mapHomotopyCategory
        (.up ℤ)).unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) =
      DerivedCategory.Q.map
        ((((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
          (.up ℤ)).unit.app Q) :=
    localized_unit (scalarReductionExtension_adjunction l E W n).choose Q
  have hmodel : (coefficientFiniteReductionModel l E W Q hQ n).hom =
      (scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) := by
    dsimp only [coefficientFiniteReductionModel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app, asIso_hom]
    change (coefficientFiniteDerivedExtension l E W n).map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
    erw [(coefficientFiniteDerivedExtension l E W n).map_id, Category.id_comp]
    rfl
  refine (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (coefficientFiniteDerivedRestriction l E W n).map f ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
          hmodel).trans ?_
  exact (congrArg (fun f ↦
    (coefficientFiniteAdjunction l E W n).unit.app (DerivedCategory.Q.obj Q) ≫
      (scalarReductionDerivedRestriction l E W n).map
        ((scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) ≫ f) hfac'.symm).trans
      (h.trans hunit)

/-- Extend the defining K-injective normalization to the projection at any tower. -/
private theorem limitUnit_projection
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    η.app Z ≫ (coefficientConstantTowerProjection l E W n).app
        (DerivedCategory.Q.obj Z) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app Z =
      DerivedCategory.Q.map (c.inv.app Z ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app Z) := by
  let ev := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  let τ := NatTrans.mapHomologicalComplex
    (lim.π (op n) : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ _) ⟶ ev) (.up ℤ)
  let α := η ≫ Functor.whiskerLeft DerivedCategory.Q
    (coefficientConstantTowerProjection l E W n) ≫
      (coefficientConstantTowerEvaluationFactors l E W n).hom
  let β := Functor.whiskerRight (c.inv ≫ τ) DerivedCategory.Q
  have hJ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective] : α.app J = β.app J := by
    change η.app J ≫ ((coefficientConstantTowerProjection l E W n).app
      (DerivedCategory.Q.obj J) ≫ _) = _
    erw [(coefficientConstantTowerProjection_exists l E W n).choose_spec.1 J]
    rw [← Category.assoc, hηnorm, ← DerivedCategory.Q.map_comp]
    rfl
  obtain ⟨J, hJ', j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective Z
  let : J.IsKInjective := hJ'
  let : QuasiIso j := hj
  have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map j) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology j ev
  apply (cancel_mono (DerivedCategory.Q.map
    ((ev.mapHomologicalComplex (.up ℤ)).map j))).mp
  change α.app Z ≫ (ev.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map j =
    β.app Z ≫ (ev.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map j
  rw [← α.naturality, ← β.naturality, hJ J]

/-- The specified ordinary tensor unit agrees with the chosen scalar unit. -/
private theorem ordinary_unit (M : OrdinaryModel l E W)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
    ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        M.limitComparison.hom.app ((M.quotient l E W).obj Q) ≫
        limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor (op n) ≫
        (NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app
            ((M.quotient l E W).obj Q) ≫
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
      (((scalarReductionExtension_adjunction l E W n).choose).mapHomologicalComplex
        (.up ℤ)).unit.app Q := by
  apply HomologicalComplex.hom_ext
  intro p
  have hp := M.limitComparison_projection ((M.quotient l E W).obj Q) n p
  have hunit := M.unit_tensor (Q.X p) n
  have hu := (scalarReductionExtension_adjunction l E W n).choose_spec (Q.X p)
  change M.adjunction.unit.app (Q.X p) ≫
    (M.limitComparison.hom.app ((M.quotient l E W).obj Q) ≫
      limit.π ((tower l E W).obj ((M.quotient l E W).obj Q)).asFunctor (op n)).f p ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (M.tensor.obj (Q.X p)) ≫
    (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app (Q.X p)) =
      ((scalarReductionExtension_adjunction l E W n).choose).unit.app (Q.X p)
  refine (congrArg (fun f ↦ M.adjunction.unit.app (Q.X p) ≫ f ≫
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (M.tensor.obj (Q.X p)) ≫
    (scalarReductionRestriction l E W n).map ((M.evaluation n).hom.app (Q.X p))) hp).trans ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  exact (hunit V x).trans (by
    dsimp only [unrestrictedIntegralTensorSection, unrestrictedIntegralReductionFunctor,
      unrestrictedIntegralReductionExistence, scalarReductionExistence] at hu ⊢
    exact (hu V x).symm)

/-- Project the comparison with total limit in the exact finite restriction coordinates. -/
private theorem system_projection
    (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (I : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (DerivedCategory.Q.map (M.limitComparison.hom.app I) ≫
        η.app ((tower l E W).obj I) ≫
        (coefficientConstantTowerLimit l E W).map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app I)) ≫
        (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj I) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app I) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj I) =
      DerivedCategory.Q.map (M.limitComparison.hom.app I ≫
        limit.π ((tower l E W).obj I).asFunctor (op n) ≫
        (NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app I) := by
  let U := coefficientSequenceRestriction l E W
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  let F := coefficientSequenceEvaluation l E W n
  let R := scalarReductionRestriction l E W n
  let e := eqToIso (coefficientSequenceRestriction_evaluation l E W n)
  have hsq := square_factors U V F R e I
  have hπ := limitUnit_projection l E W c η hηnorm ((tower l E W).obj I) n
  have hcπ : c.inv.app ((tower l E W).obj I) ≫
      (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
        ((tower l E W).obj I) = limit.π ((tower l E W).obj I).asFunctor (op n) := by
    apply (cancel_epi (c.hom.app ((tower l E W).obj I))).mp
    rw [Iso.hom_inv_id_app_assoc]
    apply HomologicalComplex.hom_ext
    intro p
    exact (hc _ n p).symm
  rw [hcπ] at hπ
  dsimp only [coefficientSequenceProjection, NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [(coefficientConstantTowerProjection l E W n).naturality_assoc
    (U.mapDerivedCategoryFactors.inv.app I)]
  have hsq' : (coefficientConstantTowerEvaluation l E W n).map
      (U.mapDerivedCategoryFactors.inv.app I) ≫
      (coefficientRestrictedEvaluationIso l E W n).hom.app (DerivedCategory.Q.obj I) ≫
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
      R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) =
    V.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
    exact hsq
  erw [hsq']
  erw [reassoc_of% hπ]
  simp only [← DerivedCategory.Q.map_comp]
  rfl

/-- A derived comparison normalized by the ordinary tensor unit has the fixed finite values,
for any left adjoint of the total limit and any finite comparison `θ` compatible with the
adjunction units and the total-limit projections.

Source: Stacks 07A6, 0941, 06YY and 09T5.

Proof: apply the injective finite scalar Hom bijection. The unit-projection identity and
naturality of the projection identify the left side with the projection of the transpose
of the comparison. The normalization `hunit` computes this transpose by the ordinary
tensor unit and the system limit unit, whose projection is the ordinary limit projection.
The ordinary unit is `x ↦ 1 ⊗ x`, which is also the normalized finite scalar unit on a
K-flat representative. -/
theorem finiteComparison_of_unitProjection (M : OrdinaryModel l E W)
    (c : (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).mapHomologicalComplex (.up ℤ) ≅ roosLimitFunctor)
    (hc : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (n : ℕ) (p : ℤ),
      (c.hom.app Z ≫ limit.π Z.asFunctor (op n)).f p = limit.π (Z.X p) (op n))
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (hηnorm : ∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [J.IsKInjective], η.app J ≫
        ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
          scalarReductionSource l E W).rightDerivedFunctorObjQIso J).hom =
        DerivedCategory.Q.map (c.inv.app J))
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (θ : ∀ n : ℕ, coefficientFiniteDerivedExtension l E W n ⟶
      L ⋙ coefficientSequenceDerivedEvaluation l E W n)
    (hθ : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
      adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P) =
        (coefficientFiniteAdjunction l E W n).unit.app P ≫
          (coefficientFiniteDerivedRestriction l E W n).map ((θ n).app P))
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hunit : ∀ Q : CochainComplex (scalarReductionSource l E W) ℤ,
      adj.homEquiv (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj ((M.quotient l E W).obj Q)) (ε.app Q) =
        DerivedCategory.Q.map
          ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
            (systemLimitUnit l E W M η).app ((M.quotient l E W).obj Q))
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (n : ℕ) :
    (θ n).app (DerivedCategory.Q.obj Q) ≫
        (coefficientSequenceDerivedEvaluation l E W n).map (ε.app Q) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((M.quotient l E W).obj Q) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
      (coefficientFiniteReductionModel l E W Q hQ n).hom := by
  let P := DerivedCategory.Q.obj Q
  let I := (M.quotient l E W).obj Q
  let R := scalarReductionRestriction l E W n
  let e := (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q
  have hunit' := hunit Q
  dsimp only [systemLimitUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hunit'
  apply ((coefficientFiniteAdjunction l E W n).homEquiv P _).injective
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app
    (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))).mp
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hθ P n)]
  erw [← (coefficientSequenceProjection l E W n).naturality_assoc (ε.app Q)]
  rw [← reassoc_of% (adj.homEquiv_unit P (DerivedCategory.Q.obj I) (ε.app Q)), hunit']
  erw [R.mapDerivedCategoryFactors.hom.naturality e]
  have hp := system_projection l E W M c hc η hηnorm I n
  have hu := ordinary_unit l E W M Q n
  simp only [Category.assoc] at hp ⊢
  erw [reassoc_of% hp]
  simp only [Functor.comp_map, ← Functor.map_comp, Category.assoc]
  erw [hu]
  exact (finiteModel_unit l E W Q hQ n).symm

end FiniteMate

/-! ### The derived comparison for an arbitrary left adjoint of the total limit -/

/-- The system limit unit for the constant-tower limit unit exhibits the right derived
functor of the ordinary sequence limit. Source: Stacks 0D6E, 0941 and 07A6. -/
theorem systemLimitUnit_isRightDerived (M : OrdinaryModel l E W) :
    (coefficientSequenceLimit l E W).IsRightDerivedFunctor
      (systemLimitUnit l E W M (constantLimitUnit l E W))
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ)) := by
  have hsys := systemLimitUnit_isIso l E W M (termwiseLimitComparison l E W)
    (constantLimitUnit l E W) (constantLimitUnit_normalization l E W)
  apply (CategoryTheory.derives (ordinaryLimit l E W)).isRightDerivedFunctor_of_isIso
    (systemLimitUnit l E W M (constantLimitUnit l E W))
  intro I
  exact hsys I.obj I.property

/-- The specified total limit of coefficient systems has a left adjoint.
Source: Stacks 07A6, 09T5 and 0941.

Proof: derive the ordinary quotient-system adjunction on flat-term K-flat complexes and
K-injective systems; the derived right adjoint is `coefficientSequenceLimit` by the
normalized composition with exact restriction. -/
theorem leftAdjoint_exists :
    ∃ L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W,
      Nonempty (L ⊣ coefficientSequenceLimit l E W) := by
  obtain ⟨M⟩ := ordinaryModel_exists l E W
  obtain ⟨L, -, a, -⟩ := tensor_derived_exists l E W M
    (systemLimitUnit l E W M (constantLimitUnit l E W)) (systemLimitUnit_isRightDerived l E W M)
  exact ⟨L, ⟨a⟩⟩

/-- Every left adjoint of the total limit is the left derived functor of the strict
quotient-system tensor, through a comparison normalized by the derived Hom formula.
It is invertible on flat-term K-flat complexes.

Source: Stacks 06YY, 07A6, 09T5, 0941 and 0D6E.

Proof: derive the ordinary adjunction on flat-term K-flat complexes and K-injective
systems. Its derived left functor and `L` are both left adjoint to
`coefficientSequenceLimit`; transport the universal left-derived comparison along the
unique adjunction-compatible isomorphism. This preserves the universal property, the
invertibility on flat-term K-flat complexes and the derived Hom formula. -/
theorem reductionComparison_exists (M : OrdinaryModel l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W) :
    ∃ ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q,
      L.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) ∧
      (∀ Q : CochainComplex (scalarReductionSource l E W) ℤ,
        Q.IsKFlatIndependentCoefficients → (∀ p : ℤ, (Q.X p).IsFlatOnSite) →
          IsIso (ε.app Q)) ∧
      (∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (f : (M.quotient l E W).obj Q ⟶ I),
        adj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
            (ε.app Q ≫ DerivedCategory.Q.map f) =
          DerivedCategory.Q.map
              ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
            (systemLimitUnit l E W M (constantLimitUnit l E W)).app I) := by
  obtain ⟨L₀, ε, a, hε, hcomp, hhom⟩ := tensor_derived_exists l E W M
    (systemLimitUnit l E W M (constantLimitUnit l E W)) (systemLimitUnit_isRightDerived l E W M)
  let e := adj.leftAdjointUniq a
  let ε' : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q :=
    Functor.whiskerLeft DerivedCategory.Q e.hom ≫ ε
  refine ⟨ε', ?_, ?_, ?_⟩
  · exact (Functor.isLeftDerivedFunctor_iff_of_iso (LF := L) (LF' := L₀) (α := ε') ε
      (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) e rfl).2 hε
  · intro Q hQ hf
    have := hcomp Q hQ hf
    dsimp only [ε', NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · intro Q I f
    rw [← hhom Q I f]
    change adj.homEquiv _ _
      ((e.hom.app (DerivedCategory.Q.obj Q) ≫ ε.app Q) ≫ DerivedCategory.Q.map f) = _
    rw [Category.assoc, adj.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      adj.unit_leftAdjointUniq_hom_app a]
    exact (a.homEquiv_unit _ _ _).symm

/-- The derived Hom formula determines the transpose of the comparison itself.
Source: Stacks 07A6. -/
theorem reductionComparison_unit (M : OrdinaryModel l E W)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hhom : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      adj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M η).app I)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    adj.homEquiv (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj ((M.quotient l E W).obj Q)) (ε.app Q) =
      DerivedCategory.Q.map
          ((M.adjunction.mapHomologicalComplex (.up ℤ)).unit.app Q) ≫
        (systemLimitUnit l E W M η).app ((M.quotient l E W).obj Q) := by
  have h := hhom Q ((M.quotient l E W).obj Q) (𝟙 _)
  have hid : ε.app Q ≫ DerivedCategory.Q.map (𝟙 ((M.quotient l E W).obj Q)) = ε.app Q := by
    rw [(DerivedCategory.Q (C := coefficientSequenceModules l E W)).map_id]
    exact Category.comp_id _
  have hh := (congrArg (adj.homEquiv (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj ((M.quotient l E W).obj Q))) hid).symm.trans h
  simpa only [Adjunction.homEquiv_id] using hh

/-- The finite values of the normalized derived comparison, for any left adjoint `L` of
the total limit and any finite evaluation isomorphisms `ρ` satisfying the
unit-projection identity.

Source: Stacks 07A6, 0941, 06YY and 09T5.

Proof: apply `finiteComparison_of_unitProjection` to the inverses of `ρ` and cancel. -/
theorem finiteComparison_of_unit (M : OrdinaryModel l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n)
    (hunitproj : ∀ (P : DerivedCategory (scalarReductionSource l E W)) (n : ℕ),
      adj.unit.app P ≫ (coefficientSequenceProjection l E W n).app (L.obj P) =
        (coefficientFiniteAdjunction l E W n).unit.app P ≫
          (coefficientFiniteDerivedRestriction l E W n).map ((ρ n).inv.app P))
    (ε : DerivedCategory.Q ⋙ L ⟶ M.quotient l E W ⋙ DerivedCategory.Q)
    (hhom : ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
      (I : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (f : (M.quotient l E W).obj Q ⟶ I),
      adj.homEquiv (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj I)
          (ε.app Q ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map
            ((M.adjunction.mapHomologicalComplex (.up ℤ)).homEquiv Q I f) ≫
          (systemLimitUnit l E W M (constantLimitUnit l E W)).app I)
    (Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (hQ : Q.IsKFlatIndependentCoefficients) (_hflat : ∀ p : ℤ, (Q.X p).IsFlatOnSite)
    (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).map (ε.app Q) ≫
        (coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app
          ((M.quotient l E W).obj Q) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).hom.app Q) =
      (ρ n).hom.app (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom := by
  rw [← finiteComparison_of_unitProjection l E W M (termwiseLimitComparison l E W)
    (termwiseLimitComparison_projection l E W) (constantLimitUnit l E W)
    (constantLimitUnit_normalization l E W) L adj (fun n ↦ (ρ n).inv) hunitproj ε
    (reductionComparison_unit l E W M (constantLimitUnit l E W) L adj ε hhom) Q hQ n]
  simp only [Iso.hom_inv_id_app_assoc]

end WeilConjectures.OrdinaryQuotient
