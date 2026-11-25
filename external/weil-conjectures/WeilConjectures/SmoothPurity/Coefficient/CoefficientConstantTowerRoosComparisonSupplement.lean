/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Projection-normalized Roos comparison for completed coefficient towers

Source: Stacks 0941 and the strict Roos comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w g t
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory
variable {B : Type u} [Category.{v} B] [Abelian B]
  [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
  [HasExactLimitsOfShape (Discrete ℕ) B] [EnoughInjectives B]
  [HasDerivedCategory.{w} B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ B)]

private theorem normalizedRoosIso
    (RF : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (η.app I)) :
    ∃ e : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF,
      Functor.whiskerRight roosInclusion DerivedCategory.Q ≫ e.hom = η := by
  let F := CochainComplex.kInjectiveResolutionFunctor.{g} (ℕᵒᵖ ⥤ B)
  let q := CochainComplex.toKInjectiveResolution.{g} (ℕᵒᵖ ⥤ B)
  let α := Functor.whiskerRight q (roosF ⋙ DerivedCategory.Q)
  have hi (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (α.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ B) X).2
    have : QuasiIso (roosF.map (q.app X)) := roos_map_quasiIso (q.app X)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let β := Functor.whiskerLeft F (Functor.whiskerRight roosInclusion DerivedCategory.Q)
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (β.app X) := by
    have : QuasiIso (roosInclusion.app (F.obj X)) := roos_inclusion_quasiIso _
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let δ := Functor.whiskerRight q DerivedCategory.Q
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (δ.app X) := by
    have : QuasiIso (q.app X) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{g} (ℕᵒᵖ ⥤ B) X).2
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ℕᵒᵖ ⥤ B) _).2 inferInstance
  have : IsIso δ := NatIso.isIso_of_isIso_app _
  let ε := Functor.whiskerLeft F η
  have (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : IsIso (ε.app X) := hI _ inferInstance
  have : IsIso ε := NatIso.isIso_of_isIso_app _
  let γ : F ⋙ roosLimitFunctor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso ε ≪≫ (Functor.associator F DerivedCategory.Q RF).symm ≪≫
      Functor.isoWhiskerRight (asIso δ).symm RF
  let e : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF :=
    asIso α ≪≫ (Functor.associator F roosF DerivedCategory.Q) ≪≫
      (asIso β).symm ≪≫ γ
  refine ⟨e, ?_⟩
  apply NatTrans.ext
  funext X
  change DerivedCategory.Q.map (roosInclusion.app X) ≫ e.hom.app X = η.app X
  have hq : IsIso (DerivedCategory.Q.map (q.app X)) := inferInstanceAs (IsIso (δ.app X))
  have hc : IsIso (DerivedCategory.Q.map (roosInclusion.app (F.obj X))) :=
    inferInstanceAs (IsIso (β.app X))
  dsimp only [e, γ, α, β, δ, ε, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom]
  simp only [Functor.comp_map, NatIso.isIso_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp]
  erw [Category.id_comp]
  change DerivedCategory.Q.map (roosInclusion.app X) ≫
    DerivedCategory.Q.map (roosF.map (q.app X)) ≫
      inv (DerivedCategory.Q.map (roosInclusion.app (F.obj X))) ≫
        η.app (F.obj X) ≫ RF.map (inv (DerivedCategory.Q.map (q.app X))) = _
  rw [← DerivedCategory.Q.map_comp_assoc, ← roosInclusion.naturality,
    DerivedCategory.Q.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have hn := η.naturality (q.app X)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  rw [← RF.map_comp, IsIso.hom_inv_id, RF.map_id]
  exact Category.comp_id _

end CategoryTheory

namespace WeilConjectures

/-- The canonical inverse-limit comparison preserves every specified tower projection.
Source: Stacks 0941 (blueprint: stage3-pur-canonical-tower-roos-comparison).
Proof: the ordinary-limit inclusion into the strict Roos complex is a
quasi-isomorphism on K-injective towers. Resolve functorially and invert this
inclusion to get a natural comparison. Its normalization identifies the projection
on K-injective towers with the canonical right-derived projection. Naturality
along a K-injective resolution proves the equation for every tower complex. -/
theorem coefficientConstantTowerRoosComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t}) :
    ∃ e : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W ≅
        roosF ⋙ DerivedCategory.Q,
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ),
        e.inv.app X ≫ (coefficientConstantTowerProjection l E W n).app
            (DerivedCategory.Q.obj X) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app X =
        DerivedCategory.Q.map (roosEval X n) := by
  classical
  let A := scalarReductionSource l E W
  let : IsGrothendieckAbelian.{max u (t + 1)} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : IsGrothendieckAbelian.{max u (t + 1)} (ℕᵒᵖ ⥤ A) := by
    have := roos_tower_grothendieck A (AsSmall.{max u (t + 1)} ℕᵒᵖ)
    exact IsGrothendieckAbelian.of_equivalence
      (Equivalence.congrLeft (AsSmall.equiv (C := ℕᵒᵖ)).symm)
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (Scheme.ProEt.countableProducts_exact.{t, u, 0} W
          (completedIntegralCommRingSheafUnrestricted l E W)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Limits.Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Limits.Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  let F : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun X Y f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  let β := (Functor.isoWhiskerRight (strictTowerLimitIso (A := A))
    DerivedCategory.Q).hom ≫ η
  obtain ⟨e, he⟩ := normalizedRoosIso F.rightDerivedFunctor β (fun I hI ↦ by
    have := hI
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, η]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  refine ⟨e.symm, ?_⟩
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] (n : ℕ) :
      e.hom.app I ≫ (coefficientConstantTowerProjection l E W n).app
          (DerivedCategory.Q.obj I) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app I =
      DerivedCategory.Q.map (roosEval I n) := by
    have : QuasiIso (roosι I) := roos_inclusion_quasiIso I
    apply (cancel_epi (DerivedCategory.Q.map (roosι I))).1
    rw [← Category.assoc, ← Category.assoc]
    have heI := congr_app he I
    change DerivedCategory.Q.map (roosι I) ≫ e.hom.app I = β.app I at heI
    rw [heI]
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, η]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    have hp := (coefficientConstantTowerProjection_exists l E W n).choose_spec.1 I
    change (coefficientConstantTowerProjection l E W n).app _ ≫ _ = _ at hp
    rw [Category.assoc, Category.assoc, hp]
    erw [Iso.inv_hom_id_assoc]
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    congr 1
    rw [roosι_eval]
    apply HomologicalComplex.hom_ext
    intro i
    simpa only [strictTowerLimitIso, NatIso.ofComponents_hom_app,
      HomologicalComplex.comp_f, HomologicalComplex.coneOfHasLimitEval_π_app_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_obj_X,
      HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp,
      lim.π] using congrArg (fun f ↦ HomologicalComplex.Hom.f f i)
      (limit.isoLimitCone_hom_π
        ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩ (op n))
  intro X n
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective X
  have : QuasiIso f := hf
  let V := (evaluation ℕᵒᵖ A).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map f))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality f
  have hp := (coefficientConstantTowerProjection l E W n).naturality
    (DerivedCategory.Q.map f)
  have hθ := e.hom.naturality f
  have hr := roosEval_natural f n
  dsimp only [Functor.comp_map] at hv hθ
  simp only [Iso.symm_inv, Category.assoc]
  rw [← hv]
  erw [← reassoc_of% hp]
  erw [← reassoc_of% hθ, hi I n]
  rw [← DerivedCategory.Q.map_comp, hr, DerivedCategory.Q.map_comp]
  rfl

end WeilConjectures
