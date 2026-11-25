/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Shift compatibility of the ordinary and completed scalar models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory

private theorem derived_model_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : C ⥤ D) [Q.CommShift ℤ]
    (F G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
    (H J : C ⥤ E) [H.CommShift ℤ] [J.CommShift ℤ]
    (ε : Q ⋙ F ⟶ H) (η : Q ⋙ G ⟶ J) [G.IsRightKanExtension η]
    [ε.CommShift ℤ] [η.CommShift ℤ]
    (t : H ⟶ J) [t.CommShift ℤ] (e : F ⟶ G)
    (he : Functor.whiskerLeft Q e ≫ η = ε ≫ t) : e.CommShift ℤ := by
  have heK (K) : e.app (Q.obj K) ≫ η.app K = ε.app K ≫ t.app K :=
    congr_app he K
  constructor
  intro n
  apply Functor.kanShiftHom_ext J Q G η n
  intro K
  apply (cancel_epi (F.map ((Q.commShiftIso n).hom.app K))).mp
  have hε := NatTrans.shift_app_comm ε n K
  have hη := NatTrans.shift_app_comm η n K
  have ht := NatTrans.shift_app_comm t n K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc] at hε hη ht ⊢
  rw [← (shiftFunctor E n).map_comp, heK, (shiftFunctor E n).map_comp,
    reassoc_of% hε, ht]
  erw [e.naturality_assoc, hη]
  erw [reassoc_of% (heK (K⟦n⟧))]

private theorem factorh_app
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [F.mapDerivedCategoryFactorsh_hom_app]
  have hA : (DerivedCategory.quotientCompQhIso A).hom.app P =
      𝟙 (DerivedCategory.Q.obj P) := rfl
  have hB : (DerivedCategory.quotientCompQhIso B).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) := rfl
  have hF : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P =
      𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) := rfl
  erw [hA, hB, hF, F.mapDerivedCategory.map_id,
    (DerivedCategory.Qh (C := B)).map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard
  completedCoefficientMap completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
attribute [local instance 5000] integralTowerHasDerivedCategory
universe u
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L) (T : AlgebraicGeometry.Scheme.{u})

-- The counit equation compares two explicit presentations of the derived scalar functor.
/-- The canonical ordinary and completed derived scalar models have a shift-compatible
comparison preserving completion. Source: the universal derived scalar counits and the
ordinary-model comparison (blueprint: lem-sf-ordinary-completed-scalar-shift).

Proof: additive natural transformations commute with homotopy shifts degreewise. The
ordinary-model comparison intertwines the universal derived counits on cochain complexes,
hence on homotopy objects by surjectivity of the quotient. Apply the right Kan extension
universal property to this equation. Cancellation of the universal counit proves the shift
square. The completion identity of the model comparison is retained unchanged. -/
theorem ordinary_completed_scalar_shift :
    letI : (AlgebraicGeometry.Scheme.pbcDerivedExtend
        (completedCoefficientMap.{u, u} l E L i T)).CommShift ℤ :=
      PurCompactSupport.scalarCommShift (completedCoefficientMap.{u, u} l E L i T)
    ∃ e : integralOrdinaryDerivedScalar l E L i T ≅
        AlgebraicGeometry.Scheme.pbcDerivedExtend
        (completedCoefficientMap.{u, u} l E L i T),
      e.hom ≫ completedScalarComparison.{u, u} l E L i T = scalarCompletion l E L i T ∧
      e.hom.CommShift ℤ := by
  let φ := completedCoefficientMap.{u, u} l E L i T
  letI : (completedDerivedScalarExtension.{u, u} l E L i T).CommShift ℤ :=
    PurCompactSupport.scalarCommShift φ
  obtain ⟨t, e, _ht, he, hχ⟩ := integralScalarOrdinaryModelComparison l E L i T
  let F := integralOrdinaryScalar l E L i T
  let ε := F.mapDerivedCategoryFactorsh.hom
  let η : DerivedCategory.Qh ⋙ completedDerivedScalarExtension.{u, u} l E L i T ⟶
      (completedOrdinaryScalarExtension.{u, u} l E L i T).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh := AlgebraicGeometry.Scheme.pbcExtensionCounit φ
  let tH := Functor.whiskerRight
    (NatTrans.mapHomotopyCategory t.hom (.up ℤ)) DerivedCategory.Qh
  haveI := AlgebraicGeometry.Scheme.pbcDerivedExtension_universal φ
  have hkan := Functor.IsLeftDerivedFunctor.isRightKanExtension
    (AlgebraicGeometry.Scheme.pbcDerivedExtend φ)
    (AlgebraicGeometry.Scheme.pbcExtensionCounit φ)
    (HomotopyCategory.quasiIso (AlgebraicGeometry.Scheme.pbcModules T
      (completedIntegralCommRingSheafUnrestricted l E T)) (.up ℤ))
  haveI : (completedDerivedScalarExtension.{u, u} l E L i T).IsRightKanExtension η := hkan
  haveI : η.CommShift ℤ :=
    (PurCompactSupport.scalarCommShift_existsUnique φ).exists.choose_spec
  haveI : tH.CommShift ℤ := by dsimp only [tH]; infer_instance
  have h : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ η = ε ≫ tH := by
    ext K
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have hf := factorh_app F P
    change e.hom.app _ ≫ η.app _ = ε.app _ ≫ tH.app _
    dsimp only [ε]
    have hη : η.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        completedScalarCounit.{u, u} l E L i T P := by
      dsimp only [η, φ, AlgebraicGeometry.Scheme.pbcExtensionCounit,
        AlgebraicGeometry.Scheme.reductionDerivedCounit, completedScalarCounit,
        completedScalarChangeData, AlgebraicGeometry.Scheme.completedAdicChangeData]
      rfl
    have htP : tH.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P) := rfl
    rw [hf, hη, htP]
    exact he P
  refine ⟨e, hχ, ?_⟩
  exact derived_model_shift DerivedCategory.Qh F.mapDerivedCategory
    (completedDerivedScalarExtension.{u, u} l E L i T)
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    ((completedOrdinaryScalarExtension.{u, u} l E L i T).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) ε η tH e.hom h

/-- The intrinsic ordinary comparison is completion restricted to constructible objects.
Source: the normalized ordinary scalar comparison
(blueprint: lem-sf-ordinary-completed-scalar-shift). -/
theorem ordinary_scalar_comparison_hom (K : sfIntegralConstructibleCategory l E T) :
    (sfIntegralOrdinaryComparison l E L i T).hom.app K =
      (scalarCompletion l E L i T).app K.obj := by
  let χ := scalarCompletion l E L i T
  let (J : sfIntegralConstructibleCategory l E T) : IsIso (χ.app J.obj) :=
    (scalarCompletion_existsUnique l E L i T).exists.choose_spec.2 J.obj J.property.1
  let e : (sfIntegralConstructible l E T).ι ⋙ integralOrdinaryDerivedScalar l E L i T ≅
      (sfIntegralConstructible l E T).ι ⋙ integralScalarExtension l E L i T :=
    NatIso.ofComponents (fun J ↦ asIso (χ.app J.obj)) (fun f ↦ χ.naturality f.hom)
  have he : e = sfIntegralOrdinaryComparison l E L i T := by
    apply (sfIntegralOrdinaryComparison_existsUnique l E L i T).unique
    · intro P hP
      exact (scalarCompletion_existsUnique l E L i T).exists.choose_spec.1 P
    · exact (sfIntegralOrdinaryComparison_existsUnique l E L i T).exists.choose_spec
  exact (congrArg (fun a ↦ a.hom.app K) he).symm

/-- Completion in the raw ambient model, restricted to intrinsic integral objects.
Source: the canonical completed scalar comparison
(blueprint: lem-sf-ordinary-completed-scalar-shift). -/
def intrinsicScalarCompletion :
    (sfIntegralConstructible l E T).ι ⋙
        AlgebraicGeometry.Scheme.pbcDerivedExtend (completedCoefficientMap.{u, u} l E L i T) ⟶
      sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero E L i T ⋙
        (sfIntegralConstructible l L T).ι :=
  Functor.whiskerLeft (sfIntegralConstructible l E T).ι
    (completedScalarComparison.{u, u} l E L i T)

/-- The restricted comparison has the canonical completion components.
Source: the defining restriction
(blueprint: lem-sf-ordinary-completed-scalar-shift). -/
theorem intrinsicScalarCompletion_app_heq (K : sfIntegralConstructibleCategory l E T) :
    HEq ((intrinsicScalarCompletion l E L i T).app K)
      ((completedScalarComparison.{u, u} l E L i T).app K.obj) := by rfl

/-- The ordinary-to-completed comparison pastes to intrinsic completion.
Source: the completion identity of the ordinary model comparison
(blueprint: lem-sf-ordinary-completed-scalar-shift). -/
theorem intrinsicScalarCompletion_paste
    (e : integralOrdinaryDerivedScalar l E L i T ≅
      AlgebraicGeometry.Scheme.pbcDerivedExtend (completedCoefficientMap.{u, u} l E L i T))
    (h : e.hom ≫ completedScalarComparison.{u, u} l E L i T = scalarCompletion l E L i T)
    (K : sfIntegralConstructibleCategory l E T) :
    e.hom.app K.obj ≫ (intrinsicScalarCompletion l E L i T).app K =
      (sfIntegralOrdinaryComparison l E L i T).hom.app K := by
  exact (congr_app h K.obj).trans (ordinary_scalar_comparison_hom l E L i T K).symm

end WeilConjectures
