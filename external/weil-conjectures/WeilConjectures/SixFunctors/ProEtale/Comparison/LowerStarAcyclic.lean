/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.InjectiveAcyclic

import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonInjectiveDerivedVanishing
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-!
# Acyclicity for pro-étale direct images on the affine pro-étale basis

Let `f : U ⟶ V` be a morphism of schemes. A pro-étale sheaf `G` on `U` is acyclic for the
direct image `f_*` as soon as its higher derived sections over the pro-étale `U`-schemes
`U ×_V W` vanish, for `W` running over the affine pro-étale site of `V`
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isZero_rightDerived`): the higher
direct images are computed by `f_*` of an injective resolution, whose complex of sections over
`W` is the complex of sections over `U ×_V W` of the resolution, and exactness of a complex of
sheaves can be tested on the presheaves underlying its restriction to the affine pro-étale site.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- A pro-étale sheaf `G` on `U` is acyclic for the direct image along `f : U ⟶ V` if its higher
derived sections over `U ×_V W` vanish for every object `W` of the affine pro-étale site of
`V`. -/
theorem rightAcyclic_lowerStar_of_isZero_rightDerived {U V : Scheme.{u}} (f : U ⟶ V)
    (G : Sheaf (ProEt.topology U) A)
    (h : ∀ (W : V.AffineProEt) (q : ℕ), IsZero (((sectionsFunctor A
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
        ((AffineProEt.toProEt V).obj W))).rightDerived (q + 1)).obj G)) :
    (ProEtale.lowerStar A f).rightAcyclic G := by
  intro q
  let R : InjectiveResolution G := injectiveResolution G
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj _ (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology]
  refine ShortComplex.exact_of_exact_sectionsFunctor A _ fun W ↦ ?_
  have h' := (h W q).of_iso (R.isoRightDerivedObj _ (q + 1)).symm
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology] at h'
  exact h'

private lemma affine_etale_sections_vanishing (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology A) [Injective I]
    (W : X.AffineEtale) (q : ℕ) :
    IsZero (((sectionsFunctor A ((toProEt X).obj ((AffineEtale.Spec X).obj W))).rightDerived
      (q + 1)).obj ((comparisonUpperStar A X).obj I)) := by
  let T := (toProEt X).obj ((AffineEtale.Spec X).obj W)
  have : Etale T.hom := ((AffineEtale.Spec X).obj W).prop
  have : IsAffine T.left := by
    change IsAffine ((AffineEtale.Spec X).obj W).left
    rw [AffineEtale.Spec_obj_left]
    infer_instance
  have hT : WeaklyEtale T.hom := T.prop
  let j := ProEtale.localizationRestriction A T.hom hT
  let Γ := sheafToPresheaf (ProEt.topology T.left) A ⋙
    (evaluation _ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 T.left)
      (MorphismProperty.id_mem _ T.left)))
  let e : T ≅ (MorphismProperty.Over.map ⊤ hT).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 T.left) (MorphismProperty.id_mem _ T.left)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by exact Category.id_comp _)
  have : j.Additive := {}
  let eΓ : sectionsFunctor A T ≅ j ⋙ Γ :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op) (fun φ ↦ (φ.hom.naturality e.inv.op).symm)
  have : PreservesFiniteColimits j :=
    preservesFiniteColimits_of_natIso (ProEtale.upperStarIsoLocalizationRestriction A T.hom hT)
  have : PreservesFiniteLimits j :=
    preservesFiniteLimits_of_natIso (ProEtale.upperStarIsoLocalizationRestriction A T.hom hT)
  have : Injective ((Etale.upperStar A T.hom).obj I) :=
    Etale.injective_upperStar_obj_of_etale' A T.hom I
  have h := isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine A T.left
    ((Etale.upperStar A T.hom).obj I) q
  let eR : (sectionsFunctor A T).rightDerived (q + 1) ≅
      (j ⋙ Γ).rightDerived (q + 1) :=
    { hom := NatTrans.rightDerived eΓ.hom (q + 1)
      inv := NatTrans.rightDerived eΓ.inv (q + 1)
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, eΓ.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, eΓ.inv_hom_id, NatTrans.rightDerived_id] }
  refine IsZero.of_iso h (eR.app _ ≪≫
    (Functor.rightDerivedCompIsoOfExact j Γ (q + 1)).app _ ≪≫ ?_)
  exact (Γ.rightDerived (q + 1)).mapIso
    (((ProEtale.upperStarIsoLocalizationRestriction A T.hom hT).app _).symm ≪≫
      (comparisonUpperStarUpperStarIso A T.hom).app I)

section Acyclicity

/-- **Comparison of global cohomology.** The derived global sections of the comparison pullback
`ν^* M` of an étale sheaf are those of `M`: `RΓ(X_proét, ν^* M) ≅ RΓ(X_ét, M)` in the bounded
below derived category, by the invertibility of the derived unit `M ⟶ Rν_* ν^* M`, given that
`ν^* I` is acyclic for `ν_*` for every injective étale sheaf `I`. -/
noncomputable def rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoOfRightAcyclic
    (X : Scheme.{u})
    (hI : ∀ (I : Sheaf X.smallEtaleTopology A) [Injective I],
      ν_*(X)[A].rightAcyclic (ν^*(X)[A].obj I))
    (M : Sheaf X.smallEtaleTopology A) :
    (globalSectionsFunctor A X).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((comparisonUpperStar A X).obj M)) ≅
      (Etale.sectionsFunctor A X).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) := by
  have := isIso_comparisonAdjunction_unit A X
  have : (comparisonLowerStar A X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (comparisonAdjunction A X)
  -- the derived unit `M ⟶ Rν_* ν^* M` is invertible
  have hu := (comparisonAdjunction A X).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance) (fun I _ ↦ hI I)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M)
  -- the global sections of a pro-étale sheaf are the global sections of its restriction
  exact (Functor.rightDerivedFunctorPlusCompIso (comparisonLowerStar A X)
      (Etale.sectionsFunctor A X)).app _ ≪≫
    (Etale.sectionsFunctor A X).rightDerivedFunctorPlus.mapIso
      ((comparisonLowerStar A X).rightDerivedFunctorPlus.mapIso
        (((comparisonUpperStar A X).mapDerivedCategoryPlusSingleFunctor 0).app M).symm ≪≫
      (asIso ((comparisonAdjunction A X).derivedPlus.unit.app _)).symm)

/-- **Comparison of global cohomology.** The derived global sections of the comparison pullback
`ν^* M` of an étale sheaf are those of `M` in each degree: `R^qΓ(X_proét, ν^* M) ≅ R^qΓ(X_ét, M)`,
the cohomology in degree `q` of
`rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoOfRightAcyclic`. -/
noncomputable def rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIsoOfRightAcyclic
    (X : Scheme.{u})
    (hI : ∀ (I : Sheaf X.smallEtaleTopology A) [Injective I],
      ν_*(X)[A].rightAcyclic (ν^*(X)[A].obj I))
    (M : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    ((globalSectionsFunctor A X).rightDerived q).obj ((comparisonUpperStar A X).obj M) ≅
      ((Etale.sectionsFunctor A X).rightDerived q).obj M :=
  ((globalSectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).symm.app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      (rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoOfRightAcyclic A X hI M) ≪≫
    ((Etale.sectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).app M

/-- **Comparison of global cohomology.** The derived global sections of the comparison pullback
`ν^* M` of an étale sheaf are those of `M`: `RΓ(X_proét, ν^* M) ≅ RΓ(X_ét, M)` in the bounded
below derived category, by the invertibility of the derived unit `M ⟶ Rν_* ν^* M`. -/
noncomputable def rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIso
    (X : Scheme.{u}) (M : Sheaf X.smallEtaleTopology A) :
    (globalSectionsFunctor A X).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((comparisonUpperStar A X).obj M)) ≅
      (Etale.sectionsFunctor A X).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M) :=
  rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIsoOfRightAcyclic A X
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A X I) M

/-- **Comparison of global cohomology.** The derived global sections of the comparison pullback
`ν^* M` of an étale sheaf are those of `M` in each degree: `R^qΓ(X_proét, ν^* M) ≅ R^qΓ(X_ét, M)`,
the cohomology in degree `q` of `rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIso`.
-/
noncomputable def rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    ((globalSectionsFunctor A X).rightDerived q).obj ((comparisonUpperStar A X).obj M) ≅
      ((Etale.sectionsFunctor A X).rightDerived q).obj M :=
  ((globalSectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).symm.app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      (rightDerivedFunctorPlusGlobalSectionsComparisonUpperStarObjIso A X M) ≪≫
    ((Etale.sectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).app M

/-- **Comparison of global cohomology.** The derived global sections of the comparison pullback
`ν^* M` of an étale sheaf vanish in degree `q` if those of `M` do
(`rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso`). -/
lemma isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology A) (q : ℕ)
    (h : IsZero (((Etale.sectionsFunctor A X).rightDerived q).obj M)) :
    IsZero (((globalSectionsFunctor A X).rightDerived q).obj
      ((comparisonUpperStar A X).obj M)) :=
  h.of_iso (rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso A X M q)

end Acyclicity

/-- **Acyclicity of pulled-back injectives over quasi-compact quasi-separated objects.** Let
`f : U ⟶ V` be quasi-compact and quasi-separated, `I` an injective étale sheaf on `U` and `W` an
object of the affine pro-étale site of `V`. Then the higher derived sections of `ν_U^* I` over
the quasi-compact quasi-separated pro-étale `U`-scheme `U ×_V W` vanish. -/
theorem isZero_rightDerived_sectionsFunctor_comparisonUpperStar_obj {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A)
    [Injective I] (W : V.AffineProEt) (q : ℕ) :
    IsZero (((sectionsFunctor A ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
      ((AffineProEt.toProEt V).obj W))).rightDerived (q + 1)).obj
        ((comparisonUpperStar A U).obj I)) := by
  obtain ⟨J, _, _, ⟨pres⟩⟩ := AffineProEt.exists_relativeLimitPresentation _ W
  let c := pullbackPresentationCone f pres
  refine isZero_rightDerived_sectionsFunctor_of_upperStar A c.pt _ _ ?_
  refine IsZero.of_iso ?_ (((globalSectionsFunctor A c.pt.left).rightDerived (q + 1)).mapIso
    ((comparisonUpperStarCompUpperStarIso A c.pt.hom).app I))
  refine isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj A _ _ _ ?_
  have (j : J) : CompactSpace
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).obj j).left :=
    inferInstanceAs (CompactSpace ((pullbackPresentationDiagram f pres).obj j).left)
  have (j : J) : QuasiSeparatedSpace
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).obj j).left :=
    inferInstanceAs (QuasiSeparatedSpace ((pullbackPresentationDiagram f pres).obj j).left)
  have {i j : J} (g : i ⟶ j) : IsAffineHom
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).map g).left :=
    inferInstanceAs (IsAffineHom ((pullbackPresentationDiagram f pres).map g).left)
  refine Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit A I
    (pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U) ((ProEt.forget U).mapCone c)
    (isLimitPullbackPresentationCone f pres) (q + 1) fun j ↦ ?_
  have : Injective ((Etale.upperStar A
      ((pullbackPresentationDiagram f pres ⋙ toProEt U ⋙ ProEt.forget U).obj j).hom).obj I) :=
    Etale.injective_upperStar_obj_of_etale' A ((pullbackPresentationDiagram f pres).obj j).hom I
  exact Functor.isZero_rightDerived_obj_injective_succ _ _ _

/-- For `f` quasi-compact and quasi-separated, the comparison pullback `ν_U^* I` of an injective
étale sheaf is acyclic for the pro-étale direct image `f_*`. -/
theorem rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective {U V : Scheme.{u}}
    (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f] (I : Sheaf U.smallEtaleTopology A)
    [Injective I] :
    (ProEtale.lowerStar A f).rightAcyclic ((comparisonUpperStar A U).obj I) :=
  rightAcyclic_lowerStar_of_isZero_rightDerived A f _
    (isZero_rightDerived_sectionsFunctor_comparisonUpperStar_obj A f I)

end AlgebraicGeometry.ProEtale
