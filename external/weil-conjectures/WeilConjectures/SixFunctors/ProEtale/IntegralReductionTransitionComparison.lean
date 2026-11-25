/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.SixFunctors.ProEtale.IntegralPresentationEncoding
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.PrincipalConeTower
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift

set_option linter.privateModule false

/-! # Transition compatibility for normalized integral comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  scalarReductionDerivedExtension scalarReductionExtension scalarReductionCounit
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Unit-normalized comparisons preserve adjoint quotient transitions. -/
private theorem adjointTransitionComparison
    {C A B C' A' B' : Type*}
    [Category C] [Category A] [Category B]
    [Category C'] [Category A'] [Category B']
    {L : C ⥤ A} {U : A ⥤ C} {N : C ⥤ B} {W : B ⥤ C}
    {L' : C' ⥤ A'} {R : A' ⥤ C'} {N' : C' ⥤ B'} {S : B' ⥤ C'}
    (al : L ⊣ U) (an : N ⊣ W) (ar : L' ⊣ R) (as' : N' ⊣ S)
    (V : B ⥤ A) (T : B' ⥤ A') (F : C ⥤ C') (G : A ⥤ A') (H : B ⥤ B')
    (a : U ⋙ F ≅ G ⋙ R) (b : W ⋙ F ≅ H ⋙ S)
    (e : V ⋙ G ≅ H ⋙ T) (c : V ⋙ U ≅ W) (d : T ⋙ R ≅ S)
    (hsq : ∀ Z, F.map (c.hom.app Z) ≫ b.hom.app Z =
      a.hom.app (V.obj Z) ≫ R.map (e.hom.app Z) ≫ d.hom.app (H.obj Z))
    (K : C) (bm : L'.obj (F.obj K) ≅ G.obj (L.obj K))
    (bn : N'.obj (F.obj K) ≅ H.obj (N.obj K))
    (hm : ar.unit.app (F.obj K) ≫ R.map bm.hom ≫ a.inv.app (L.obj K) =
      F.map (al.unit.app K))
    (hn : as'.unit.app (F.obj K) ≫ S.map bn.hom ≫ b.inv.app (N.obj K) =
      F.map (an.unit.app K))
    (v : L.obj K ⟶ V.obj (N.obj K))
    (hv : al.unit.app K ≫ U.map v ≫ c.hom.app (N.obj K) = an.unit.app K) :
    R.map ((ar.homEquiv (F.obj K) (T.obj (N'.obj (F.obj K)))).symm
        (as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)))) ≫
        d.hom.app (N'.obj (F.obj K)) ≫ S.map bn.hom ≫ b.inv.app (N.obj K) =
      R.map bm.hom ≫ a.inv.app (L.obj K) ≫
        F.map (U.map v ≫ c.hom.app (N.obj K)) := by
  have hm' : ar.unit.app (F.obj K) ≫ R.map bm.hom =
      F.map (al.unit.app K) ≫ a.hom.app (L.obj K) := by
    have h := congrArg (fun k ↦ k ≫ a.hom.app (L.obj K)) hm
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  have hn' : as'.unit.app (F.obj K) ≫ S.map bn.hom =
      F.map (an.unit.app K) ≫ b.hom.app (N.obj K) := by
    have h := congrArg (fun k ↦ k ≫ b.hom.app (N.obj K)) hn
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  let t := (ar.homEquiv (F.obj K) (T.obj (N'.obj (F.obj K)))).symm
    (as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)))
  have ht : bm.hom ≫ G.map v ≫ e.hom.app (N.obj K) = t ≫ T.map bn.hom := by
    apply (ar.homEquiv _ _).injective
    simp only [ar.homEquiv_unit, R.map_comp]
    have htu : ar.unit.app (F.obj K) ≫ R.map t =
        as'.unit.app (F.obj K) ≫ d.inv.app (N'.obj (F.obj K)) :=
      (ar.homEquiv_unit _ _ t).symm.trans ((ar.homEquiv _ _).apply_symm_apply _)
    rw [reassoc_of% htu]
    apply (cancel_mono (d.hom.app (H.obj (N.obj K)))).1
    rw [reassoc_of% hm']
    have ha := a.hom.naturality v
    dsimp only [Functor.comp_map] at ha
    simp only [Category.assoc]
    rw [← reassoc_of% ha, ← hsq]
    have hd := d.hom.naturality bn.hom
    dsimp only [Functor.comp_map] at hd
    rw [hd]
    simp only [Iso.inv_hom_id_app_assoc]
    rw [hn', ← F.map_comp_assoc, ← F.map_comp_assoc, Category.assoc, hv]
  have hc : a.inv.app (V.obj (N.obj K)) ≫ F.map (c.hom.app (N.obj K)) =
      R.map (e.hom.app (N.obj K)) ≫ d.hom.app (H.obj (N.obj K)) ≫
        b.inv.app (N.obj K) := by
    have h := congrArg
      (fun k ↦ a.inv.app (V.obj (N.obj K)) ≫ k ≫ b.inv.app (N.obj K))
      (hsq (N.obj K))
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc] at h
    dsimp only [Functor.comp_obj] at h
    simpa only [Category.comp_id] using h
  have ha := a.inv.naturality v
  dsimp only [Functor.comp_map] at ha
  change R.map t ≫ d.hom.app (N'.obj (F.obj K)) ≫ S.map bn.hom ≫
      b.inv.app (N.obj K) = _
  rw [F.map_comp]
  rw [← reassoc_of% ha]
  rw [hc, ← R.map_comp_assoc, ← R.map_comp_assoc]
  simp only [Category.assoc]
  rw [ht, R.map_comp]
  have hd := d.hom.naturality bn.hom
  dsimp only [Functor.comp_map] at hd
  rw [Category.assoc, reassoc_of% hd]

attribute [local irreducible] Functor.mapDerivedCategory

section RestrictionCompositor
attribute [local semireducible] completedIntegralCoefficientSheafUnrestricted

end RestrictionCompositor

end AlgebraicGeometry.ProEtale.IntegralPresentation
