/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

@[expose] public section

universe u_complex
open CategoryTheory TopologicalSpace AlgebraicGeometry
namespace SheafOfModules

/-- Acyclicity preservation for termwise skyscraper complexes.
(blueprint: lem-pc-skyscraper-complex-acyclic)
Exactness is checked on sections: opens containing the chosen point reproduce the
original exact sequence, and the other opens give the zero sequence. -/
theorem skyscraper_complex_acyclic (X : RingedSpace.{u_complex}) (x : X)
    (M : CochainComplex (ModuleCat.{u_complex} (X.presheaf.stalk x)) ℤ) :
    M.Acyclic → (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M).Acyclic := by
  classical
  intro hM i
  let F := ringedModuleSkyscraperFunctor X x
  let R := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u_complex} RingCat.{u_complex})).obj X.sheaf
  let U := SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj
  apply U.reflects_exact_of_faithful
  let S := ((((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).sc i).map U)
  change S.Exact
  rw [ShortComplex.exact_iff_isZero_homology, Limits.IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext V
  have hS : (S.map ((CategoryTheory.evaluation _ _).obj V)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro s hs
    have hm := (ShortComplex.moduleCat_exact_iff (M.sc i)).mp (hM i)
    choose t ht using fun h : PLift (x ∈ V.unop) ↦ hm (s h) (by
      exact congrFun hs h)
    exact ⟨t, funext ht⟩
  have hz := (ShortComplex.exact_iff_isZero_homology _).mp hS
  have hz' := hz.of_iso (ShortComplex.mapHomologyIso S
    ((CategoryTheory.evaluation _ _).obj V)).symm
  exact (Limits.IsZero.iff_id_eq_zero _).mp hz'


end SheafOfModules
