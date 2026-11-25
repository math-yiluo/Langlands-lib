/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat

/-! # Totalizing a normalized open tensor comparison

Source: Stacks 012Z and 0GL1.
(blueprint: lem-sf-native-open-tensor-total-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace NativeExtensionDescentProof

/-- A natural sheaf projection comparison totalizes with its prescribed summand formula.

Source: Stacks 012Z and 0GL1; comparisonPrecomposeIso and its insertion equation.
(blueprint: lem-sf-native-open-tensor-total-comparison)

Proof: curry the inverse of the given natural isomorphism and apply the existing
comparisonPrecomposeIso construction. Its naturality in both complexes assembles
these maps into an isomorphism of the uncurried total bifunctors. Invert it.
Postcompose the desired summand equality with the degreewise forward isomorphism;
the insertion equation and the inverse identities prove the resulting equality.
No boundedness or nonzero assumption is used. -/
theorem native_open_tensor_total_comparison
    {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] [HasCountableCoproducts A] [HasCountableCoproducts B]
    (E : A ⥤ B) (R : B ⥤ A) [E.Additive] [R.Additive]
    [PreservesColimitsOfSize.{0, 0} E]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    (g : E.prod (𝟭 _) ⋙ Functor.uncurry.obj H' ≅
      (𝟭 _).prod R ⋙ Functor.uncurry.obj H ⋙ E) :
    ∃ e : (E.mapHomologicalComplex (.up ℤ)).prod (𝟭 _) ⋙
        Functor.uncurry.obj H'.map₂CochainComplex ≅
      (𝟭 _).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj H.map₂CochainComplex ⋙ E.mapHomologicalComplex (.up ℤ),
      ∀ P T (p q n : ℤ) (h : p + q = n),
        HomologicalComplex.ιMapBifunctor
            ((E.mapHomologicalComplex (.up ℤ)).obj P) T H' (.up ℤ) p q n h ≫
            (e.app (P, T)).hom.f n =
          (g.app (P.X p, T.X q)).hom ≫ E.map
            (HomologicalComplex.ιMapBifunctor P
              ((R.mapHomologicalComplex (.up ℤ)).obj T) H (.up ℤ) p q n h) := by
  let τ : (Functor.postcompose₂.obj E).obj
      (H ⋙ (Functor.whiskeringLeft B A A).obj R) ≅
      (((Functor.whiskeringLeft₂ _).obj E).obj (𝟭 _)).obj H' :=
    SheafOfModules.bifunctorIsoOfComponents _ _ (fun M N ↦ g.symm.app (M, N)) (by
      intro M M' N N' a b
      change E.map ((H.map a).app (R.obj N)) ≫ E.map ((H.obj M').map (R.map b)) ≫
          (g.symm.app (M', N')).hom = (g.symm.app (M, N)).hom ≫
          (H'.map (E.map a)).app N ≫ (H'.obj (E.obj M')).map b
      simpa only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj, Iso.app_hom,
        Functor.uncurry_obj_map, Functor.prod_map, Functor.id_map, Functor.id_obj,
        Functor.map_comp, Iso.symm_hom, Iso.app_inv, Category.assoc] using
          g.inv.naturality (Prod.mkHom a b))
  let := SheafOfModules.precompose_preservesZero H R
  let (M : A) := SheafOfModules.precompose_obj_preservesZero H R M
  let (P : CochainComplex A ℤ) (T : CochainComplex B ℤ) :=
    SheafOfModules.precompose_hasTotal H R P T
  let e : (𝟭 (CochainComplex A ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
      Functor.uncurry.obj H.map₂CochainComplex ⋙ E.mapHomologicalComplex (.up ℤ) ≅
      (E.mapHomologicalComplex (.up ℤ)).prod (𝟭 (CochainComplex B ℤ)) ⋙
        Functor.uncurry.obj H'.map₂CochainComplex :=
    NatIso.ofComponents
      (fun PQ ↦ SheafOfModules.comparisonPrecomposeIso E R H H' τ PQ.1 PQ.2)
      (by
        intro PQ PQ' fg
        simpa only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
          Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_map,
          Functor.id_map, Functor.id_obj, Category.assoc,
          Functor.map₂CochainComplex, Functor.map₂HomologicalComplex] using
          SheafOfModules.comparisonPrecomposeIso_map₂_natural E R H H' τ fg.1 fg.2)
  refine ⟨e.symm, fun P T p q n h ↦ ?_⟩
  have hι := SheafOfModules.comparisonPrecomposeIso_ι E R H H' τ P T p q n h
  change HomologicalComplex.ιMapBifunctor
      ((E.mapHomologicalComplex (.up ℤ)).obj P) T H' (.up ℤ) p q n h ≫
      (SheafOfModules.comparisonPrecomposeIso E R H H' τ P T).inv.f n = _
  apply (cancel_mono
    ((SheafOfModules.comparisonPrecomposeIso E R H H' τ P T).hom.f n)).1
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
    Category.comp_id]
  rw [hι]
  simp only [τ, SheafOfModules.bifunctorIsoOfComponents_hom]
  erw [Iso.app_hom, Iso.app_hom, Iso.symm_hom, Iso.hom_inv_id_app_assoc]

end NativeExtensionDescentProof
