/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityBaseChangeNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityCondensedTraceCriterion

/-!
# The carrier of a descended trace

A normalized square of direct-image comparisons identifies the carrier of the
descended trace with the ordinary base-changed trace.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

/-- Conjugating a universal trace by source and target isomorphisms preserves its
universal property. -/
lemma bijective_map_comp_iso_trace
    {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {P P' K : C} {N N' : D} (e : P ≅ P') (e' : N ≅ N')
    (ε : L.obj P' ⟶ N)
    (h : Function.Bijective fun φ : K ⟶ P' ↦ L.map φ ≫ ε) :
    Function.Bijective fun φ : K ⟶ P ↦ L.map φ ≫ L.map e.hom ≫ ε ≫ e'.hom := by
  have he : (fun φ : K ⟶ P ↦ L.map φ ≫ L.map e.hom ≫ ε ≫ e'.hom) =
      (fun ψ ↦ ψ ≫ e'.hom) ∘ (fun φ : K ⟶ P' ↦ L.map φ ≫ ε) ∘
        (fun φ ↦ φ ≫ e.hom) := by
    funext φ
    simp [Functor.map_comp, Category.assoc]
  rw [he]
  exact (e'.homToEquiv).bijective.comp (h.comp (e.homToEquiv).bijective)

/-- Forgetting a descended trace gives the ordinary base-changed trace, conjugated
by the source and target comparison isomorphisms. -/
lemma descendedTrace_forget
    {B B' C C' D D' : Type*}
    [Category B] [Category B'] [Category C] [Category C'] [Category D] [Category D']
    (L₀ : B ⥤ B') (T : B ⥤ C') (S : B' ⥤ D')
    (U : C' ⥤ C) (V : D' ⥤ D) (R : C ⥤ D) (RW : C' ⥤ D')
    (T₀ : B ⥤ C) (S₀ : B' ⥤ D)
    (a : T ⋙ U ≅ T₀) (a' : S ⋙ V ≅ S₀)
    (b : T ⋙ RW ≅ L₀ ⋙ S) (c : RW ⋙ V ≅ U ⋙ R)
    (d : L₀ ⋙ S₀ ≅ T₀ ⋙ R)
    (hd : ∀ P, d.hom.app P = a'.inv.app (L₀.obj P) ≫
      V.map (b.inv.app P) ≫ c.hom.app (T.obj P) ≫ R.map (a.hom.app P))
    {P : B} {N : B'} (ε : L₀.obj P ⟶ N) :
    c.inv.app (T.obj P) ≫ V.map (b.hom.app P ≫ S.map ε) =
      R.map (a.hom.app P) ≫ d.inv.app P ≫ S₀.map ε ≫ a'.inv.app N := by
  have he : d.app P = a'.symm.app (L₀.obj P) ≪≫ V.mapIso (b.symm.app P) ≪≫
      c.app (T.obj P) ≪≫ R.mapIso (a.app P) := by
    apply Iso.ext
    exact hd P
  have hi := congrArg Iso.inv he
  simp only [Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv] at hi
  rw [hi]
  simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  rw [← a'.hom.naturality_assoc]
  simp

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

/-- The invertible adjoint of a trace gives its universal property on every source. -/
lemma bijective_map_comp_of_isIso_homEquiv
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {P : C} {N : D} (ε : L.obj P ⟶ N)
    [IsIso (adj.homEquiv P N ε)] (K : C) :
    Function.Bijective fun φ : K ⟶ P ↦ L.map φ ≫ ε := by
  have he : (fun φ : K ⟶ P ↦ L.map φ ≫ ε) =
      (adj.homEquiv K N).symm ∘ (fun φ ↦ φ ≫ adj.homEquiv P N ε) := by
    funext φ
    apply (adj.homEquiv K N).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply,
      homEquiv_naturality_left]
  rw [he]
  exact (adj.homEquiv K N).symm.bijective.comp
    ((asIso (adj.homEquiv P N ε)).homToEquiv).bijective

end CategoryTheory.Adjunction

namespace CategoryTheory.ObjectProperty

/-- A trace with invertible adjoint on full subcategories is universal on the
underlying morphisms from objects of the source subcategory. -/
lemma bijective_map_comp_hom_of_isIso_homEquiv
    {C D : Type*} [Category C] [Category D] (PC : ObjectProperty C)
    (PD : ObjectProperty D) (L : C ⥤ D) (hL : ∀ K, PC K → PD (L.obj K))
    {R : PD.FullSubcategory ⥤ PC.FullSubcategory}
    (adj : PC.liftFullSubcategory PD L hL ⊣ R)
    {P : PC.FullSubcategory} {N : PD.FullSubcategory}
    (ε : (PC.liftFullSubcategory PD L hL).obj P ⟶ N)
    [IsIso (adj.homEquiv P N ε)] (K : C) (hK : PC K) :
    Function.Bijective fun φ : K ⟶ P.obj ↦ L.map φ ≫ ε.hom := by
  have hb := Adjunction.bijective_map_comp_of_isIso_homEquiv adj ε ⟨K, hK⟩
  constructor
  · intro φ ψ h
    have hh := hb.1 (a₁ := PC.homMk φ) (a₂ := PC.homMk ψ)
      (ObjectProperty.hom_ext _ h)
    exact congrArg InducedCategory.Hom.hom hh
  · intro ψ
    obtain ⟨φ, hφ⟩ := hb.2 (PD.homMk ψ)
    exact ⟨φ.hom, congrArg InducedCategory.Hom.hom hφ⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe u

open Scheme
open scoped CategoryTheory.Obj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}} {s : X ⟶ Spec (.of k)}
  {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y} {h : f ≫ t = s}
  (hc : UpperStarWeilCompatible Λ f h)
  {P : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
  {N : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))}
  (ε : (lowerStar Λ f).rightDerivedFunctor.obj P ⟶ N)

/-- Descend a finite-base direct-image trace using the specified comparison. -/
noncomputable def geometricFiberWeilDirectTrace :
    (geometricFiberMapWeilLowerStar Λ f h).rightDerivedFunctor.obj
      ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj P) ⟶
    (geometricFiberWeilLowerStar Λ t).mapDerivedCategory.obj N :=
  (geometricFiberWeilRightDerivedLowerStarIso hc).hom.app P ≫
    (geometricFiberWeilLowerStar Λ t).mapDerivedCategory.map ε

/-- The geometric carrier of the descended trace is the ordinary base-changed trace. -/
lemma geometricFiberWeilDirectTrace_forget :
    (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
      (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h)).inv.app
        ((geometricFiberWeilLowerStar Λ s).mapDerivedCategory.obj P) ≫
      (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map
        (geometricFiberWeilDirectTrace Λ hc ε) =
    (lowerStar Λ (Scheme.Hom.geometricFiberMap f h)).rightDerivedFunctor.map
      ((Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
        (Endofunctor.IsoAlgebra.forget _)).hom.app P) ≫
      (rightDerivedLowerStarBaseChangeIso Λ
        (Scheme.Hom.isPullback_geometricFiberMap f h).flip).inv.app P ≫
      (upperStar Λ t.geometricFiberProj).mapDerivedCategory.map ε ≫
      (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
        (Endofunctor.IsoAlgebra.forget _)).inv.app N := by
  exact Functor.descendedTrace_forget
    (lowerStar Λ f).rightDerivedFunctor
    (geometricFiberWeilLowerStar Λ s).mapDerivedCategory
    (geometricFiberWeilLowerStar Λ t).mapDerivedCategory
    (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory
    (Endofunctor.IsoAlgebra.forget _).mapDerivedCategory
    (lowerStar Λ (Scheme.Hom.geometricFiberMap f h)).rightDerivedFunctor
    (geometricFiberMapWeilLowerStar Λ f h).rightDerivedFunctor
    (upperStar Λ s.geometricFiberProj).mapDerivedCategory
    (upperStar Λ t.geometricFiberProj).mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ s)
      (Endofunctor.IsoAlgebra.forget _))
    (Functor.mapDerivedCategoryCompIso (geometricFiberWeilLowerStar Λ t)
      (Endofunctor.IsoAlgebra.forget _))
    (geometricFiberWeilRightDerivedLowerStarIso hc)
    (Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _
      (lowerStarGeometricFiberMapCompFrobeniusIso Λ f h))
    (rightDerivedLowerStarBaseChangeIso Λ
      (Scheme.Hom.isPullback_geometricFiberMap f h).flip)
    (geometricFiberWeilRightDerivedLowerStarIso_forget Λ hc) ε

end AlgebraicGeometry.ProEtale.CondensedRing
