/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Assembling shifts from an object-covering family of functors

Source: thm-coef-qbar-verdier, proof steps 3--4.
(blueprint: lem-commshift-object-cover-assembly-K6)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory
namespace WeilConjectures.CoefQbarVerdier.ShiftDescent

theorem commShift_ext
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {V : A ⥤ B} (s t : V.CommShift ℤ)
    (h : ∀ n, s.commShiftIso n = t.commShiftIso n) : s = t := by
  cases s
  cases t
  congr
  funext n
  exact h n

/-- Transport shift compatibility along equality of the target shift structures. -/
theorem compatibility_transport
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    {F G : A ⥤ B} [F.CommShift ℤ]
    (s t : G.CommShift ℤ) (h : s = t) (τ : F ⟶ G)
    (hc : letI := t; NatTrans.CommShift τ ℤ) :
    letI := s; NatTrans.CommShift τ ℤ := by
  subst t
  exact hc

def precompShift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (J : A ⥤ B) [J.CommShift ℤ] (V : B ⥤ C) (n : ℤ)
    (e : shiftFunctor B n ⋙ V ≅ V ⋙ shiftFunctor C n) :
    shiftFunctor A n ⋙ (J ⋙ V) ≅ (J ⋙ V) ⋙ shiftFunctor C n :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (J.commShiftIso n) V ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft J e ≪≫
      (Functor.associator _ _ _).symm

theorem precompShift_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (J : A ⥤ B) [J.CommShift ℤ] (V : B ⥤ C) (n : ℤ)
    (e : shiftFunctor B n ⋙ V ≅ V ⋙ shiftFunctor C n) (K : A) :
    (precompShift J V n e).hom.app K =
      V.map ((J.commShiftIso n).hom.app K) ≫ e.hom.app (J.obj K) := by
  simp [precompShift]

theorem precompShift_zero
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (J : A ⥤ B) [J.CommShift ℤ] (V : B ⥤ C) :
    precompShift J V 0 (Functor.CommShift.isoZero V ℤ) =
      Functor.CommShift.isoZero (J ⋙ V) ℤ := by
  ext K
  simp [precompShift_hom, Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app, ← Functor.map_comp_assoc]

theorem precompShift_add
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (J : A ⥤ B) [J.CommShift ℤ] (V : B ⥤ C) (a b : ℤ)
    (ea : shiftFunctor B a ⋙ V ≅ V ⋙ shiftFunctor C a)
    (eb : shiftFunctor B b ⋙ V ≅ V ⋙ shiftFunctor C b) :
    precompShift J V (a + b) (Functor.CommShift.isoAdd ea eb) =
      Functor.CommShift.isoAdd (precompShift J V a ea) (precompShift J V b eb) := by
  ext K
  simp only [precompShift_hom, Functor.commShiftIso_add,
    Functor.CommShift.isoAdd_hom_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  have key := eb.hom.naturality ((J.commShiftIso a).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at key
  rw [← V.map_comp_assoc ((shiftFunctorAdd B a b).inv.app (J.obj K))
    ((shiftFunctorAdd B a b).hom.app (J.obj K)), Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp, reassoc_of% key]

/-- Assemble a specified natural shift family from coherent restrictions.
Source: thm-coef-qbar-verdier, shift descent in steps 3--4
(blueprint: lem-commshift-object-cover-assembly-K6).

Proof: precomposition preserves the zero and addition formulas. At any object,
choose a literal finite-stage presentation. The corresponding restriction has the
required laws. Cancel the mapped inclusion isomorphism to obtain the global laws. -/
@[instance_reducible] def assembleShift
    {I : Type*} {A : I → Type*} [∀ i, Category (A i)]
    {B C : Type*} [Category B] [Category C]
    [∀ i, HasShift (A i) ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (J : ∀ i, A i ⥤ B) [∀ i, (J i).CommShift ℤ]
    (hJ : ∀ P : B, ∃ i K, (J i).obj K = P) (V : B ⥤ C)
    (c : ∀ i, (J i ⋙ V).CommShift ℤ)
    (e : ∀ n : ℤ, shiftFunctor B n ⋙ V ≅ V ⋙ shiftFunctor C n)
    (he : ∀ i n, precompShift (J i) V n (e n) = (c i).commShiftIso n) :
    V.CommShift ℤ where
  commShiftIso := e
  commShiftIso_zero := by
    ext P
    obtain ⟨i, K, rfl⟩ := hJ P
    apply (cancel_epi (V.map (((J i).commShiftIso (0 : ℤ)).hom.app K))).1
    have h := congrArg (fun q ↦ q.hom.app K)
      ((he i 0).trans ((c i).commShiftIso_zero.trans (precompShift_zero (J i) V).symm))
    simpa only [precompShift_hom] using h
  commShiftIso_add a b := by
    ext P
    obtain ⟨i, K, rfl⟩ := hJ P
    apply (cancel_epi (V.map (((J i).commShiftIso (a + b)).hom.app K))).1
    have h : precompShift (J i) V (a + b) (e (a + b)) =
        precompShift (J i) V (a + b) (Functor.CommShift.isoAdd (e a) (e b)) := by
      rw [he, precompShift_add, he, he]
      exact (c i).commShiftIso_add a b
    simpa only [precompShift_hom] using congrArg (fun q ↦ q.hom.app K) h

end WeilConjectures.CoefQbarVerdier.ShiftDescent
