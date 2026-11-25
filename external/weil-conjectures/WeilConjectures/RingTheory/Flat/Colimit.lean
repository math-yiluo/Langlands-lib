/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness over a filtered colimit of rings

If `R = colim_i R_i` is a filtered colimit of commutative rings and `ψ : R → S` is a ring map such
that every composite `R_i → R → S` is flat, then `ψ` is flat.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace RingHom

/-- Let `R = colim_i R_i` be a filtered colimit of commutative rings and `ψ : R → S` a ring map
such that each composite `R_i → R → S` is flat. Then `ψ` is flat.
(blueprint: `lem-weil-pbc-colimit-rings-flat`) -/
theorem Flat.of_isColimit_of_forall_comp {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c) {S : CommRingCat.{u}}
    (ψ : c.pt ⟶ S) (h : ∀ j, (c.ι.app j ≫ ψ).hom.Flat) : ψ.hom.Flat := by
  have : PreservesFilteredColimits (forget CommRingCat.{u}) :=
    comp_preservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat)
  algebraize [ψ.hom]
  refine Module.Flat.iff_forall_isTrivialRelation.mpr fun {l f x} hfx ↦ ?_
  choose j a ha using fun i ↦ Concrete.isColimit_exists_rep F hc (f i)
  let K := IsFiltered.cocone (Discrete.functor j)
  let b : Fin l → F.obj K.pt := fun i ↦ F.map (K.ι.app ⟨i⟩) (a i)
  have hb : ∀ i, c.ι.app K.pt (b i) = f i := by
    intro i
    rw [← ha i]
    exact congr($(c.w (K.ι.app ⟨i⟩)).hom (a i))
  have hk := h K.pt
  algebraize [(c.ι.app K.pt ≫ ψ).hom]
  have hrel : ∑ i, b i • x i = 0 := by
    rw [← hfx]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, Algebra.smul_def, ← hb i]
    rfl
  obtain ⟨m, a', y, hy, ha'⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨m, fun i t ↦ c.ι.app K.pt (a' i t), y, fun i ↦ ?_, fun t ↦ ?_⟩
  · rw [hy i]
    rfl
  · have h0 := congr((c.ι.app K.pt).hom $(ha' t))
    simp only [map_sum, map_mul, map_zero] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hb i]

end RingHom
