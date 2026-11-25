/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Flatness over a filtered colimit of commutative rings

Source: Stacks Project, Algebra, Tag 05UU (1), with the module equal to the target ring;
Categories, Tag 0032, for filtered reindexing (blueprint: lem-weil-pbc-colimit-rings-flat).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingHom

/-- A ring map out of a filtered colimit is flat if its composite with every coprojection
is flat. Source: Stacks Project, Algebra, Tag 05UU (1), specialized to the target ring,
and Categories, Tag 0032 (blueprint: lem-weil-pbc-colimit-rings-flat).

Proof:
1. Apply the equational criterion for flatness (Stacks Tag 00HK): it suffices to
   trivialize every finite relation in the target module.
2. Represent its finitely many coefficients at stages of the colimit. Filteredness
   supplies one common stage; transport the representatives there. Naturality of
   the coprojections identifies their images with the original coefficients.
3. The same relation holds in the target viewed as a module over this common stage.
   Flatness of the composite map trivializes this relation over the stage ring.
4. Map the resulting coefficient matrix into the colimit. The equations expressing
   the target elements are unchanged, and the zero coefficient equations map to zero.
   This trivializes the original relation and proves flatness. -/
theorem flat_of_flat_comp_colimit_ι {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] {S : Type v} [CommRing S]
    (ψ : ↥(colimit F) →+* S)
    (hψ : ∀ i : I, (ψ.comp (colimit.ι F i).hom).Flat) : ψ.Flat := by
  classical
  let : Algebra ↥(colimit F) S := ψ.toAlgebra
  change Module.Flat ↥(colimit F) S
  refine Module.Flat.of_forall_isTrivialRelation fun {n r x} hx ↦ ?_
  have reps (k : Fin n) := Concrete.colimit_exists_rep F (r k)
  choose i a ha using reps
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (k : Fin n) : i k ⟶ j := (hj (Finset.mem_image_of_mem i (Finset.mem_univ k))).some
  let b (k : Fin n) : F.obj j := F.map (f k) (a k)
  have hb (k : Fin n) : (colimit.ι F j).hom (b k) = r k := by
    exact (ConcreteCategory.congr_hom (colimit.w F (f k)) (a k)).trans (ha k)
  let : Algebra (F.obj j) S := (ψ.comp (colimit.ι F j).hom).toAlgebra
  have : Module.Flat (F.obj j) S := hψ j
  have hx' : ∑ k, b k • x k = 0 := by
    change ∑ k, ψ ((colimit.ι F j).hom (b k)) * x k = 0
    simpa only [hb, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hx
  obtain ⟨l, c, y, hxy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hx'
  refine ⟨l, fun k t ↦ (colimit.ι F j).hom (c k t), y, ?_, ?_⟩
  · intro k
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hxy k
  · intro t
    simpa only [map_sum, map_mul, map_zero, hb] using
      congrArg (colimit.ι F j).hom (hc t)

end RingHom
