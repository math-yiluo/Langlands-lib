/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CommRingCat
/-- A filtered colimit cocone of domains has a domain as its vertex, transported
along an equality of the vertex with a specified ring.
(blueprint: new-filtered-colimit-domain-cocone)
The proof represents two factors at stages, lifts them to a common stage, and
uses the domain property there; filteredness detects the zero relation later. -/
theorem isDomain_of_filtered_colimit_cocone
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i : I, IsDomain (D.obj i))
    {R : CommRingCat.{u}} (e : c.pt = R) : IsDomain R := by
  subst R
  let : ∀ i : I, IsDomain (D.obj i) := hD
  let : ∀ i : I, Nontrivial (D.obj i) := fun i ↦ inferInstance
  let : Nontrivial c.pt := FilteredColimits.nontrivial hc
  have ht := isColimitOfPreserves (forget CommRingCat) hc
  let : NoZeroDivisors c.pt := ⟨by
    intro x y hxy
    obtain ⟨i, a, b, ha, hb⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ ht x y
    change D.obj i at a b
    change (c.ι.app i).hom a = x at ha
    change (c.ι.app i).hom b = y at hb
    have hab : (c.ι.app i).hom (a * b) = (c.ι.app i).hom 0 := by
      simpa only [map_mul, map_zero, ha, hb] using hxy
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' ht (a * b : D.obj i) (0 : D.obj i)).mp hab
    change (D.map f).hom (a * b) = (D.map f).hom 0 at hf
    have hz : (D.map f).hom a * (D.map f).hom b = 0 := by
      simpa only [map_mul, map_zero] using hf
    rcases mul_eq_zero.mp hz with h | h
    · left
      rw [← ha, ← c.w f]
      change (c.ι.app j).hom ((D.map f).hom a) = 0
      rw [h, map_zero]
    · right
      rw [← hb, ← c.w f]
      change (c.ι.app j).hom ((D.map f).hom b) = 0
      rw [h, map_zero]⟩
  exact NoZeroDivisors.to_isDomain c.pt
end CommRingCat
