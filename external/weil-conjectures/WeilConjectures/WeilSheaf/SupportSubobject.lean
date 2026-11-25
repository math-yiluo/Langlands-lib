/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# Supports of subobjects of Weil sheaves

The support of a subobject of a Weil sheaf `G` is contained in the support of `G`, its stalks
being subspaces of those of `G`, and a Weil sheaf with empty support vanishes, the stalks at the
closed points detecting zero objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The support of a subobject of `G` is contained in the support of `G`: the stalks of the
subobject are subspaces of the stalks of `G`. -/
theorem support_subset_of_mono {F G : WeilSheaf k₀ l X} (f : F ⟶ G) [Mono f] :
    F.support ⊆ G.support := fun x hx ↦ by
  have : Nontrivial (F.stalkAt _ _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (X ↘ Spec (CommRingCat.of k₀)) x)).carrier := hx
  exact (injective_stalkAtMap _ _ _ f).nontrivial

/-- A Weil sheaf with empty support vanishes: a nonzero Weil sheaf has a nonzero stalk at some
closed point (`AlgebraicGeometry.WeilSheaf.exists_nontrivial_stalk_of_not_isZero`). -/
theorem isZero_of_support_eq_empty {F : WeilSheaf k₀ l X} (hF : F.support = ∅) : IsZero F := by
  by_contra h
  obtain ⟨x, hx⟩ := F.exists_nontrivial_stalk_of_not_isZero h
  exact (Set.eq_empty_iff_forall_notMem.1 hF) x hx

/-- A Weil sheaf vanishes if and only if its support is empty. -/
theorem isZero_iff_support_eq_empty {F : WeilSheaf k₀ l X} : IsZero F ↔ F.support = ∅ :=
  ⟨support_eq_empty_of_isZero, isZero_of_support_eq_empty⟩

end AlgebraicGeometry.WeilSheaf
