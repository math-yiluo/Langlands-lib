/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # CompactSupportRoosTriangleTransport

A proved generic calculation for the compact-support finite action.
(blueprint: lem-weil-compact-support-roos-triangle-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace WeilConjectures

/-- Transport of a specified Roos triangle through compatible tower and vertex isomorphisms.
Source: Stacks Project, Derived limits, Tag 08TC; triangle isomorphism axioms.
(blueprint: lem-weil-compact-support-roos-triangle-transport).
Proof: Construct the product isomorphism from the levelwise isomorphisms. The two
compatibilities give the first two squares of an isomorphism of Roos triangles;
transport the connecting map through the product and vertex isomorphisms.
Distinguished triangles are invariant under this isomorphism. -/
theorem compactSupportRoosTriangleTransport {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X Y : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    {K L : C} (e : K ≅ L) (a : ∀ n, X n ≅ Y n)
    (p : ∀ n, K ⟶ X n) (q : ∀ n, L ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p n ≫ (a n).hom = e.hom ≫ q n)
    (h : ∃ hprod : HasProduct X, letI := hprod
      ∃ δ : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f K (Pi.lift p) δ) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ : (∏ᶜ Y) ⟶ L⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g L (Pi.lift q) δ := by
  obtain ⟨hprod, δ, hδ⟩ := h
  let := hprod
  let : HasProduct Y :=
    hasProduct_of_equiv_of_iso X Y (Equiv.refl ℕ) (fun n ↦ (a n).symm)
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨inferInstance, A.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, ?_⟩
  apply isomorphic_distinguished _ hδ _
  refine Triangle.isoMk _ _ e.symm A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = e.inv ≫ Pi.lift p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using (congrArg (fun k ↦ e.inv ≫ k) (hp n)).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom) ≫
      (shiftFunctor C (1 : ℤ)).map e.inv = A.inv ≫ δ
    simp [Category.assoc, ← Functor.map_comp]

end WeilConjectures
