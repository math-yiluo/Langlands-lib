/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # CompactSupportRoosTriangleUniqueness

A proved generic calculation for the compact-support finite action.
(blueprint: lem-weil-compact-support-roos-triangle-uniqueness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace WeilConjectures

/-- Two Roos triangles for the same tower have a projection-preserving vertex isomorphism.
Source: Stacks Project, Derived limits, Tag 08TC; triangle isomorphism axioms.
(blueprint: lem-weil-compact-support-roos-triangle-uniqueness).
Proof: Rotate both distinguished triangles, complete the identity maps on the two product
terms to an isomorphism, then unrotate. Its first component preserves the given
projection because the second component is the identity. -/
theorem compactSupportRoosTriangleUniqueness
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : ℕ → C} [HasProduct T] (t : ∀ n, T (n + 1) ⟶ T n)
    {M N : C} (p : M ⟶ ∏ᶜ T) (q : N ⟶ ∏ᶜ T)
    (δ : ∏ᶜ T ⟶ M⟦(1 : ℤ)⟧) (ε : ∏ᶜ T ⟶ N⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle t M p δ) (hq : IsDerivedLimitTriangle t N q ε) :
    ∃ e : M ≅ N, e.hom ≫ q = p := by
  let A := Triangle.mk p (towerTransitionEndomorphism t) δ
  let B := Triangle.mk q (towerTransitionEndomorphism t) ε
  let e := Pretriangulated.isoTriangleOfIso₁₂ A.rotate B.rotate
    (Pretriangulated.rot_of_distTriang A hp)
    (Pretriangulated.rot_of_distTriang B hq) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  let d : A ≅ B :=
    (rotCompInvRot.app A) ≪≫ (Pretriangulated.invRotate C).mapIso e ≪≫
      (rotCompInvRot.app B).symm
  refine ⟨Triangle.π₁.mapIso d, ?_⟩
  have hd : d.hom.hom₂ = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  have h : (Triangle.π₁.mapIso d).hom ≫ q = p ≫ d.hom.hom₂ := d.hom.comm₁.symm
  rw [hd] at h
  exact h.trans (Category.comp_id p)

end WeilConjectures
