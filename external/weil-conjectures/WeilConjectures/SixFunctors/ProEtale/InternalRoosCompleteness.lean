/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.InternalRoosOutputComplete

/-! # Canonical completeness detected by the internal reduction Roos triangle

Source: Stacks 099B, 0A0E and 0941; blueprint integral-criterion-reductions, final sentence.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.AdicCompletion

/-- A Roos triangle on the actual reductions implies canonical-map completeness.
Source: Stacks 099B, 0A0E, 0941; blueprint integral-criterion-reductions, final sentence
(auxiliary; not a blueprint node).

Proof: choose a K-flat representative P of K. Its strict Roos complex gives a
second distinguished triangle for the same reduction tower. Rotate both triangles:
their first two objects and their first map coincide. Complete the identity maps
to an isomorphism of distinguished triangles, then reflect the isomorphism of their
third objects through the shift equivalence. Thus K is isomorphic to Q(roos P).
The quotient Roos output is complete by the regular-scalar completion reflector.
Compose its K-flat representative isomorphism with this isomorphism to obtain
IsDerivedComplete for K, retaining exactly the same invertible augmentation. No
equality between this triangle isomorphism and the specified augmentation is used. -/
theorem isDerivedComplete_of_roos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K : DerivedCategory (Modules l E X)) [HasProduct (integralLevel l E X K)]
    (δ : (∏ᶜ (integralLevel l E X K)) ⟶ K⟦(1 : ℤ)⟧)
    (hδ : IsDerivedLimitTriangle (integralStep l E X K) K
      (Pi.lift (fun n ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction
        (quotient l E X n)).unit.app K)) δ) :
    IsDerivedComplete l E X K := by
  classical
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have : QuasiIso f := hf
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨p, δ', hT, _⟩ := roos_isDerivedLimit l E X K P hP e
  let unit : K ⟶ ∏ᶜ (integralLevel l E X K) := Pi.lift (fun n ↦
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app K)
  let T := Pretriangulated.Triangle.mk unit
    (towerTransitionEndomorphism (integralStep l E X K)) δ
  let T' := Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism (integralStep l E X K)) δ'
  let i := Pretriangulated.isoTriangleOfIso₁₂ T.rotate T'.rotate
    (Pretriangulated.rot_of_distTriang T hδ)
    (Pretriangulated.rot_of_distTriang T' hT) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
  let k : K ≅ DerivedCategory.Q.obj (roos l E X P) :=
    (shiftFunctor _ (1 : ℤ)).preimageIso (Pretriangulated.Triangle.π₃.mapIso i)
  obtain ⟨Q, hQ, ⟨eQ⟩, hη⟩ := isDerivedComplete_roos l E X P hP
  exact ⟨Q, hQ, ⟨eQ ≪≫ k.symm⟩, hη⟩

end AlgebraicGeometry.ProEtale.AdicCompletion
