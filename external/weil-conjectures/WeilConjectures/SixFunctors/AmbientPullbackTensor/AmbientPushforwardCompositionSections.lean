/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData

/-! # Inverse sections of the selected ambient pushforward comparison

Source: Stacks 03D3, 0941 and fibre-product pasting.
(blueprint: lem-sf-ambient-pushforward-composition-inverse-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

private theorem moduleRestriction_inverse
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules R) {U V : C} (i : U ≅ V) (x : M.obj (op U)) :
    M.map i.hom.op (M.map i.inv.op x) = x := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, i.hom_inv_id, op_id, M.map_id]
  rfl

/-- Inverse comparison restricts by the forward fibre-product comparison.
Source: Stacks 03D3 and 0941
(blueprint: lem-sf-ambient-pushforward-composition-inverse-sections).
Proof: evaluate the specified forward section formula on the inverse image of
x. The isomorphism inverse law identifies the left side with x. Restrict both
sides by the forward fibre-product comparison; the presheaf restriction laws and
the fibre-product inverse law cancel its composite with the inverse comparison.
The resulting equality is the asserted inverse section formula. -/
theorem pushComp_inverse_sections {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) (s : Option ℕ) (M : Modules ell E Z s)
    (U : Site V s) (x : ((push ell E h s ⋙ push ell E k s).obj M).val.obj (op U)) :
    (((pushComp_existsUnique ell E h k s).exists.choose.inv.app M).val.app (op U)) x =
      M.val.map ((baseComp h k s).hom.app U).op x := by
  let e := (pushComp_existsUnique ell E h k s).exists.choose
  have he := (pushComp_existsUnique ell E h k s).exists.choose_spec
  have hh := he M U ((e.inv.app M).val.app (op U) x)
  have hi := congrArg (fun z ↦ z.val.app (op U) x) (e.inv_hom_id_app M)
  change (e.hom.app M).val.app (op U) ((e.inv.app M).val.app (op U) x) = x at hi
  change (e.hom.app M).val.app (op U) ((e.inv.app M).val.app (op U) x) =
    M.val.map ((baseComp h k s).inv.app U).op
      ((e.inv.app M).val.app (op U) x) at hh
  rw [hi] at hh
  have hr := congrArg (fun z ↦ M.val.map
    ((baseComp h k s).hom.app U).op z) hh
  have hc := moduleRestriction_inverse M.val
    ((baseComp h k s).app U)
      ((e.inv.app M).val.app (op U) x)
  exact hc.symm.trans hr.symm

end WeilConjectures.AmbientPullbackTensor
