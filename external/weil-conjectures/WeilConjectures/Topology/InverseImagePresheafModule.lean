/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Module.TransferInstance
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Modules on the presheaf inverse image

This is the filtered-colimit step of Stacks Tag 008T, before sheafification.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

set_option quotPrecheck false in
local notation "L" A => (Opens.map f).op.lan (H := A)

/-- The presheaf inverse image of a module has section module structures over the
presheaf inverse image ring, with semilinear restrictions and semilinear Lan unit.
Source: Stacks Tag 008T, lemma-pullback-presheaf-module.
Proof: apply the existing concrete presheaf-module pullback adjunction theorem,
whose coprojection formula is the multiplication on filtered-colimit representatives.
Its underlying abelian presheaf is naturally isomorphic to the Lan of the original
abelian presheaf. On each open, use the inverse of that isomorphism as an additive
equivalence to transport the section module structure back to the Lan carrier.
The equivalence carries a transported scalar product to the original scalar product.
Its naturality and the semilinear restrictions of the module presheaf therefore imply
semilinearity of the transported restrictions, by injectivity of the equivalence.
For the unit, apply the coprojection formula on the inverse image of the source open,
where the final restriction is the identity. The same injectivity gives semilinearity
of the Lan unit. No assumption on nonemptiness of an open is made.
(blueprint: lem-pc-inverse-image-presheaf-module). -/
theorem exists_inverseImagePresheafModuleInstances
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ∃ d : ∀ U : (Opens X)ᵒᵖ,
      Module (((L CommRingCat.{u}).obj R.obj).obj U)
        (((L AddCommGrpCat.{u}).obj M.val.presheaf).obj U),
      (letI := d
       ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) r m,
         ((L AddCommGrpCat.{u}).obj M.val.presheaf).map i (r • m) =
           ((L CommRingCat.{u}).obj R.obj).map i r •
             ((L AddCommGrpCat.{u}).obj M.val.presheaf).map i m) ∧
      (letI := d
       ∀ (V : (Opens Y)ᵒᵖ) (r : R.obj.obj V) (m : M.val.obj V),
         (((Opens.map f).op.lanAdjunction AddCommGrpCat.{u}).unit.app
           M.val.presheaf).app V (r • m) =
         @SMul.smul _ _ (d ((Opens.map f).op.obj V)).toSMul
           ((((Opens.map f).op.lanAdjunction CommRingCat.{u}).unit.app R.obj).app V r)
           ((((Opens.map f).op.lanAdjunction AddCommGrpCat.{u}).unit.app
             M.val.presheaf).app V m)) := by
  obtain ⟨P, e, _adj, hact, _huniq, _hadj⟩ :=
    PresheafOfModules.topologicalPullbackAdjunction f R.obj
  let (U : (Opens X)ᵒᵖ) :
      Module (((L CommRingCat.{u}).obj R.obj).obj U) ((P.obj M.val).obj U) :=
    ((P.obj M.val).obj U).isModule
  let t (U : (Opens X)ᵒᵖ) :
      (((L AddCommGrpCat.{u}).obj M.val.presheaf).obj U) ≃+ ((P.obj M.val).obj U) :=
    ((e.app M.val).app U).symm.addCommGroupIsoToAddEquiv
  let d (U : (Opens X)ᵒᵖ) := (t U).module
    (((L CommRingCat.{u}).obj R.obj).obj U)
  have he (U : (Opens X)ᵒᵖ) (r : ((L CommRingCat.{u}).obj R.obj).obj U)
      (m : ((L AddCommGrpCat.{u}).obj M.val.presheaf).obj U) :
      t U (@SMul.smul _ _ (d U).toSMul r m) = r • t U m := by
    exact (t U).apply_symm_apply _
  have hn {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
      (m : ((L AddCommGrpCat.{u}).obj M.val.presheaf).obj U) :
      t V (((L AddCommGrpCat.{u}).obj M.val.presheaf).map i m) =
        (P.obj M.val).map i (t U m) := by
    exact NatTrans.naturality_apply (e.app M.val).inv i m
  refine ⟨d, ?_, ?_⟩
  · intro U V i r m
    apply (t V).injective
    exact (hn i _).trans ((congrArg ((P.obj M.val).map i) (he U r m)).trans
      (((P.obj M.val).map_smul i r _).trans
        ((he V _ _).trans (congrArg
          (fun z ↦ ((L CommRingCat.{u}).obj R.obj).map i r • z) (hn i m))).symm))
  · intro V r m
    apply (t ((Opens.map f).op.obj V)).injective
    rw [he]
    simp only [Functor.op_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      Functor.id_obj, Functor.whiskeringLeft_obj_obj, PresheafOfModules.presheaf_obj_coe,
      Functor.lanAdjunction_unit]
    have hh := (hact M.val ((Opens.map f).obj V.unop) V.unop le_rfl r m).symm
    simp only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
      PresheafOfModules.toPresheaf_obj_coe, Iso.app_inv, op_unop,
      PresheafOfModules.presheaf_obj_coe, PresheafOfModules.topologicalPullbackSectionMap,
      TopCat.Presheaf.pushforward_obj_obj, Functor.id_obj,
      TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit,
      Functor.op_obj, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      Category.comp_id] at hh
    exact hh

end
end TopCat.Sheaf
