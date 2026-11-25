/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.WeilObject.Sheaf.StalkFrobenius

/-! # Composition of the specified separably closed point trivializations

Source: the composition and source-reparametrization steps of the local Frobenius argument.
(blueprint: lem-wf-condensed-point-trivialization-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified trivializations at a separably closed point respect composition.

Source: pullback-composition paragraph of the current blueprint coefficient construction.
Proof: on a module pulled back from the condensed point, each trivialization is the
specified comparison from that point. Their composition equation is the already proved
pseudonaturality equation for those comparisons. The pullback from the condensed point
is essentially surjective, so the natural endomorphism obtained by dividing the two
comparisons is the identity on every module.
(blueprint: lem-wf-condensed-point-trivialization-composition). -/
theorem sepClosedPointTrivialization_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f g : Spec (.of Ω) ⟶ Spec (.of Ω))
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))) :
    (upperStarComp Λ f g).hom.app N ≫
        (upperStar Λ f).map ((upperStarIsoIdOfIsSepClosed Λ g).hom.app N) ≫
        (upperStarIsoIdOfIsSepClosed Λ f).hom.app N =
      (upperStarIsoIdOfIsSepClosed Λ (f ≫ g)).hom.app N := by
  let τ := upperStarIsoIdOfIsSepClosed Λ (f ≫ g)
  let τc := upperStarComp Λ f g ≪≫
    Functor.isoWhiskerRight (upperStarIsoIdOfIsSepClosed Λ g) (upperStar Λ f) ≪≫
    Functor.leftUnitor (upperStar Λ f) ≪≫ upperStarIsoIdOfIsSepClosed Λ f
  have hA : ∀ A, τc.hom.app ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A) =
      τ.hom.app ((upperStarFromPointMod Λ (Spec (.of Ω))).obj A) := by
    intro A
    simp only [τc, τ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
      Functor.id_obj, Category.id_comp,
      upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod]
    exact upperStarComp_hom_app_comp_upperStarFromPointModComp Λ f g A
  have h := NatTrans.app_eq_id_of_essSurj (upperStarFromPointMod Λ (Spec (.of Ω)))
    (τ.inv ≫ τc.hom) (fun A ↦ by
      simp only [NatTrans.comp_app, hA, Iso.inv_hom_id_app]) N
  have h' : τc.hom.app N = τ.hom.app N := by
    apply (cancel_epi (τ.inv.app N)).1
    simpa only [NatTrans.comp_app, Iso.inv_hom_id_app, Functor.id_obj] using h
  simpa only [τc, τ, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.id_obj, Category.id_comp,
    Category.assoc] using h'

end AlgebraicGeometry.ProEtale.CondensedRing
