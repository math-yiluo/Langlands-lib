/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisCoverTrace
public import WeilConjectures.SixFunctors.ProEtale.UpperStarIsoRestrictionMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# The trace of a Galois covering as a natural transformation, and the monoidal action

For a Galois covering `g : Y ⟶ X` with group `Γ` (`AlgebraicGeometry.ProEtale.IsGaloisAction`),
this file packages the trace `g_* g^* H ⟶ H` of `AlgebraicGeometry.ProEtale.galoisTrace` and the
action of `Γ` on `g_* g^* H` as natural transformations
(`AlgebraicGeometry.ProEtale.galoisTraceNatTrans`,
`AlgebraicGeometry.ProEtale.galoisActionNatTrans`)
of functors on abelian pro-étale sheaves, and
proves:

* the action is monoidal for the lax monoidal structure of `g^* ⋙ g_*`
  (`AlgebraicGeometry.ProEtale.isMonoidal_galoisActionNatTrans`): it is the restriction along the
  automorphisms `V ×_X Y ⟶ V ×_X Y`, conjugated by the monoidal comparison `g^* ≅ j_g^*`;
* the action fixes the unit, the unit is a monomorphism, and the trace factors the norm through
  the unit.

These are the inputs of `CategoryTheory.Adjunction.mapModTrace`, which lifts the trace to module
objects over any coefficient ring.
-/

@[expose] public section

universe u

open CategoryTheory Category MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g] [Surjective g] [QuasiCompact g]
  {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
  [Group Γ] [Fintype Γ] (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b)) (hgal : IsGaloisAction g ρ)

omit [Surjective g] [QuasiCompact g] in
instance isContinuous_baseChangeFunctor :
    (baseChangeFunctor g).IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) :=
  isContinuous_overPullback_comp_overMap g

/-- **The trace of a Galois covering** as a natural transformation `g^* ⋙ g_* ⟶ 𝟭`. -/
@[simps]
noncomputable def galoisTraceNatTrans :
    (g)^*[AddCommGrpCat.{u + 1}] ⋙ (g)_*[AddCommGrpCat.{u + 1}] ⟶ 𝟭 _ where
  app := galoisTrace g hρ hmul hgal
  naturality _ _ φ := galoisTrace_naturality g hρ hmul hgal φ

omit [Surjective g] [QuasiCompact g] in
/-- The restriction along the automorphisms `V ×_X Y ⟶ V ×_X Y`, as a natural transformation of
`j_g^* ⋙ g_*`. -/
noncomputable def galoisActionRestrictionNatTrans (s : Y ⟶ Y) (hs : s ≫ g = g) :
    localizationRestriction AddCommGrpCat.{u + 1} g inferInstance ⋙
        (g)_*[AddCommGrpCat.{u + 1}] ⟶
      localizationRestriction AddCommGrpCat.{u + 1} g inferInstance ⋙
        (g)_*[AddCommGrpCat.{u + 1}] :=
  (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).hom ≫
    Functor.sheafPushforwardContinuousNatTrans (baseChangeAction g s hs) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology X) ≫
    (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g))) AddCommGrpCat.{u + 1}
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).inv


omit [Surjective g] [QuasiCompact g] in
instance isMonoidal_galoisActionRestrictionNatTrans (s : Y ⟶ Y) (hs : s ≫ g = g) :
    NatTrans.IsMonoidal (galoisActionRestrictionNatTrans g s hs) := by
  unfold galoisActionRestrictionNatTrans
  infer_instance


/-- **The action of `a : Γ` on `g_* g^*`**, as a natural transformation. -/
noncomputable def galoisActionNatTrans (a : Γ) :
    (g)^*[AddCommGrpCat.{u + 1}] ⋙ (g)_*[AddCommGrpCat.{u + 1}] ⟶
      (g)^*[AddCommGrpCat.{u + 1}] ⋙ (g)_*[AddCommGrpCat.{u + 1}] :=
  Functor.whiskerRight (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g
      inferInstance).hom (g)_*[AddCommGrpCat.{u + 1}] ≫
    galoisActionRestrictionNatTrans g (ρ a) (hρ a) ≫
    Functor.whiskerRight (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g
      inferInstance).inv (g)_*[AddCommGrpCat.{u + 1}]

omit [Surjective g] [QuasiCompact g] [Group Γ] [Fintype Γ] in
/-- The action of `Γ` on `g_* g^*` is monoidal. -/
instance isMonoidal_galoisActionNatTrans (a : Γ) :
    NatTrans.IsMonoidal (galoisActionNatTrans g hρ a) := by
  unfold galoisActionNatTrans
  infer_instance

omit [Surjective g] [QuasiCompact g] [Group Γ] [Fintype Γ] in
lemma galoisActionNatTrans_app (a : Γ) (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (galoisActionNatTrans g hρ a).app H = galoisAction g hρ a H := by
  simp only [galoisActionNatTrans, galoisAction, NatTrans.comp_app, Functor.whiskerRight_app]
  congr 2
  refine Sheaf.hom_ext ?_
  ext U : 2
  simp only [Functor.comp_obj, galoisActionRestrictionNatTrans,
    Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp, Iso.refl_trans,
    Functor.sheafPushforwardContinuousIso_hom, Iso.refl_inv,
    Functor.sheafPushforwardContinuousIso_inv,
    Iso.refl_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, NatTrans.op_id, ObjectProperty.ι_obj,
    Functor.whiskerRight_id', NatTrans.id_app, Functor.op_obj, Functor.whiskerRight_app,
    NatTrans.op_app, galoisActionRestriction, ObjectProperty.homMk_hom,
    Presheaf.baseChangeAction_app]
  erw [Category.id_comp, Category.comp_id]


omit [Surjective g] [QuasiCompact g] [Group Γ] [Fintype Γ] in
@[reassoc]
lemma localizationRestrictionLowerStarAdjunction_unit_app_comp_galoisActionRestriction (a : Γ)
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g inferInstance).unit.app H ≫
      galoisActionRestriction g hρ a H =
    (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_comp]
  exact Presheaf.baseChangeUnit_comp_baseChangeAction (baseChangeAction_comp_proj g (ρ a) (hρ a)) _

omit [Surjective g] [QuasiCompact g] [Group Γ] [Fintype Γ] in
/-- The action of `Γ` fixes the unit `H ⟶ g_* g^* H`. -/
lemma unit_comp_galoisActionNatTrans (a : Γ) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit ≫ galoisActionNatTrans g hρ a =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit := by
  ext H : 2
  rw [NatTrans.comp_app, galoisActionNatTrans_app, galoisAction]
  erw [upperStarLowerStarAdjunction_unit_app_comp_assoc]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_comp_galoisActionRestriction_assoc]
  erw [← upperStarLowerStarAdjunction_unit_app_comp_assoc g H]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, comp_id]

/-- The trace followed by the unit is the sum of the action of `Γ`. -/
lemma galoisTraceNatTrans_comp_unit :
    galoisTraceNatTrans g hρ hmul hgal ≫
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit =
      ∑ a, galoisActionNatTrans g hρ a := by
  ext H : 2
  simp only [NatTrans.comp_app, NatTrans.app_sum, galoisTraceNatTrans_app, galoisActionNatTrans_app]
  exact galoisTrace_comp_unit g hρ hmul hgal H

/-- The unit followed by the trace is multiplication by the order of `Γ`. -/
lemma unit_comp_galoisTraceNatTrans :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit ≫
      galoisTraceNatTrans g hρ hmul hgal =
      Fintype.card Γ • 𝟙 _ := by
  ext H : 2
  simp only [NatTrans.comp_app, galoisTraceNatTrans_app, NatTrans.app_nsmul, NatTrans.id_app]
  exact unit_comp_galoisTrace g hρ hmul hgal H

omit [Group Γ] [Fintype Γ] in
/-- The unit `H ⟶ g_* g^* H` of a surjective weakly étale `g` is a monomorphism. -/
instance mono_upperStarLowerStarAdjunction_unit_app
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    Mono ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H) := by
  have : Mono ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H).hom :=
    Presheaf.mono_baseChangeUnit (ProEt.topology X) (generate_singleton_baseChangeProj_mem g)
      (isSheaf_comp_forget H)
  have : Mono ((localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g
      inferInstance).unit.app H) := Sheaf.Hom.mono_of_presheaf_mono _ _ _
  have h := upperStarLowerStarAdjunction_unit_app_comp g H
  exact mono_of_mono_fac h

end AlgebraicGeometry.ProEtale
