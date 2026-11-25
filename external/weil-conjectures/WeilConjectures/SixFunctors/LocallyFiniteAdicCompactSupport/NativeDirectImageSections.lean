/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import WeilConjectures.SixFunctors.ProEtale.Adic.SectionAction

/-! # Native direct image on sections

Source: Stacks, Tag 03D6; Bhatt--Scholze, Section 6.8.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
variable (l : ℕ) [Fact l.Prime]

open CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
open scoped TensorProduct

private theorem section_smul (T : Scheme.{u}) [IsCommMonObj (abRing l T)]
    (M : ProEtale.AdicSheaf l T) (W : T.ProEtᵒᵖ)
    (r : (ringSheaf l T).obj.obj W) (m : ((sections l T).obj M).val.obj W) :
    ((ModuleCat.smul (((sections l T).obj M).val.obj W) r).asHom.hom) m =
      ProEtale.AdicSheaf.sectionAct M r m := by
  let F := ProEtale.weilCoefficientsForgetAb l T
  let I := sheafToPresheaf (ProEt.topology T) Ab.{u + 1}
  have h := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafCompose
    (ProEt.topology T) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})
    (ProEtale.adicConstantSheaf l T) M.X) W
  simp only [NatTrans.comp_app] at h
  change ((μ I (F.obj (ProEtale.adicConstantSheaf l T)) (F.obj M.X)).app W ≫
    (μ F (ProEtale.adicConstantSheaf l T) M.X).hom.app W ≫
    (F.map (Mod.act M.X)).hom.app W).hom (r ⊗ₜ[ℤ] m) = _
  erw [← Category.assoc, h]
  rfl

private theorem lower_sectionAct {U V : Scheme.{u}} (g : U ⟶ V)
    (M : ProEtale.AdicSheaf l U) (W : V.ProEtᵒᵖ)
    (r : (ProEtale.adicConstantSheaf l V).obj.obj W)
    (m : M.X.obj.obj ((proEtaleBaseChange g).op.obj W)) :
    ProEtale.AdicSheaf.sectionAct ((ProEtale.adicLowerStar l g).obj M) r m =
      ProEtale.AdicSheaf.sectionAct M
        ((ProEtale.adicConstantSheafToLowerStar l g).hom.app W r) m := by
  let I := sheafToPresheaf (ProEt.topology V) (WeilCoefficients.{u} l)
  let P := ProEtale.lowerStar (WeilCoefficients.{u} l) g
  let ψ := ProEtale.adicConstantSheafToLowerStar l g
  have hn := congr_app (μ_natural_left I ψ (P.obj M.X)) W
  simp only [NatTrans.comp_app] at hn
  have ht := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (proEtaleBaseChange g) (WeilCoefficients.{u} l)
    (ProEt.topology V) (ProEt.topology U) (ProEtale.adicConstantSheaf l U) M.X W
  change ((μ I (ProEtale.adicConstantSheaf l V) (P.obj M.X)).app W ≫
    (ψ ▷ P.obj M.X).hom.app W ≫ (μ P (ProEtale.adicConstantSheaf l U) M.X).hom.app W ≫
    (P.map (Mod.act M.X)).hom.app W) (r ⊗ₜ m) = _
  erw [← reassoc_of% hn, reassoc_of% ht]
  rfl

/-- The native and ringed direct images have the same sections and scalar action.
Source: Stacks, Tag 03D6, and Bhatt--Scholze, Section 6.8.
(blueprint: lem-sf-native-direct-image-sections).

Proof: evaluate the two functors at an adic module M and a test object W over V.
Both underlying groups are M evaluated at W times_V U, with the same restriction maps.
The internal pushforward action is the pushforward tensorator followed by the action
of M, with scalars restricted along the native precomposition map. The tensorator
formula on pure section tensors makes this exactly the sectionwise action of the
ringed direct image. The hypothesis pull_normalized identifies its structural ring map
with precomposition. The identity underlying maps are consequently linear in both
directions, natural in W and M, and inverse. Uniqueness follows by extensionality on
M, W and sections. The zero module and empty test objects require no exception. -/
theorem native_direct_image_sections [N : NativeRings.{u} l]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ∃! c : ProEtale.adicLowerStar l g ⋙ sections l V ≅ sections l U ⋙
        proEtaleRingModuleDirectImage g (ringSheaf l V) (ringSheaf l U) (N.pull g),
      ∀ (M : ProEtale.AdicSheaf l U) (W : V.ProEtᵒᵖ)
        (m : ((sections l V).obj ((ProEtale.adicLowerStar l g).obj M)).val.obj W),
        HEq (((c.hom.app M).val.app W) m) m := by
  classical
  let L := ProEtale.adicLowerStar l g ⋙ sections l V
  let R := sections l U ⋙
    proEtaleRingModuleDirectImage g (ringSheaf l V) (ringSheaf l U) (N.pull g)
  have h (M : ProEtale.AdicSheaf l U) (W : V.ProEtᵒᵖ)
      (r : (ringSheaf l V).obj.obj W) (m : (L.obj M).val.obj W) :
      ((ModuleCat.smul ((L.obj M).val.obj W) r).asHom.hom) m =
        ((ModuleCat.smul ((R.obj M).val.obj W) r).asHom.hom) m := by
    erw [section_smul l V ((ProEtale.adicLowerStar l g).obj M) W r m,
      lower_sectionAct]
    let s := (proEtaleRingDirectImageMap g (ringSheaf l V) (ringSheaf l U)
      (N.pull g)).hom.app W r
    change _ = ((ModuleCat.smul
      (((sections l U).obj M).val.obj ((proEtaleBaseChange g).op.obj W)) s).asHom.hom) m
    erw [section_smul]
    congr 1
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact (N.pull_normalized g W r x).symm
  let q (M) : L.obj M ⟶ R.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (L.obj M).val) (M₂ := (R.obj M).val)
      (𝟙 _) (fun W r m ↦ h M W r m)⟩
  let p (M) : R.obj M ⟶ L.obj M :=
    ⟨PresheafOfModules.homMk (M₁ := (R.obj M).val) (M₂ := (L.obj M).val)
      (𝟙 _) (fun W r m ↦ (h M W r m).symm)⟩
  let c : L ≅ R := NatIso.ofComponents
    (fun M ↦ { hom := q M, inv := p M,
               hom_inv_id := by ext W m; rfl,
               inv_hom_id := by ext W m; rfl })
    (fun f ↦ by ext W m; rfl)
  refine ⟨c, ?_, ?_⟩
  · intro M W m
    rfl
  · intro d hd
    apply Iso.ext
    ext M W m
    exact eq_of_heq (hd M W m)

end WeilConjectures.LocallyFiniteAdicCompactSupport
