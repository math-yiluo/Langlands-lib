/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.AdicFiniteRealization.AdicFiniteRealizationData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Finite free modules on sectionwise pro-etale slices
Source: Stacks Project, Tags 00YV, 03DM and 03DO.
(blueprint: lem-sf-adic-section-slice-freeness).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace WeilConjectures.AdicFiniteRealization

private instance (priority := 20000) siteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private def section_free (X : Scheme.{u}) (A : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (n : ℕ) :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (ProEt.topology X) A).functor.obj (Mod.finiteFree A n) ≅
    SheafOfModules.free (R := (adicLisseForget X).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology X) A)) (ULift.{u + 1} (Fin n)) := by
  let F := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) A).functor
  let := Functor.additive_of_preserves_binary_products F
  letI : PreservesBiproduct (fun _ : Fin n ↦ Mod.regular A) F :=
    preservesBiproduct_of_preservesCoproduct F
  letI : HasFiniteBiproducts (SheafOfModules.{u + 1} ((adicLisseForget X).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) A))) :=
    Abelian.hasFiniteBiproducts
  exact F.mapBiproduct _ ≪≫ biproduct.mapIso
    (fun _ : Fin n ↦ ProEtale.CondensedRing.sectionModuleRegularIso X A) ≪≫
    biproduct.isoCoproduct (fun _ : Fin n ↦ SheafOfModules.unit _) ≪≫
    (Sigma.reindex Equiv.ulift (fun _ : Fin n ↦ SheafOfModules.unit _)).symm

private theorem free_comap_iso {X : Scheme.{u}}
    {A B : Sheaf (ProEt.topology X) Ab.{u + 1}}
    [MonObj A] [MonObj B] (φ : A ⟶ B) [IsMonHom φ] [IsIso φ]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) B) :
    Mod.IsFree A ((Mod.comap φ).obj P) ↔ Mod.IsFree B P := by
  let E := Mod.comapEquivalenceOfIsIso φ
  let := Functor.additive_of_preserves_binary_products E.functor
  let ef (n : ℕ) : E.functor.obj (Mod.finiteFree B n) ≅ Mod.finiteFree A n :=
    E.functor.mapBiproduct (fun _ : Fin n ↦ Mod.regular B) ≪≫
      biproduct.mapIso (fun _ : Fin n ↦
        ((Mod.comapCongr (IsIso.inv_inv (f := φ)).symm).app (Mod.regular B)) ≪≫
          Mod.regularIsoOfIsIso (inv φ))
  constructor
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨E.fullyFaithfulFunctor.preimageIso (en ≪≫ (ef n).symm)⟩⟩
  · rintro ⟨n, ⟨en⟩⟩
    exact ⟨n, ⟨E.functor.mapIso en ≪≫ ef n⟩⟩

/-- Sectionwise free presentations on a pro-etale slice correspond to free internal
inverse images on its scheme. Source: Stacks Project, Tags 00YV, 03DM and 03DO
(blueprint: lem-sf-adic-section-slice-freeness).
Proof: identify the slice site with the small pro-etale site of the chart. The
monoidal restriction comparison identifies the internal pullback with restriction
up to an invertible coefficient map. Reconstructing rings gives the identity on
sections: the unit and tensor comparison equations prove compatibility with one
and multiplication. The same tensor equation proves compatibility with module
actions. The resulting module equivalence preserves the regular module and finite
coproducts. Both this equivalence and the section equivalence are fully faithful,
so free presentations transport in both directions, including rank zero. -/
theorem section_slice_free (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) A) (W : X.ProEt) :
    (∃ n : ℕ, Nonempty
      (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (ProEt.topology X) A).functor.obj P).over W ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj A)
        (((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod A).obj P) := by
  let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale W.hom)
  have : F.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap W.prop
  let G := F.sheafPushforwardContinuous Ab.{u + 1} (ProEt.topology W.left) (ProEt.topology X)
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology X) A
  let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (ProEt.topology W.left) (G.obj A)
  let r : S.obj ⟶ F.op ⋙ R.obj :=
    { app V := @CommRingCat.ofHom (S.obj.obj V) (R.obj.obj (F.op.obj V))
        (S.obj.obj V).commRing (R.obj.obj (F.op.obj V)).commRing
        { toFun := id
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          map_one' := by
            change ((Functor.LaxMonoidal.ε (sheafToPresheaf _ Ab.{u + 1})).app V ≫
              ((η[G.obj A]).hom.app V)).hom (ULift.up 1) = _
            change ((Functor.LaxMonoidal.ε (sheafToPresheaf _ Ab.{u + 1})).app V ≫
              ((Functor.LaxMonoidal.ε G).hom.app V ≫ (G.map η[A]).hom.app V)).hom
                (ULift.up 1) = _
            rw [← Category.assoc]
            erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
              F Ab.{u + 1} (ProEt.topology W.left) (ProEt.topology X) V]
            rfl
          map_mul' := by
            intro a b
            change ((Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab.{u + 1}) _ _).app V ≫
              (μ[G.obj A]).hom.app V).hom (a ⊗ₜ[ℤ] b) = _
            change ((Functor.LaxMonoidal.μ (sheafToPresheaf _ Ab.{u + 1}) _ _).app V ≫
              ((Functor.LaxMonoidal.μ G A A).hom.app V ≫ (G.map μ[A]).hom.app V)).hom
                (a ⊗ₜ[ℤ] b) = _
            rw [← Category.assoc]
            erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
              F Ab.{u + 1} (ProEt.topology W.left) (ProEt.topology X) A A V]
            rfl }
      naturality := by intros; rfl }
  let e := ProEt.sliceEquiv X W
  let : e.inverse.IsDenseSubsite (ProEt.topology W.left) ((ProEt.topology X).over W) :=
    ProEt.sliceDense X W
  let RR := (adicLisseForget X).obj R
  let SS := (adicLisseForget W.left).obj S
  let er (V : W.left.ProEtᵒᵖ) : S.obj.obj V ≃+* (F.op ⋙ R.obj).obj V :=
    { (r.app V).hom with
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let c : SS ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology W.left) ((ProEt.topology X).over W)).obj (RR.over W) := by
    apply ObjectProperty.isoMk
    refine NatIso.ofComponents (fun V ↦
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).mapIso (er V).toCommRingCatIso) ?_
    intro V V' a
    ext x
    rfl
  obtain ⟨q, hq⟩ := ProEt.module_transport
    ((ProEt.topology X).over W) (ProEt.topology W.left) e (RR.over W) SS c
  have hforget (N : SheafOfModules.{u + 1} (RR.over W)) :
      (q.functor.obj N).val = (PresheafOfModules.pushforward c.hom.hom).obj N.val :=
    congrArg (fun F ↦ F.obj N) hq
  let unitIso : SheafOfModules.unit SS ≅ q.functor.obj (SheafOfModules.unit (RR.over W)) := by
    apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    change (SheafOfModules.unit SS).val ≅
      (q.functor.obj (SheafOfModules.unit (RR.over W))).val
    rw [hforget]
    refine PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro a
      ext x
      have h := (r.app V).hom.map_mul a (show S.obj.obj V from x)
      exact h.symm
    · intro V V' a
      ext
      rfl
  let M := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) A).functor.obj P
  let Q := (G.mapMod A).obj P
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology W.left) (G.obj A)
  let em : q.functor.obj (M.over W) ≅ E.functor.obj Q := by
    apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    change (q.functor.obj (M.over W)).val ≅ (E.functor.obj Q).val
    rw [hforget]
    refine PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro a
      ext x
      dsimp only [E, Q, M, InternalAbelianSheafModule.sectionModuleEquivalence,
        InternalAbelianSheafModule.sectionModuleFunctor,
        InternalAbelianSheafModule.presheafModuleFunctor,
        InternalAbelianSheafModule.presheafModules,
        InternalAbelianSheafModule.ordinaryModule,
        InternalAbelianSheafModule.pointwiseMod,
        InternalAbelianSheafModule.sheafModuleInclusion]
      change (((Functor.LaxMonoidal.μ (sheafToPresheaf
          (ProEt.topology W.left) Ab.{u + 1}) (G.obj A) (G.obj P.X)).app V) ≫
          ((Functor.LaxMonoidal.μ G A P.X).hom.app V ≫
            (Mod.act P.X).hom.app (F.op.obj V))).hom (a ⊗ₜ[ℤ] x) =
        ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
          A P.X).app (F.op.obj V) ≫
            (Mod.act P.X).hom.app (F.op.obj V)).hom (a ⊗ₜ[ℤ] x)
      rw [← Category.assoc]
      erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        F Ab.{u + 1} (ProEt.topology W.left) (ProEt.topology X) A P.X V]
      rfl
    · intros
      ext x
      rfl
  have he : (∃ n : ℕ, Nonempty (M.over W ≅
      SheafOfModules.free (ULift.{u + 1} (Fin n)))) ↔ Mod.IsFree (G.obj A) Q := by
    constructor
    · rintro ⟨n, ⟨en⟩⟩
      refine ⟨n, ⟨E.fullyFaithfulFunctor.preimageIso ?_⟩⟩
      exact em.symm ≪≫ q.functor.mapIso en ≪≫
        (SheafOfModules.mapFreeIso q.functor _ unitIso).symm ≪≫ (section_free _ _ n).symm
    · rintro ⟨n, ⟨en⟩⟩
      refine ⟨n, ⟨q.fullyFaithfulFunctor.preimageIso ?_⟩⟩
      exact em ≪≫ E.functor.mapIso en ≪≫ section_free _ _ n ≪≫
        SheafOfModules.mapFreeIso q.functor _ unitIso
  rw [he]
  let τ := ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} W.hom W.prop
  have : NatTrans.IsMonoidal τ.hom := inferInstanceAs
    (NatTrans.IsMonoidal (ProEtale.upperStarIsoSheafPushforward Ab.{u + 1} W.hom W.prop).hom)
  have : IsMonHom (τ.hom.app A) := NatTrans.isMonHom_app τ.hom A
  let ep := (Functor.mapModNatIso τ A).app P
  have hi : Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj A)
      (((ProEtale.upperStar Ab.{u + 1} W.hom).mapMod A).obj P) ↔
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} W.hom).obj A)
        ((Mod.comap (τ.hom.app A)).obj Q) := by
    constructor <;> rintro ⟨n, ⟨en⟩⟩
    · exact ⟨n, ⟨ep.symm ≪≫ en⟩⟩
    · exact ⟨n, ⟨ep ≪≫ en⟩⟩
  exact (hi.trans (free_comap_iso (τ.hom.app A) Q)).symm

end WeilConjectures.AdicFiniteRealization
