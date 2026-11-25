/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.SiteInverseImageModuleFlat.SiteInverseImageModuleFlat
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentTensorNormalization

set_option linter.privateModule false

/-! # Flatness of component module pullback

Source: Hemo--Richarz--Scholbach, Construction (4.1) and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v₁ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem preservesFlat_transport
    {C D : Type*} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C]
    [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D] [HasCoequalizers D]
    {F G : C ⥤ D} [bF : F.Braided] [bG : G.Braided]
    (e : F ≅ G) [NatTrans.IsMonoidal e.hom]
    (R : C) [MonObj R] [IsCommMonObj R]
    (S : D) [MonObj S] [IsCommMonObj S]
    (ρ : S ⟶ F.obj R) [IsMonHom ρ] [IsIso ρ]
    (h : ∀ (σ : S ⟶ G.obj R) [IsMonHom σ] [IsIso σ],
      (G.mapMod R ⋙ Mod.comap σ).PreservesFlat) :
    (F.mapMod R ⋙ Mod.comap ρ).PreservesFlat := by
  let i : F.mapMod R ⋙ Mod.comap ρ ≅
      G.mapMod R ⋙ Mod.comap (ρ ≫ e.hom.app R) :=
    Functor.isoWhiskerRight (Functor.mapModNatIso e R) (Mod.comap ρ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (G.mapMod R) (Mod.comapComp ρ (e.hom.app R)).symm
  have hG := h (ρ ≫ e.hom.app R)
  exact ⟨fun {M} hM ↦ ObjectProperty.prop_of_iso _ (i.app M).symm (hG.flat_obj hM)⟩

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

-- Preserve the existing hypotheses although the general site theorem needs fewer of them.
end AlgebraicGeometry.ProEtale.CondensedRing
