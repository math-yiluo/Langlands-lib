/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.NoetherianSpace

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Reduced.ReducedSourceFactors
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Finite open filtrations with finite constant models on reduced strata

Source: Stacks Project, Topology, Tag 09Y5
(`lemma-noetherian-partition-refined-by-stratification`), and Pro-etale Cohomology,
Tag 09AH (`lemma-ses-associated-to-open`)
(blueprint: lem-sfb-finite-model-stratum-filtration).
Re-recorded by group NS on 2026-10-18; the statement and constructions are unchanged.

The auxiliary functors name the actual extension-by-zero pieces and closed-stratum
pieces. Cokernels in the functor category express naturality with the opens fixed.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true

universe u

private instance (priority := 2000) essentiallySmallSelfInstance
    (C : Type (u + 1)) [CategoryTheory.Category.{u} C] :
    CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option backward.isDefEq.respectTransparency false in
private theorem pointModulePullbackIso {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((upperStar Λ f).obj (((upperStarFromPoint Z).mapMod Λ).obj P) ≅
      ((upperStarFromPoint Y).mapMod Λ).obj P) := by
  let α := condensedPullbackHom Λ f
  let e := Mod.comapEquivalenceOfIsIso α
  have : (Mod.comap α).Full := e.fullyFaithfulFunctor.full
  have : (Mod.comap α).Faithful := e.fullyFaithfulFunctor.faithful
  let a := Mod.extendRestrictAdjunction α
  have : IsIso a.counit := a.counit_isIso_of_R_fully_faithful
  let eP := (Functor.mapModCompIso (upperStarFromPoint Z)
    (ProEtale.upperStar Ab.{u + 1} f) (upperStarFromPointComp f).hom Λ).app P
  exact ⟨(Mod.extendScalars α).mapIso eP ≪≫ asIso (a.counit.app _)⟩

private theorem finiteModel_of_iso {Y : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
    HasFiniteConstantLocalModel Λ Y N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
  exact ⟨P, hP, ⟨(upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩

private theorem pullback_square_iso {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D)
    (h : a ≫ c = b ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D)) :
    Nonempty ((upperStar Λ a).obj ((upperStar Λ c).obj M) ≅
      (upperStar Λ b).obj ((upperStar Λ d).obj M)) := by
  exact ⟨(upperStarComp Λ a c).symm.app M ≪≫
    (upperStarCongr Λ h).app M ≪≫ (upperStarComp Λ b d).app M⟩

private theorem pullback_model {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D)
    (h : a ≫ c = b ≫ d)
    (M : Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D))
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (e : Nonempty ((upperStar Λ d).obj M ≅ ((upperStarFromPoint C).mapMod Λ).obj P)) :
    Nonempty ((upperStar Λ a).obj ((upperStar Λ c).obj M) ≅
      ((upperStarFromPoint A).mapMod Λ).obj P) := by
  obtain ⟨e⟩ := e
  obtain ⟨es⟩ := pullback_square_iso Λ a b c d h M
  obtain ⟨ep⟩ := pointModulePullbackIso Λ b P
  exact ⟨es ≪≫ (upperStar Λ b).mapIso e ≪≫ ep⟩

private theorem finiteModel_pullback_cover {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Z)
    (𝒱 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (a : 𝒱.I₀ → 𝒰.I₀) (g : ∀ i, 𝒱.X i ⟶ 𝒰.X (a i))
    (w : ∀ i, 𝒱.f i ≫ f = g i ≫ 𝒰.f (a i))
    (h𝒰 : ∀ i, ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
      Nonempty ((upperStar Λ (𝒰.f i)).obj M ≅
        ((upperStarFromPoint (𝒰.X i)).mapMod Λ).obj P)) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M) := by
  refine ⟨𝒱, fun i ↦ ?_⟩
  obtain ⟨P, hP, eP⟩ := h𝒰 (a i)
  exact ⟨P, hP, pullback_model Λ (𝒱.f i) (g i) f (𝒰.f (a i)) (w i) M P eP⟩

private theorem finiteModel_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hM : HasFiniteConstantLocalModel Λ Z M) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  exact finiteModel_pullback_cover Λ f M 𝒰 (𝒰.pullback₂ f) id
    (fun i ↦ pullback.fst (𝒰.f i) f)
    (fun i ↦ (pullback.condition (f := 𝒰.f i) (g := f)).symm) h𝒰

private theorem reduced_factors_immersion {Y Z X : Scheme.{u}} [IsReduced Y]
    (f : Y ⟶ X) (i : Z ⟶ X) [IsImmersion i]
    (h : Set.range f ⊆ Set.range i) : ∃ g : Y ⟶ Z, g ≫ i = f := by
  let f' : Y ⟶ i.coborderRange.toScheme :=
    IsOpenImmersion.lift i.coborderRange.ι f (h.trans (by simpa using! subset_coborder))
  have hf' : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  have h' : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := h (Set.mem_range_self y)
    refine ⟨z, ?_⟩
    apply i.coborderRange.ι.isOpenEmbedding.injective
    change (i.liftCoborder ≫ i.coborderRange.ι) z = (f' ≫ i.coborderRange.ι) y
    rw [i.liftCoborder_ι, hf']
    exact hz
  obtain ⟨g, hg⟩ :=
    (reduced_source_factors_through_closed_subscheme i.liftCoborder f').1.mpr h'
  refine ⟨g, ?_⟩
  rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf']

private theorem finiteModel_on_reduced_substratum {X Y : Scheme.{u}} [IsReduced Y]
    (A : Scheme.Stratification X) (a : Fin A.n) (f : Y ⟶ X)
    (hf : Set.range f ⊆ A.stratum a)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ (A.domain a)
      ((upperStar Λ (A.immersion a)).obj M)) :
    HasFiniteConstantLocalModel Λ Y ((upperStar Λ f).obj M) := by
  obtain ⟨g, hg⟩ := reduced_factors_immersion f (A.immersion a)
    (by rwa [A.range_immersion])
  have h := finiteModel_pullback Λ g _ hM
  apply finiteModel_of_iso Λ ((upperStarComp Λ g (A.immersion a)).symm.app M) at h
  rwa [hg] at h

private theorem noetherian_qc {Y Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y]
    (f : Y ⟶ Z) : QuasiCompact f :=
  ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact (f ⁻¹' U)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
