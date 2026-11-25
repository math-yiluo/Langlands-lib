/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk

/-!
# Local freeness through the pullback of module objects

`ProEtale.IsLocallyFree` is phrased with the sheaf pullback `mapMod(f^*)`, a module over the
sheaf pullback `f^* Λ_X` of the coefficient ring. This file shows that it suffices that the
pullbacks `f^* M = Λ_Y ⊗_{f^* Λ_X} f^* M` of module objects over the condensed ring `Λ` be free
(`ProEtale.CondensedRing.isLocallyFree_of_isFree_upperStar`), since the coefficient morphism
`α_f : f^* Λ_X ⟶ Λ_Y` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}

variable {Λ} in
/-- A module object whose pullback `f^* M` over `Λ` is free is free as a module over the sheaf
pullback `f^* Λ_X`, in the sense of `ProEtale.IsLocallyFree`. -/
lemma isFree_mapMod_of_isFree_upperStar {Y : Scheme.{u}} (f : Y ⟶ X)
    (h : Mod.IsFree (condensedRingObj Λ Y) ((f)^*⟦Λ⟧.obj M)) :
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ X))
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj M) := by
  obtain ⟨d, ⟨e⟩⟩ := h
  let α := condensedPullbackHom Λ f
  exact ⟨d, ⟨(comapUpperStarObjIso _ f M).symm ≪≫ (Mod.comap α).mapIso e ≪≫
    Mod.finiteFreeIsoMap (Mod.comap α)
      ((Mod.comapCongr (IsIso.inv_inv (f := α)).symm).app _ ≪≫ Mod.regularIsoOfIsIso (inv α)) d⟩⟩

variable {Λ} in
/-- A module object is locally free as soon as its pullbacks over `Λ` to the members of a
pro-étale cover are free. -/
lemma isLocallyFree_of_isFree_upperStar (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, Mod.IsFree (condensedRingObj Λ (𝒰.X i)) ((𝒰.f i)^*⟦Λ⟧.obj M)) :
    IsLocallyFree (condensedRingObj Λ X) M :=
  ⟨𝒰, fun i ↦ isFree_mapMod_of_isFree_upperStar _ (h i)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
