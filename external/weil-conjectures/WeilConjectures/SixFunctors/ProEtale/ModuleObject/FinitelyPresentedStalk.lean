/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Pullbacks of constructible module objects to separably closed points

Let `Λ` be a commutative condensed ring and `Mod_X` the category of `Λ_X`-modules on `X_proét`.

* The pullback `g^* : Mod_Y ⥤ Mod_W` preserves finitely presented module objects
  (`ProEtale.CondensedRing.IsFinitelyPresented.upperStar`), being additive, right exact and
  sending `Λ_Y` to `Λ_W` (`ProEtale.CondensedRing.upperStarObjRegularIso`).
* If the pullback `h^* N` of the sheaf pullback of a module `N` over a ring object `T ≅ Λ_X` is
  finitely presented over `h^* T`, then the pullback `h^* M` on module objects over `Λ` is
  finitely presented over `Λ_Y`
  (`ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_comap_iso`).
* For a separably closed field `Ω`, the pullback of a constructible module object along a point
  `x̄ : Spec Ω ⟶ X` is finitely presented
  (`ProEtale.CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject`):
  `x̄` factors through the stratum `Xₐ` containing its image, then through a member `U` of a
  pro-étale cover of `Xₐ` over which the restriction is finitely presented, every pro-étale
  cover having a section over `Spec Ω`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The pullback of module objects over `Λ` sends the free module `Λ_Y` to the free module
`Λ_W`: it is `α_g : g^* Λ_Y ≅ Λ_W`. -/
noncomputable def upperStarObjRegularIso {W Y : Scheme.{u}} (g : W ⟶ Y) :
    (g)^*⟦Λ⟧.obj (Mod.regular (condensedRingObj Λ Y)) ≅ Mod.regular (condensedRingObj Λ W) :=
  (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).app _ ≪≫
    Mod.regularIsoOfIsIso (condensedPullbackHom Λ g)

/-- The pullback of module objects over `Λ` preserves finitely presented module objects. -/
lemma IsFinitelyPresented.upperStar {W Y : Scheme.{u}} (g : W ⟶ Y)
    {N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (hN : Mod.IsFinitelyPresented (condensedRingObj Λ Y) N) :
    Mod.IsFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj N) :=
  hN.map _ (upperStarObjRegularIso Λ g)

/-- Let `φ : T ⟶ Λ_X` be an isomorphism of ring objects of abelian sheaves on `X_proét`, `M` a
`Λ_X`-module and `N ≅ M` the corresponding `T`-module. If the sheaf pullback `h^* N` is finitely
presented over `h^* T`, then the pullback `h^* M` of module objects over `Λ` is finitely
presented over `Λ_Y`. -/
lemma isFinitelyPresented_upperStar_of_comap_iso {X Y : Scheme.{u}} (h : Y ⟶ X)
    {T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj T]
    (φ : T ⟶ condensedRingObj Λ X) [IsMonHom φ] [IsIso φ]
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : (Mod.comap φ).obj M ≅ N)
    (hN : Mod.IsFinitelyPresented ((h)^*[Ab.{u + 1}].obj T)
      (((h)^*[Ab.{u + 1}].mapMod T).obj N)) :
    Mod.IsFinitelyPresented (condensedRingObj Λ Y) ((h)^*⟦Λ⟧.obj M) := by
  have h₁ := (hN.of_iso ((((h)^*[Ab.{u + 1}]).mapMod T).mapIso e.symm ≪≫
    (Functor.mapModComapIso (h)^*[Ab.{u + 1}] φ).app M)).of_comap ((h)^*[Ab.{u + 1}].map φ)
  exact (h₁.comap (asIso (condensedPullbackHom Λ h)).inv).of_iso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ h)).app _).symm

/-- The restriction `j^* M` of a module object along a morphism `j`, viewed as a module over
the sheaf pullback `j^* Λ_X` along `α_j : j^* Λ_X ≅ Λ_Z`, is the sheaf pullback of `M`. -/
noncomputable def comapUpperStarObjIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.comap (condensedPullbackHom Λ j)).obj ((j)^*⟦Λ⟧.obj M) ≅
      ((j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj M :=
  (Mod.comap (condensedPullbackHom Λ j)).mapIso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)).app _) ≪≫
    ((Mod.comapComp (condensedPullbackHom Λ j) (asIso (condensedPullbackHom Λ j)).inv).app
      _).symm ≪≫
    (Mod.comapCongr (asIso (condensedPullbackHom Λ j)).hom_inv_id).app _ ≪≫ (Mod.comapId _).app _

/-- **Stalks of constructible module objects are finitely presented.** For a separably closed
field `Ω`, the pullback of a constructible `Λ_X`-module along a point `x̄ : Spec Ω ⟶ X` is a
finitely presented `Λ_{Spec Ω}`-module.

The field `Ω` is given as a commutative ring which is a field, so that `Spec (.of Ω)` is formed
with the ring structure of `Ω` itself; this avoids comparing two ring structures on `Ω` inside the
large categories of module objects. -/
theorem isFinitelyPresented_upperStar_of_isConstructibleModuleObject {Ω : Type u} [CommRing Ω]
    (hΩ : IsField Ω) (hsep : letI := hΩ.toField; IsSepClosed Ω) {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) (x : Spec (.of Ω) ⟶ X) :
    Mod.IsFinitelyPresented (condensedRingObj Λ (Spec (.of Ω))) ((x)^*⟦Λ⟧.obj M) := by
  obtain ⟨S, hS⟩ := hM
  have : Nontrivial Ω := ⟨hΩ.exists_pair_ne⟩
  obtain ⟨z⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (x z))
  rw [← S.range_immersion a] at ha
  obtain ⟨y, hy⟩ := Scheme.exists_comp_eq_of_mem_range_of_isField (S.immersion a) hΩ x z ha
  obtain ⟨𝒰, h𝒰⟩ := hS a
  obtain ⟨i, g, hg⟩ := 𝒰.exists_comp_eq_of_isField hΩ hsep y
  have h₁ := isFinitelyPresented_upperStar_of_comap_iso Λ (𝒰.f i)
    (condensedPullbackHom Λ (S.immersion a)) (comapUpperStarObjIso Λ (S.immersion a) M) (h𝒰 i)
  exact (IsFinitelyPresented.upperStar Λ g h₁).of_iso
    ((g)^*⟦Λ⟧.mapIso ((upperStarComp Λ (𝒰.f i) (S.immersion a)).app M).symm ≪≫
      ((upperStarComp Λ g (𝒰.f i ≫ S.immersion a)).app M).symm ≪≫
      eqToIso (congrArg (fun f ↦ (f)^*⟦Λ⟧.obj M) (by rw [reassoc_of% hg, hy])))

end AlgebraicGeometry.ProEtale.CondensedRing
