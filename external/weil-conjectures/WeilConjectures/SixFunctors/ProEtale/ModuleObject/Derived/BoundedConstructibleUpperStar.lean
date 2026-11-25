/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Pullbacks of constructible module objects

Let `Λ` be a commutative condensed ring and `g : W ⟶ X` a morphism of schemes. The pullback
`g^*` of module objects over `Λ` preserves

* pro-étale local finite presentation
  (`ProEtale.CondensedRing.IsLocallyFinitelyPresented.upperStar`): pull back the pro-étale cover,
  `g^*` preserving finitely presented module objects;
* constructibility (`ProEtale.CondensedRing.IsConstructibleModuleObject.upperStar`, blueprint
  `prop-constructible-pullback`): pull back the stratification;
* bounded constructible complexes, for its left derived functor `Lg^*`
  (`ProEtale.CondensedRing.boundedConstructible_leftDerivedUpperStar_obj_of_scheme`, blueprint
  `proposition-six-operations-dctf`): `Lg^*` commutes with the homology functors.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Finite presentation of the pullback `f^* N` of a module object can be read either over
`f^* Λ_X` or over `Λ_W`, the two being identified by the isomorphism of ring objects
`α_f : f^* Λ_X ⟶ Λ_W`. -/
lemma isFinitelyPresented_mapMod_iff {W X : Scheme.{u}} (f : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.IsFinitelyPresented ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N) ↔
      Mod.IsFinitelyPresented (condensedRingObj Λ W) ((f)^*⟦Λ⟧.obj N) := by
  let α := condensedPullbackHom Λ f
  let e := (Mod.extendScalarsIsoComapInv α).app
    (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N)
  refine ⟨fun h ↦ (h.comap (asIso α).inv).of_iso e.symm, fun h ↦ (h.comap α).of_iso ?_⟩
  exact (Mod.comap α).mapIso e ≪≫ (Mod.comapEquivalenceOfIsIso α).counitIso.app _

/-- The pullbacks of a module object along the two sides of a commutative square
`a ≫ f = b ≫ g` agree: `a^* f^* M ≅ (a ≫ f)^* M = (b ≫ g)^* M ≅ b^* g^* M`. -/
noncomputable def upperStarSquareIso {P U W X : Scheme.{u}} {a : P ⟶ U} {b : P ⟶ W}
    {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (a)^*⟦Λ⟧.obj ((f)^*⟦Λ⟧.obj M) ≅ (b)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M) :=
  ((upperStarComp Λ a f).app M).symm ≪≫ (upperStarCongr Λ h).app M ≪≫
    (upperStarComp Λ b g).app M

/-- Along a commutative square `a ≫ f = b ≫ g`, if `f^* M` is finitely presented, then so is
`b^* g^* M ≅ a^* f^* M`. -/
lemma isFinitelyPresented_upperStar_upperStar_of_comm {P U W X : Scheme.{u}} {a : P ⟶ U}
    {b : P ⟶ W} {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented (condensedRingObj Λ U) ((f)^*⟦Λ⟧.obj M)) :
    Mod.IsFinitelyPresented (condensedRingObj Λ P) ((b)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) :=
  (IsFinitelyPresented.upperStar Λ a hM).of_iso (upperStarSquareIso Λ h M)

/-- The pullback `g^*` of module objects over `Λ` preserves pro-étale local finite presentation:
if `M|_{Uᵢ}` is finitely presented for a pro-étale cover `{Uᵢ ⟶ X}`, then `(g^* M)|_{W ×_X Uᵢ}`
is the pullback of `M|_{Uᵢ}` along `W ×_X Uᵢ ⟶ Uᵢ`, hence finitely presented. -/
lemma IsLocallyFinitelyPresented.upperStar {W X : Scheme.{u}} (g : W ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ X) M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰.pullback₁ g, fun i ↦ ?_⟩
  let a : (𝒰.pullback₁ g).X i ⟶ 𝒰.X i := pullback.snd g (𝒰.f i)
  exact (isFinitelyPresented_mapMod_iff Λ _ _).2
    (isFinitelyPresented_upperStar_upperStar_of_comm Λ (a := a) (b := (𝒰.pullback₁ g).f i)
      pullback.condition.symm
      ((isFinitelyPresented_mapMod_iff Λ _ _).1 (h𝒰 i)))

/-- Along a commutative square `a ≫ f = b ≫ g`, if `f^* M` is pro-étale locally finitely
presented, then so is `b^* g^* M ≅ a^* f^* M`. -/
lemma isLocallyFinitelyPresented_upperStar_upperStar_of_comm {P U W X : Scheme.{u}}
    {a : P ⟶ U} {b : P ⟶ W} {f : U ⟶ X} {g : W ⟶ X} (h : a ≫ f = b ≫ g)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ U) ((f)^*⟦Λ⟧.obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ P) ((b)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) :=
  (IsLocallyFinitelyPresented.upperStar Λ a hM).of_iso (upperStarSquareIso Λ h M)

/-- Blueprint `prop-constructible-pullback`: the pullback `g^*` of module objects over `Λ`
preserves constructibility. If `M` is constructible along a stratification `X = ∐ₐ Xₐ`, then
`g^* M` is constructible along the preimage stratification `W = ∐ₐ W ×_X Xₐ`, the restriction of
`g^* M` to `W ×_X Xₐ` being the pullback of `M|_{Xₐ}`. -/
theorem IsConstructibleModuleObject.upperStar {W X : Scheme.{u}} (g : W ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    IsConstructibleModuleObject (condensedRingObj Λ W) ((g)^*⟦Λ⟧.obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S.pullback g, fun i ↦ ?_⟩
  let a : (S.pullback g).domain i ⟶ S.domain i := pullback.fst (S.immersion i) g
  exact (isLocallyFinitelyPresented_mapMod_iff Λ _ _).2
    (isLocallyFinitelyPresented_upperStar_upperStar_of_comm Λ (a := a)
      (b := (S.pullback g).immersion i) pullback.condition
      ((isLocallyFinitelyPresented_mapMod_iff Λ _ _).1 (hS i)))

/-- Blueprint `proposition-six-operations-dctf` (pullback): the derived pullback `Lg^*` of module
objects over `Λ` along any morphism of schemes `g : W ⟶ X` preserves bounded constructible
complexes. The functor `g^*` being exact, `Lg^*` commutes with the homology functors, and `g^*`
preserves zero objects and constructible module objects. -/
theorem boundedConstructible_leftDerivedUpperStar_obj_of_scheme {W X : Scheme.{u}} (g : W ⟶ X)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : boundedConstructible (condensedRingObj Λ X) K) :
    boundedConstructible (condensedRingObj Λ W) ((L((g)^*⟦Λ⟧)).obj K) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff _ K).1 hK
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨a, b, fun i hi ↦ ?_⟩, fun n ↦ ?_⟩
  · exact ((g)^*⟦Λ⟧.map_isZero (hab i hi)).of_iso
      ((leftDerivedUpperStarHomologyIso Λ g i).app K).symm
  · exact (IsConstructibleModuleObject.upperStar Λ g (hc n)).of_iso
      ((leftDerivedUpperStarHomologyIso Λ g n).app K)

end AlgebraicGeometry.ProEtale.CondensedRing
