/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SupportExchangeOnComponentBdc
public import WeilConjectures.TraceFormula.Specialization.SupportIdentityAbstract
public import WeilConjectures.TraceFormula.Specialization.CompactificationRouteClosedExtension
public import WeilConjectures.TraceFormula.Specialization.FixedSquareClosedExchange
public import WeilConjectures.TraceFormula.Specialization.ComponentUnitClassF

/-!

# The support identity on a component: the generic inputs

The inputs of `CategoryTheory.supportIdentity_aux` which are statements about arbitrary
morphisms of schemes and of models:

* `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map`: the pushforward
  exchange on `Dᵇc` is the ambient one, through the compatibility isomorphisms;
* `ProEtale.CondensedRing.eqToHom_comp_map_lowerStarComp_inv`: the composition isomorphism of the
  pushforwards on `Dᵇc`, transported along equal morphisms, is the ambient one;
* `ProEtale.CondensedRing.compactificationRoute_ambient_eq_fixedSquareRoute_of_eq`: the
  agreement of the two routes for a morphism `g` equal to `j ≫ ι`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

section Exchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- The pushforward exchange on `Dᵇc` is the ambient one, through the (identity) compatibility
isomorphisms of the restricted functors with the inclusions. -/
theorem NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_map
    (K : Dᵇc(X.left)⟦Λℓ⟧) :
    (boundedConstructible _).ι.map ((φ.boundedConstructiblePushforwardExchange ℓ hM hN).app K) =
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hN).hom.app
          ((boundedConstructibleLowerStar ℓ f).obj K) ≫
        (N.nearbyCycles Λℓ).map ((boundedConstructibleLowerStarCompatibility ℓ f).hom.app K) ≫
        (φ.pushforwardExchange Λℓ).app K.obj ≫
        R((f'.left)_*⟦Λℓ⟧).map
          ((NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hM).inv.app K) ≫
        (boundedConstructibleLowerStarCompatibility ℓ f').inv.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj K) := by
  simp only [boundedConstructibleLowerStarCompatibility,
    NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact φ.boundedConstructiblePushforwardExchange_app_hom ℓ hM hN K

end Exchange

section Comp

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {B X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The inverse composition isomorphism `R(f₁ ≫ Δ)_* ≅ RΔ_* Rf₁_*` on `Dᵇc`, transported along
`f₁ = f₂` and preceded by an `eqToHom`, is the ambient composition isomorphism of a factorization
`f₂ ≫ Δ = phg`, through the compatibility isomorphisms. -/
lemma eqToHom_comp_map_lowerStarComp_inv (f₁ f₂ : B ⟶ X) (hf : f₁ = f₂) (Δ : X ⟶ Y)
    {phg : B.left ⟶ Y.left} (hp : f₂.left ≫ Δ.left = phg) (K : Dᵇc(B.left)⟦Λℓ⟧)
    (hE : R((phg)_*⟦Λℓ⟧).obj ((boundedConstructible _).ι.obj K) =
      (boundedConstructible _).ι.obj ((boundedConstructibleLowerStar ℓ (f₁ ≫ Δ)).obj K)) :
    eqToHom hE ≫ (boundedConstructible _).ι.map
        ((boundedConstructibleLowerStarComp ℓ f₁ Δ).inv.app K ≫
          (boundedConstructibleLowerStar ℓ Δ).map (eqToHom (by rw [hf]))) =
      (lowerStarCompOfEq (Λ := Λℓ) hp).hom.app ((boundedConstructible _).ι.obj K) ≫
        R((Δ.left)_*⟦Λℓ⟧).map ((boundedConstructibleLowerStarCompatibility ℓ f₂).inv.app K) ≫
        (boundedConstructibleLowerStarCompatibility ℓ Δ).inv.app
          ((boundedConstructibleLowerStar ℓ f₂).obj K) := by
  subst hf hp
  have h := boundedConstructibleLowerStarComp_inv_app_hom ℓ f₁ Δ K
  have hE' : eqToHom hE = 𝟙 _ := rfl
  rw [hE', Category.id_comp, eqToHom_refl, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simp only [boundedConstructibleLowerStarCompatibility, ObjectProperty.liftCompιIso,
    Iso.refl_inv, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  exact h

end Comp


section Route

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {B F C P X Y : Over (Spec (.of k))} [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
  [IsSeparated B.hom] [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- `compactificationRoute_ambient_eq_fixedSquareRoute'` for a morphism `g` equal to `j ≫ ι`
(e.g. the special component `B'' ⟶ C'` of a morphism of models, through `B'' ⟶ F'`), with the
composition isomorphism `Rι_* Rj_* ≅ Rg_*` of `boundedConstructibleLowerStarCompOfEq`. -/
theorem compactificationRoute_ambient_eq_fixedSquareRoute_of_eq (j : B ⟶ F) {ι : F ⟶ C}
    {g : B ⟶ C} (wg : j ≫ ι = g) {c : C ⟶ Y} {d : F ⟶ X} {Δ : X ⟶ Y} (sq : ι ≫ c = d ≫ Δ)
    (h : C ⟶ P) (p : P ⟶ Y) [IsOpenImmersion h.left] [IsProper p.left] (w : h ≫ p = c)
    [IsProper ι.left] [IsProper Δ.left] [IsProper j.left] [IsProper g.left]
    [IsProper (j ≫ d).left] [IsProper ((j ≫ d) ≫ Δ).left] [IsProper (g ≫ c).left]
    [IsProper (g ≫ h).left] [IsProper ((g ≫ h) ≫ p).left] (N : Dᵇc(B.left)⟦Λℓ⟧)
    (hE : R(((g.left ≫ h.left) ≫ p.left)_*⟦Λℓ⟧).obj N.obj =
      ((boundedConstructibleLowerStar ℓ ((j ≫ d) ≫ Δ)).obj N).obj) :
    (boundedConstructible _).ι.map ((boundedConstructibleLowerShriek ℓ c).map
        ((boundedConstructibleLowerStarCompOfEq ℓ j ι wg).hom.app N)) ≫
      (boundedConstructible _).ι.map ((compactificationLowerShriekIso ℓ h p w).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      (boundedConstructibleLowerStarCompatibility ℓ p).hom.app
        ((boundedConstructibleOpenImmersionLowerShriek Λℓ ℓ h).obj
          ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R((p.left)_*⟦Λℓ⟧).map
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ h).hom.app
        ((boundedConstructibleLowerStar ℓ g).obj N)) ≫
      R((p.left)_*⟦Λℓ⟧).map (D((h.left)_!open⟦Λℓ⟧).map
        ((boundedConstructibleLowerStarCompatibility ℓ g).hom.app N)) ≫
      R((p.left)_*⟦Λℓ⟧).map ((closedExtension (openImmersionAdjunction ℓ h.left)
        (rfl : g.left ≫ h.left = _)).app N.obj) ≫
      (lowerStarCompOfEq (Λ := Λℓ) (rfl : (g.left ≫ h.left) ≫ p.left = _)).inv.app N.obj ≫
      eqToHom hE =
    ((lowerStarLowerShriekCompIso ℓ sq).hom.app ((boundedConstructibleLowerStar ℓ j).obj N) ≫
      (boundedConstructibleLowerStar ℓ Δ).map
        ((boundedConstructibleLowerShriek ℓ d).map
            ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ j).inv.app N) ≫
          (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j d).inv.app N ≫
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (j ≫ d)).hom.app N) ≫
      (boundedConstructibleLowerStarComp ℓ (j ≫ d) Δ).hom.app N).hom := by
  subst wg
  have hr := compactificationRoute_ambient_eq_fixedSquareRoute' ℓ j sq h p w N
  have hc : (boundedConstructibleLowerStarCompOfEq ℓ j ι rfl).hom.app N =
      (boundedConstructibleLowerStarComp ℓ j ι).hom.app N := by
    simp [boundedConstructibleLowerStarCompOfEq]
  rw [hc]
  exact hr

end Route

end AlgebraicGeometry.ProEtale.CondensedRing
