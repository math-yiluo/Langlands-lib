/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisActionSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransportInputs

/-!
# The Galois action on module objects is the unit transport

For a Galois covering `g : Y ⟶ X` with action `ρ`, the action `galoisAction Λ g hρ σ` of `σ` on
`g_* g^*` of module objects over `Λ` is the unit transport along `ρ σ`
(`ProEtale.CondensedRing.galoisAction_eq_unitTransport`). Since the forgetful functor from module
objects to sheaves is faithful, this is checked on underlying sheaves, where both sides are, up to
the identifications `upperStarForgetIso`, the corresponding constructions for sheaves
(`ProEtale.CondensedRing.forget_map_galoisAction_app`,
`ProEtale.CondensedRing.forget_map_unitTransport_app`), identified by
`ProEtale.galoisAction_eq_unitTransport`.

As a consequence the splitting of the pullback exchange of a finite Galois layer by the averaged
action on nearby cycles holds without hypotheses
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_autAction`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- The composition isomorphism of pushforwards of module objects is, on underlying sheaves, the
composition isomorphism of pushforwards of sheaves. -/
lemma forget_map_lowerStarComp_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((lowerStarComp Λ f g).hom.app N) =
      (ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app N.X := by
  rfl

/-- The comparison `mapModCompToUpperStarLowerStar` is, on underlying sheaves, `g_*` of the
identification `upperStarForgetIso`. -/
lemma forget_map_mapModCompToUpperStarLowerStar_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((mapModCompToUpperStarLowerStar Λ g).app M) =
      (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M) := by
  rfl

/-- The Galois action on module objects is, on underlying sheaves, the Galois action on sheaves,
through the identification `upperStarForgetIso`. -/
lemma forget_map_galoisAction_app {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    [Surjective g] [QuasiCompact g] {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
    (a : Γ) (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((galoisAction Λ g hρ a).app M) =
      (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M) ≫
        ProEtale.galoisAction g hρ a M.X ≫
        (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M) := by
  rw [← cancel_epi ((g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M)),
    ← forget_map_mapModCompToUpperStarLowerStar_app, ← Functor.map_comp, galoisAction]
  simp only [NatTrans.comp_app, NatIso.isIso_inv_app, IsIso.hom_inv_id_assoc, Functor.map_comp,
    forget_map_mapModCompToUpperStarLowerStar_app]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← galoisActionNatTrans_app]
  rfl

omit [IsCommMonObj Λ] in
/-- The pushforward of module objects is, on underlying sheaves, the pushforward of sheaves. -/
lemma forget_map_lowerStar_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N N' : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} (φ : N ⟶ N') :
    (Mod.forget _).map ((f)_*⟦Λ⟧.map φ) = (f)_*[Ab.{u + 1}].map ((Mod.forget _).map φ) :=
  rfl

/-- The inverse composition isomorphism of pullbacks of module objects, on underlying sheaves,
through the identifications `upperStarForgetIso`. -/
lemma forget_map_upperStarComp_inv_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (Mod.forget _).map ((upperStarComp Λ f g).inv.app M) =
      (upperStarForgetIso Λ f).inv.app ((g)^*⟦Λ⟧.obj M) ≫
        (f)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M) ≫
        (ProEtale.upperStarComp Ab.{u + 1} f g).inv.app ((Mod.forget _).obj M) ≫
        (upperStarForgetIso Λ (f ≫ g)).hom.app M := by
  have h := upperStarComp_hom_app_upperStarForgetIso Λ f g M
  have h' : (Mod.forget _).map ((upperStarComp Λ f g).hom.app M) =
      (upperStarForgetIso Λ (f ≫ g)).inv.app M ≫
        (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app ((Mod.forget _).obj M) ≫
        (f)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M) ≫
        (upperStarForgetIso Λ f).hom.app ((g)^*⟦Λ⟧.obj M) := by
    rw [h, Iso.inv_hom_id_app_assoc]
  rw [← cancel_epi ((Mod.forget _).map ((upperStarComp Λ f g).hom.app M)), ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, h']
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    Iso.inv_hom_id_app]
  rfl

/-- **The unit transport of module objects on underlying sheaves** is the unit transport of
sheaves, through the identifications `upperStarForgetIso`. -/
lemma forget_map_unitTransport_app {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((unitTransport Λ s (p₁ := s ≫ g) (q₁ := s ≫ g) rfl rfl).app M) =
      (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M) ≫
        (g)_*[Ab.{u + 1}].map ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} s).unit.app
          ((g)^*[Ab.{u + 1}].obj M.X)) ≫
        (ProEtale.lowerStarComp Ab.{u + 1} s g).hom.app _ ≫
        (s ≫ g)_*[Ab.{u + 1}].map ((ProEtale.upperStarComp Ab.{u + 1} s g).inv.app M.X) ≫
        (s ≫ g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ (s ≫ g)).hom.app M) := by
  simp only [unitTransport, eqToHom_refl, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.comp_id, Functor.map_comp, forget_map_lowerStar_map,
    forget_map_upperStarLowerStarAdjunction_unit_app', forget_map_lowerStarComp_hom_app,
    forget_map_upperStarComp_inv_app, lowerStarForgetIso, Iso.refl_hom, NatTrans.id_app,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have h1 := (ProEtale.lowerStarComp Ab.{u + 1} s g).hom.naturality
    ((upperStarForgetIso Λ s).hom.app ((g)^*⟦Λ⟧.obj M))
  have h2 := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} s).unit.naturality
    ((upperStarForgetIso Λ g).inv.app M)
  have h3 := (ProEtale.lowerStarComp Ab.{u + 1} s g).hom.naturality
    ((s)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h1 h2 h3
  erw [reassoc_of% h1, ← Functor.map_comp_assoc (s ≫ g)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% h3, ← Functor.map_comp_assoc, ← h2, Functor.map_comp_assoc]

/-- `forget_map_unitTransport_app` for an arbitrary factorization `s ≫ g = p₁`. -/
lemma forget_map_unitTransport_app_of_eq {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    {p₁ : Y' ⟶ X} (hp : s ≫ g = p₁)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((unitTransport Λ s hp hp).app M) =
      (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M) ≫
        ((g)_*[Ab.{u + 1}].map ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} s).unit.app
          ((g)^*[Ab.{u + 1}].obj M.X)) ≫
        (ProEtale.lowerStarComp Ab.{u + 1} s g).hom.app _ ≫
        (s ≫ g)_*[Ab.{u + 1}].map ((ProEtale.upperStarComp Ab.{u + 1} s g).inv.app M.X) ≫
        eqToHom (congrArg (fun p ↦ (p)_*[Ab.{u + 1}].obj ((p)^*[Ab.{u + 1}].obj M.X))
          hp)) ≫
        (p₁)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ p₁).hom.app M) := by
  subst hp
  rw [eqToHom_refl, Category.comp_id, forget_map_unitTransport_app]
  simp only [Category.assoc]

/-- **The Galois action on module objects is the unit transport** along `ρ σ`: the module-level
identity behind `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit`, obtained from
the identity on abelian sheaves `ProEtale.galoisAction_eq_unitTransport` on underlying sheaves. -/
theorem galoisAction_eq_unitTransport {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    [Surjective g] [QuasiCompact g] {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g)
    (σ : Γ) [WeaklyEtale (ρ σ)] :
    galoisAction Λ g hρ σ = unitTransport Λ (ρ σ) (hρ σ) (hρ σ) := by
  ext M : 2
  apply (Mod.forget (condensedRingObj Λ X)).map_injective
  rw [forget_map_galoisAction_app, forget_map_unitTransport_app_of_eq,
    ProEtale.galoisAction_eq_unitTransport g hρ σ]

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (L' : Type u) [Field L'] [Algebra L L']
  [FiniteDimensional L L'] [IsGalois L L']

-- the derived functors and their composition isomorphisms are large terms
/-- **The pullback exchange of a finite Galois layer is split by the averaged action on nearby
cycles**: if multiplication by `|Γ|` is invertible on `Lε^* C`, the pullback exchange `α` of
`N_{L'} ⟶ N` has a retraction `r` with `|Γ| • (r ≫ α) = ∑ σ, σ_*`, where `σ_*` is the action of
`galoisLayerAut σ` on the nearby cycles. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_autAction
    (C : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso (Fintype.card (L' ≃ₐ[L] L') • 𝟙 (L((N.ε)^*⟦Λ⟧).obj C))] :
    ∃ r, ((N.galoisLayerHom h L').pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      Fintype.card (L' ≃ₐ[L] L') • (r ≫ ((N.galoisLayerHom h L').pullbackExchange Λ).app C) =
        ∑ σ, (N.galoisLayerAut h L' σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) :=
  exists_retraction_pullbackExchange_galoisLayerHom_of_galoisAction_eq Λ N h L' C
    (Equiv.refl _) fun σ ↦ galoisAction_eq_unitTransport Λ _
      (pullbackAction_fst h _ specGaloisAction_comp) σ

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
