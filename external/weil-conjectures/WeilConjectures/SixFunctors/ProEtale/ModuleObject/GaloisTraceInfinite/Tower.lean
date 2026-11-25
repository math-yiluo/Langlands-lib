/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.UnitTransport
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits

/-!
# Towers of finite Galois coverings

A *Galois tower* over a scheme `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) is a directed
system of finite étale Galois coverings `g_j : Y_j ⟶ X` with groups `Γ_j`, transition maps
`Y_{j'} ⟶ Y_j` over `X` along which the Galois actions lift, and a cone `π_j : Y_∞ ⟶ Y_j` over `X`
with `g_∞ : Y_∞ ⟶ X` weakly étale. The example is `Y_j = G ×_L L_j`, `Y_∞ = G ×_L Ω` for a
Galois extension `Ω/L` with finite Galois subextensions `L_j`.

For a commutative condensed ring `Λ` and a `Λ_X`-module object `M`, the unit transports along the
transition maps and along the `π_j` form a diagram `j ↦ g_{j*} g_j^* M` with a cocone to
`g_{∞*} g_∞^* M` (`AlgebraicGeometry.ProEtale.GaloisTower.moduleDiagram`,
`AlgebraicGeometry.ProEtale.GaloisTower.moduleCocone`). It is a colimit as soon as the
corresponding cocone of abelian sheaves of restrictions is
(`AlgebraicGeometry.ProEtale.GaloisTower.isColimitModuleCocone`).

Everything is stated for an abstract tower: the unit transports of module objects at concrete
pullback schemes are expensive for the kernel, and an abstract statement is instantiated once.
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- A *Galois tower* over `X`: a directed system of finite étale Galois coverings `g_j : Y_j ⟶ X`
with groups `Γ_j`, transition maps `t : Y_{j'} ⟶ Y_j` over `X` along which the Galois actions
lift, and a cone `π_j : Y_∞ ⟶ Y_j` over `X` with `g_∞ : Y_∞ ⟶ X` weakly étale. -/
structure GaloisTower {X Yinf : Scheme.{u}} (ginf : Yinf ⟶ X) where
  /-- the index set. -/
  J : Type u
  [preorder : Preorder J]
  [isDirected : IsDirected J (· ≤ ·)]
  [nonempty : Nonempty J]
  /-- the finite levels. -/
  Y : J → Scheme.{u}
  /-- the structure maps of the finite levels. -/
  g : ∀ j, Y j ⟶ X
  [weaklyEtale : ∀ j, WeaklyEtale (g j)]
  [surjective : ∀ j, Surjective (g j)]
  [quasiCompact : ∀ j, QuasiCompact (g j)]
  /-- the transition maps. -/
  t : ∀ {j j' : J}, j ≤ j' → (Y j' ⟶ Y j)
  t_g : ∀ {j j' : J} (h : j ≤ j'), t h ≫ g j = g j'
  t_refl : ∀ j, t (le_refl j) = 𝟙 _
  t_comp : ∀ {j j' j'' : J} (h₁ : j ≤ j') (h₂ : j' ≤ j''), t h₂ ≫ t h₁ = t (h₁.trans h₂)
  /-- the projections from the limit. -/
  π : ∀ j, Yinf ⟶ Y j
  π_g : ∀ j, π j ≫ g j = ginf
  π_t : ∀ {j j' : J} (h : j ≤ j'), π j' ≫ t h = π j
  /-- the Galois groups. -/
  Γ : J → Type u
  [group : ∀ j, Group (Γ j)]
  [fintype : ∀ j, Fintype (Γ j)]
  /-- the Galois actions. -/
  ρ : ∀ j, Γ j → (Y j ⟶ Y j)
  ρ_g : ∀ j a, ρ j a ≫ g j = g j
  ρ_mul : ∀ j a b, ρ j a ≫ ρ j b = ρ j (a * b)
  isGaloisAction : ∀ j, IsGaloisAction (g j) (ρ j)
  exists_lift : ∀ {j j' : J} (h : j ≤ j') (a : Γ j), ∃ b : Γ j', t h ≫ ρ j a = ρ j' b ≫ t h

namespace GaloisTower

attribute [instance] preorder isDirected nonempty weaklyEtale surjective quasiCompact
  group fintype

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)

/-! ### Abelian sheaves -/

/-- The diagram `j ↦ g_{j*} g_j^* H` of abelian sheaves, with the restrictions along the
transition maps. -/
@[simps]
noncomputable def abDiagram (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    T.J ⥤ Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} where
  obj j := ((T.g j)^*[AddCommGrpCat.{u + 1}] ⋙ (T.g j)_*[AddCommGrpCat.{u + 1}]).obj H
  map f := (upperStarLowerStarHom _ _ (T.t (leOfHom f)) (T.t_g _)).app H
  map_id j := by
    rw [upperStarLowerStarHom_congr _ (T.t_refl j), upperStarLowerStarHom_id]
    rfl
  map_comp f f' := by
    rw [← NatTrans.comp_app, upperStarLowerStarHom_comp,
      upperStarLowerStarHom_congr _ (T.t_comp _ _)]

/-- The cocone of the restrictions `g_{j*} g_j^* H ⟶ g_{∞*} g_∞^* H` along the projections. -/
@[simps]
noncomputable def abCocone (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    Cocone (T.abDiagram H) where
  pt := ((ginf)^*[AddCommGrpCat.{u + 1}] ⋙ (ginf)_*[AddCommGrpCat.{u + 1}]).obj H
  ι :=
    { app j := (upperStarLowerStarHom _ _ (T.π j) (T.π_g j)).app H
      naturality j j' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, abDiagram_map, comp_id]
        rw [← NatTrans.comp_app, upperStarLowerStarHom_comp,
          upperStarLowerStarHom_congr _ (T.π_t _)] }

/-! ### Module objects -/

open CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The endofunctor `g_{j*} g_j^*` of `Λ_X`-module objects at the level `j`. -/
noncomputable def levelFunctor (j : T.J) :
    CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (T.g j)^*⟦Λ⟧ ⋙ (T.g j)_*⟦Λ⟧

/-- The endofunctor `g_{∞*} g_∞^*` of `Λ_X`-module objects. -/
noncomputable def infFunctor (ginf : Yinf ⟶ X) :
    CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (ginf)^*⟦Λ⟧ ⋙ (ginf)_*⟦Λ⟧

variable (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The unit transport `g_{j*} g_j^* M ⟶ g_{j'*} g_{j'}^* M` along the transition map. -/
@[irreducible] noncomputable def transport {j j' : T.J} (h : j ≤ j') :
    (T.levelFunctor Λ j).obj M ⟶ (T.levelFunctor Λ j').obj M :=
  (unitTransport Λ (T.t h) (T.t_g h) (T.t_g h)).app M

/-- The unit transport `g_{j*} g_j^* M ⟶ g_{∞*} g_∞^* M` along the projection. -/
@[irreducible] noncomputable def infTransport (j : T.J) :
    (T.levelFunctor Λ j).obj M ⟶ (infFunctor Λ ginf).obj M :=
  (unitTransport Λ (T.π j) (T.π_g j) (T.π_g j)).app M

lemma forget_map_transport {j j' : T.J} (h : j ≤ j') :
    (Mod.forget _).map (T.transport Λ M h) =
      (T.g j)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ (T.g j)).inv.app M) ≫
        (upperStarLowerStarHom (T.g j) (T.g j') (T.t h) (T.t_g h)).app M.X ≫
        (T.g j')_*[Ab.{u + 1}].map ((upperStarForgetIso Λ (T.g j')).hom.app M) := by
  unfold transport
  exact forget_map_unitTransport_app_eq Λ (T.t h) (T.g j) (T.t_g h) M

lemma forget_map_infTransport (j : T.J) :
    (Mod.forget _).map (T.infTransport Λ M j) =
      (T.g j)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ (T.g j)).inv.app M) ≫
        (upperStarLowerStarHom (T.g j) ginf (T.π j) (T.π_g j)).app M.X ≫
        (ginf)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ ginf).hom.app M) := by
  unfold infTransport
  exact forget_map_unitTransport_app_eq Λ (T.π j) (T.g j) (T.π_g j) M

lemma transport_refl (j : T.J) : T.transport Λ M (le_refl j) = 𝟙 _ := by
  apply (Mod.forget _).map_injective
  rw [forget_map_transport, upperStarLowerStarHom_congr _ (T.t_refl j),
    upperStarLowerStarHom_id, NatTrans.id_app]
  erw [id_comp]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

lemma transport_comp {j j' j'' : T.J} (h₁ : j ≤ j') (h₂ : j' ≤ j'') :
    T.transport Λ M h₁ ≫ T.transport Λ M h₂ = T.transport Λ M (h₁.trans h₂) := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, forget_map_transport, forget_map_transport, forget_map_transport]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (T.g j')_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc, upperStarLowerStarHom_comp,
    upperStarLowerStarHom_congr _ (T.t_comp h₁ h₂)]

lemma transport_comp_infTransport {j j' : T.J} (h : j ≤ j') :
    T.transport Λ M h ≫ T.infTransport Λ M j' = T.infTransport Λ M j := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, forget_map_transport, forget_map_infTransport, forget_map_infTransport]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (T.g j')_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc, upperStarLowerStarHom_comp,
    upperStarLowerStarHom_congr _ (T.π_t h)]

/-- The diagram `j ↦ g_{j*} g_j^* M` of module objects, with the unit transports along the
transition maps. -/
noncomputable def moduleDiagram : T.J ⥤
    CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) where
  obj j := (T.levelFunctor Λ j).obj M
  map f := T.transport Λ M (leOfHom f)
  map_id j := T.transport_refl Λ M j
  map_comp _ _ := (T.transport_comp Λ M _ _).symm

/-- The transition maps of the module diagram. -/
lemma moduleDiagram_map {j j' : T.J} (f : j ⟶ j') :
    (T.moduleDiagram Λ M).map f = T.transport Λ M (leOfHom f) := rfl

/-- The cocone of the unit transports `g_{j*} g_j^* M ⟶ g_{∞*} g_∞^* M` along the projections. -/
noncomputable def moduleCocone : Cocone (T.moduleDiagram Λ M) where
  pt := (infFunctor Λ ginf).obj M
  ι :=
    { app j := T.infTransport Λ M j
      naturality _ _ _ := (T.transport_comp_infTransport Λ M _).trans (comp_id _).symm }

/-- The maps of the module cocone. -/
lemma moduleCocone_ι_app (j : T.J) : (T.moduleCocone Λ M).ι.app j = T.infTransport Λ M j := rfl

/-- On underlying sheaves, the diagram of module objects is the diagram of abelian sheaves. -/
noncomputable def moduleDiagramForgetIso :
    T.moduleDiagram Λ M ⋙ Mod.forget _ ≅ T.abDiagram M.X :=
  NatIso.ofComponents (fun j ↦ (T.g j)_*[Ab.{u + 1}].mapIso
      ((upperStarForgetIso Λ (T.g j)).app M).symm)
    fun {j j'} f ↦ by
      rw [Functor.comp_map, moduleDiagram_map, forget_map_transport]
      simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, abDiagram_map, assoc]
      rw [← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, comp_id]

/-- **Colimits of module objects from colimits of abelian sheaves**: if the cocone of restrictions
of the underlying abelian sheaf of `M` is a colimit, so is the cocone of unit transports of `M`. -/
noncomputable def isColimitModuleCocone (hc : IsColimit (T.abCocone M.X)) :
    IsColimit (T.moduleCocone Λ M) := by
  refine isColimitOfReflects (Mod.forget _)
    ((IsColimit.equivOfNatIsoOfIso (T.moduleDiagramForgetIso Λ M) _ _ ?_).symm hc)
  refine Cocone.ext ((ginf)_*[Ab.{u + 1}].mapIso
    ((upperStarForgetIso Λ _).app M).symm) fun j ↦ ?_
  rw [Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app, moduleCocone_ι_app,
    forget_map_infTransport]
  simp only [moduleDiagramForgetIso, NatIso.ofComponents_inv_app, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_inv, abCocone_ι_app,
    assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, comp_id]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]

end GaloisTower

end AlgebraicGeometry.ProEtale
