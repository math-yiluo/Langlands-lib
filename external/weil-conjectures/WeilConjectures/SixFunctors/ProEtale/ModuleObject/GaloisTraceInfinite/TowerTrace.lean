/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.Tower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.NormalizedTraceUnique

/-!
# The normalized trace of a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `Λ` a
commutative condensed ring in which the orders `|Γ_j|` of the Galois groups are invertible. For a
`Λ_X`-module object `M` such that `g_{∞*} g_∞^* M` is the colimit of the finite levels
`g_{j*} g_j^* M` (`AlgebraicGeometry.ProEtale.GaloisTower.moduleCocone`), the normalized finite
traces `|Γ_j|⁻¹ t_j : g_{j*} g_j^* M ⟶ M` are compatible with the transition maps and glue to a
*normalized trace* `τ : g_{∞*} g_∞^* M ⟶ M` (`AlgebraicGeometry.ProEtale.GaloisTower.trace`):

* `τ` is a retraction of the unit (`AlgebraicGeometry.ProEtale.GaloisTower.unit_comp_trace`);
* `τ` is natural in `M` (`AlgebraicGeometry.ProEtale.GaloisTower.map_comp_trace`);
* `τ` is invariant under the unit transport along any automorphism of `Y_∞` over `X` which is
  compatible with the Galois actions at all finite levels
  (`AlgebraicGeometry.ProEtale.GaloisTower.infAction_comp_trace`).

Compatibility of the normalized finite traces is proved by uniqueness: an invariant retraction of
the unit of a finite Galois covering is the normalized trace (`CategoryTheory.eq_normalizedTrace`).
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
/-- The unit of `g^* ⊣ g_*` on module objects is a monomorphism for `g` surjective, quasi-compact
and weakly étale. -/
instance _root_.AlgebraicGeometry.ProEtale.CondensedRing.mono_upperStarLowerStarAdjunction_unit_app
    {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g] [Surjective g] [QuasiCompact g]
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono ((CondensedRing.upperStarLowerStarAdjunction Λ g).unit.app M) := by
  refine (Mod.forget _).mono_of_mono_map ?_
  rw [CondensedRing.forget_map_unit_app]
  have : Mono ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app M.X) :=
    inferInstance
  have : Mono ((g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M)) :=
    IsIso.mono_of_iso _
  exact mono_comp _ _

/-- The trace `g_j^* ⋙ g_{j*} ⟶ 𝟭` of the finite Galois covering at the level `j`. -/
noncomputable def levelTrace (j : T.J) : T.levelFunctor Λ j ⟶ 𝟭 _ :=
  CondensedRing.galoisTrace Λ (T.g j) (T.ρ_g j) (T.ρ_mul j) (T.isGaloisAction j)

/-- The action of `a ∈ Γ_j` on `g_j^* ⋙ g_{j*}`. -/
noncomputable def levelAction (j : T.J) (a : T.Γ j) : T.levelFunctor Λ j ⟶ T.levelFunctor Λ j :=
  CondensedRing.galoisAction Λ (T.g j) (T.ρ_g j) a

/-- The unit of `g_j^* ⊣ g_{j*}`, as a natural transformation to the level functor. -/
noncomputable def levelUnit (j : T.J) : 𝟭 _ ⟶ T.levelFunctor Λ j :=
  (CondensedRing.upperStarLowerStarAdjunction Λ (T.g j)).unit

/-- The unit of `g_∞^* ⊣ g_{∞*}`. -/
noncomputable def infUnit (ginf : Yinf ⟶ X) : 𝟭 _ ⟶ infFunctor Λ ginf :=
  (CondensedRing.upperStarLowerStarAdjunction Λ ginf).unit

instance (j : T.J)
    (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono ((T.levelUnit Λ j).app M) :=
  CondensedRing.mono_upperStarLowerStarAdjunction_unit_app Λ (T.g j) M

lemma levelUnit_comp_levelTrace (j : T.J) :
    T.levelUnit Λ j ≫ T.levelTrace Λ j = Fintype.card (T.Γ j) • 𝟙 _ :=
  CondensedRing.unit_comp_galoisTrace Λ (T.g j) (T.ρ_g j) (T.ρ_mul j) (T.isGaloisAction j)

lemma levelTrace_comp_levelUnit (j : T.J) :
    T.levelTrace Λ j ≫ T.levelUnit Λ j = ∑ a, T.levelAction Λ j a :=
  CondensedRing.galoisTrace_comp_unit Λ (T.g j) (T.ρ_g j) (T.ρ_mul j) (T.isGaloisAction j)

variable (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

lemma levelAction_app_comp_levelAction_app (j : T.J) (a b : T.Γ j) :
    (T.levelAction Λ j a).app M ≫ (T.levelAction Λ j b).app M = (T.levelAction Λ j (b * a)).app M :=
  CondensedRing.galoisAction_app_comp_galoisAction_app Λ (T.ρ_g j) (T.ρ_mul j) a b M

lemma levelUnit_app_comp_transport {j j' : T.J} (h : j ≤ j') :
    (T.levelUnit Λ j).app M ≫ T.transport Λ M h = (T.levelUnit Λ j').app M := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, forget_map_transport]
  unfold levelUnit
  rw [CondensedRing.forget_map_unit_app, CondensedRing.forget_map_unit_app]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (T.g j)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc, upperStarLowerStarAdjunction_unit_comp_upperStarLowerStarHom]

lemma levelUnit_app_comp_infTransport (j : T.J) :
    (T.levelUnit Λ j).app M ≫ T.infTransport Λ M j = (infUnit Λ ginf).app M := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, forget_map_infTransport]
  unfold levelUnit infUnit
  rw [CondensedRing.forget_map_unit_app, CondensedRing.forget_map_unit_app]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (T.g j)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc, upperStarLowerStarAdjunction_unit_comp_upperStarLowerStarHom]

lemma levelAction_app_comp_transport {j j' : T.J} (h : j ≤ j') (a : T.Γ j) (b : T.Γ j')
    (hab : T.t h ≫ T.ρ j a = T.ρ j' b ≫ T.t h) :
    (T.levelAction Λ j a).app M ≫ T.transport Λ M h =
      T.transport Λ M h ≫ (T.levelAction Λ j' b).app M := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, Functor.map_comp, forget_map_transport]
  unfold levelAction
  rw [CondensedRing.forget_map_galoisAction_app_eq, CondensedRing.forget_map_galoisAction_app_eq]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (T.g j)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← Functor.map_comp_assoc (T.g j')_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc, ← NatTrans.comp_app_assoc,
    upperStarLowerStarHom_comp_upperStarLowerStarHom_of_comp_eq _ _ _ _ _ _ hab]

/-! ### The normalized finite traces -/

variable (hd : ∀ (j : T.J)
  (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsIso (Fintype.card (T.Γ j) • 𝟙 N))

/-- The normalized trace `|Γ_j|⁻¹ t_j : g_{j*} g_j^* M ⟶ M` at the level `j`. -/
noncomputable def normTrace (j : T.J) : (T.levelFunctor Λ j).obj M ⟶ M :=
  haveI := hd j M
  normalizedTrace ((T.levelTrace Λ j).app M) (Fintype.card (T.Γ j))

lemma levelUnit_app_comp_normTrace (j : T.J) :
    (T.levelUnit Λ j).app M ≫ T.normTrace Λ M hd j = 𝟙 M := by
  have := hd j M
  exact comp_normalizedTrace (by
    simpa using congr_app (T.levelUnit_comp_levelTrace Λ j) M)

lemma levelAction_app_comp_normTrace (j : T.J) (a : T.Γ j) :
    (T.levelAction Λ j a).app M ≫ T.normTrace Λ M hd j = T.normTrace Λ M hd j := by
  have := hd j M
  refine comp_normalizedTrace_of_comp_eq ?_
  exact comp_eq_of_comp_eq_sum (u := (T.levelUnit Λ j).app M)
    (ρ := fun a ↦ (T.levelAction Λ j a).app M)
    (fun a b ↦ T.levelAction_app_comp_levelAction_app Λ M j a b)
    (by simpa [NatTrans.app_sum] using congr_app (T.levelTrace_comp_levelUnit Λ j) M) a

lemma transport_comp_normTrace {j j' : T.J} (h : j ≤ j') :
    T.transport Λ M h ≫ T.normTrace Λ M hd j' = T.normTrace Λ M hd j := by
  have := hd j M
  refine eq_normalizedTrace (u := (T.levelUnit Λ j).app M)
    (ρ := fun a ↦ (T.levelAction Λ j a).app M) rfl
    (by simpa [NatTrans.app_sum] using congr_app (T.levelTrace_comp_levelUnit Λ j) M) ?_ ?_
  · rw [← assoc, T.levelUnit_app_comp_transport]
    exact T.levelUnit_app_comp_normTrace Λ M hd j'
  · intro a
    obtain ⟨b, hab⟩ := T.exists_lift h a
    rw [← assoc, T.levelAction_app_comp_transport Λ M h a b hab, assoc]
    exact congrArg (T.transport Λ M h ≫ ·) (T.levelAction_app_comp_normTrace Λ M hd j' b)

/-! ### The normalized trace of the tower -/

/-- The cocone of the normalized finite traces, with point `M`. -/
noncomputable def normTraceCocone : Cocone (T.moduleDiagram Λ M) where
  pt := M
  ι :=
    { app j := T.normTrace Λ M hd j
      naturality _ _ f := (T.transport_comp_normTrace Λ M hd (leOfHom f)).trans (comp_id _).symm }

/-- **The normalized trace of a Galois tower** `τ : g_{∞*} g_∞^* M ⟶ M`, glued from the normalized
finite traces along the colimit `g_{∞*} g_∞^* M = colim_j g_{j*} g_j^* M`. -/
noncomputable def trace (hc : IsColimit (T.moduleCocone Λ M)) : (infFunctor Λ ginf).obj M ⟶ M :=
  hc.desc (T.normTraceCocone Λ M hd)

lemma infTransport_comp_trace (hc : IsColimit (T.moduleCocone Λ M)) (j : T.J) :
    T.infTransport Λ M j ≫ T.trace Λ M hd hc = T.normTrace Λ M hd j :=
  hc.fac (T.normTraceCocone Λ M hd) j

/-- **The normalized trace is a retraction of the unit.** -/
lemma unit_comp_trace (hc : IsColimit (T.moduleCocone Λ M)) :
    (infUnit Λ ginf).app M ≫ T.trace Λ M hd hc = 𝟙 M := by
  obtain ⟨j⟩ := T.nonempty
  rw [← T.levelUnit_app_comp_infTransport Λ M j, assoc, T.infTransport_comp_trace,
    T.levelUnit_app_comp_normTrace]

/-! ### Naturality -/

lemma infTransport_naturality {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : M ⟶ M') (j : T.J) :
    T.infTransport Λ M j ≫ (infFunctor Λ ginf).map φ =
      (T.levelFunctor Λ j).map φ ≫ T.infTransport Λ M' j := by
  unfold infTransport
  exact ((unitTransport Λ (T.π j) (T.π_g j) (T.π_g j)).naturality φ).symm

lemma normTrace_naturality {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : M ⟶ M') (j : T.J) :
    (T.levelFunctor Λ j).map φ ≫ T.normTrace Λ M' hd j = T.normTrace Λ M hd j ≫ φ := by
  have := hd j M
  have := hd j M'
  have hφ : inv (Fintype.card (T.Γ j) • 𝟙 M) ≫ φ = φ ≫ inv (Fintype.card (T.Γ j) • 𝟙 M') := by
    rw [IsIso.inv_comp_eq, ← assoc, IsIso.eq_comp_inv, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, id_comp, comp_id]
  simp only [normTrace, normalizedTrace]
  rw [← assoc, (T.levelTrace Λ j).naturality φ, assoc, assoc, hφ]
  rfl

/-- **The normalized trace is natural** in the module object. -/
lemma map_comp_trace {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : M ⟶ M') (hc : IsColimit (T.moduleCocone Λ M))
    (hc' : IsColimit (T.moduleCocone Λ M')) :
    (infFunctor Λ ginf).map φ ≫ T.trace Λ M' hd hc' = T.trace Λ M hd hc ≫ φ := by
  refine hc.hom_ext fun j ↦ ?_
  change T.infTransport Λ M j ≫ _ = T.infTransport Λ M j ≫ _
  rw [← assoc, T.infTransport_naturality, assoc, T.infTransport_comp_trace, ← assoc,
    T.infTransport_comp_trace, T.normTrace_naturality]

/-! ### Galois invariance -/

/-- The unit transport `g_{∞*} g_∞^* M ⟶ g_{∞*} g_∞^* M` along an automorphism `σ` of `Y_∞` over
`X`. -/
@[irreducible] noncomputable def infAction (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) :
    (infFunctor Λ ginf).obj M ⟶ (infFunctor Λ ginf).obj M :=
  (unitTransport Λ σ hσ hσ).app M

lemma infAction_eq (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) :
    infAction Λ M σ hσ = (unitTransport Λ σ hσ hσ).app M := by
  unfold infAction
  rfl

lemma infTransport_comp_infAction (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) (j : T.J)
    (a : T.Γ j) (ha : σ ≫ T.π j = T.π j ≫ T.ρ j a) :
    T.infTransport Λ M j ≫ infAction Λ M σ hσ =
      (T.levelAction Λ j a).app M ≫ T.infTransport Λ M j := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, Functor.map_comp, forget_map_infTransport, infAction_eq,
    forget_map_unitTransport_app_eq]
  unfold levelAction
  rw [CondensedRing.forget_map_galoisAction_app_eq]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (ginf)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← Functor.map_comp_assoc (T.g j)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc, ← NatTrans.comp_app_assoc, upperStarLowerStarHom_comp,
    upperStarLowerStarHom_comp, upperStarLowerStarHom_congr _ ha]

/-- **The normalized trace is Galois invariant**: it is fixed by the unit transport along any
automorphism `σ` of `Y_∞` over `X` which, at every finite level, covers an element of the Galois
group. -/
lemma infAction_comp_trace (hc : IsColimit (T.moduleCocone Λ M)) (σ : Yinf ⟶ Yinf)
    (hσ : σ ≫ ginf = ginf) (hσj : ∀ j, ∃ a, σ ≫ T.π j = T.π j ≫ T.ρ j a) :
    infAction Λ M σ hσ ≫ T.trace Λ M hd hc = T.trace Λ M hd hc := by
  refine hc.hom_ext fun j ↦ ?_
  obtain ⟨a, ha⟩ := hσj j
  change T.infTransport Λ M j ≫ _ = T.infTransport Λ M j ≫ _
  rw [← assoc, T.infTransport_comp_infAction Λ M σ hσ j a ha, assoc, T.infTransport_comp_trace,
    T.levelAction_app_comp_normTrace]

end AlgebraicGeometry.ProEtale.GaloisTower
