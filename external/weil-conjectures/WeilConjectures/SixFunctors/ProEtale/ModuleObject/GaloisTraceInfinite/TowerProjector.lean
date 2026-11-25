/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace
public import WeilConjectures.CategoryTheory.Preadditive.SubgroupAverage

/-!
# Averaging projectors on the infinite level of a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`), `Λ` a commutative
condensed ring in which the orders `|Γ_j|` are invertible, and `M` a `Λ_X`-module object such
that `M_∞ = g_{∞*} g_∞^* M` is the colimit of the finite levels `M_j = g_{j*} g_j^* M`.

For a subgroup `H ≤ Γ_j`, the average `avg_H = |H|⁻¹ ∑_{a ∈ H} a` acts on `M_j`
(`AlgebraicGeometry.ProEtale.GaloisTower.levelAvg`). A family of subgroups `N j ≤ Γ_j` compatible
with the transition maps (`AlgebraicGeometry.ProEtale.GaloisTower.transport_comp_levelAvg`) gives
a projector `π_N : M_∞ ⟶ M_∞` (`AlgebraicGeometry.ProEtale.GaloisTower.proj`), equal to
`avg_{N j}` on the level `j`. We prove:

* `π_N ≫ π_N' = π_(N ⊔ N')` for normal subgroups
  (`AlgebraicGeometry.ProEtale.GaloisTower.proj_comp_proj`);
* `π_N` is the identity on the level `j` if `N j = ⊥`
  (`AlgebraicGeometry.ProEtale.GaloisTower.infTransport_comp_proj_of_eq_bot`);
* `π_N = τ ≫ u` is the invariant projector of the normalized trace if `N j = ⊤` for all `j`
  (`AlgebraicGeometry.ProEtale.GaloisTower.proj_eq_trace_comp_infUnit`);
* on the level `j`, `π_N ≫ ∑_i σ_i = |I| • avg_{Γ_j}` if the `σ_i` cover a system of
  representatives of the cosets of `N j`
  (`AlgebraicGeometry.ProEtale.GaloisTower.infTransport_comp_proj_comp_sum`);
* `π_N` is natural in `M` (`AlgebraicGeometry.ProEtale.GaloisTower.proj_naturality`).
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits Preadditive

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))

/-- An element of the Galois group acting trivially on a finite level acts trivially on the
level functor. -/
lemma levelAction_app_eq_id (j : T.J) (a : T.Γ j) (ha : T.ρ j a = 𝟙 _) :
    (T.levelAction Λ j a).app M = 𝟙 _ := by
  apply (Mod.forget _).map_injective
  unfold levelAction
  rw [CondensedRing.forget_map_galoisAction_app_eq, upperStarLowerStarHom_congr _ ha,
    upperStarLowerStarHom_id, NatTrans.id_app]
  erw [id_comp]
  rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

include hd in
/-- The order of `Γ_j` is invertible on module objects. -/
lemma isIso_natCard_nsmul (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (Nat.card (T.Γ j) • 𝟙 N) := by
  rw [Nat.card_eq_fintype_card]
  exact hd j N

/-- The average `avg_H = |H|⁻¹ ∑_{a ∈ H} a` over a subgroup `H ≤ Γ_j`, acting on the level
`M_j`. -/
noncomputable def levelAvg (j : T.J) (H : Subgroup (T.Γ j)) :
    (T.levelFunctor Λ j).obj M ⟶ (T.levelFunctor Λ j).obj M :=
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  subgroupAvg (fun a ↦ (T.levelAction Λ j a).app M) H

/-- Unfolding the level average. -/
lemma levelAvg_eq (j : T.J) (H : Subgroup (T.Γ j))
    [IsIso (Nat.card (T.Γ j) • 𝟙 ((T.levelFunctor Λ j).obj M))] :
    T.levelAvg Λ M hd j H = subgroupAvg (fun a ↦ (T.levelAction Λ j a).app M) H :=
  rfl

/-- **Compatibility of averages with the transition maps**: if the restriction maps `H'` onto
`H` (in the sense of the lifts of the Galois actions along `t`), then the averages commute with
the transport `M_j ⟶ M_{j'}`. -/
lemma transport_comp_levelAvg {j j' : T.J} (hle : j ≤ j') (H : Subgroup (T.Γ j))
    (H' : Subgroup (T.Γ j'))
    (h₁ : ∀ a ∈ H, ∃ b ∈ H', T.t hle ≫ T.ρ j a = T.ρ j' b ≫ T.t hle)
    (h₂ : ∀ b ∈ H', ∃ a ∈ H, T.t hle ≫ T.ρ j a = T.ρ j' b ≫ T.t hle) :
    T.transport Λ M hle ≫ T.levelAvg Λ M hd j' H' =
      T.levelAvg Λ M hd j H ≫ T.transport Λ M hle := by
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  have := T.isIso_natCard_nsmul Λ hd j' ((T.levelFunctor Λ j').obj M)
  rw [T.levelAvg_eq, T.levelAvg_eq]
  have e₁ : subgroupAvg (fun a ↦ (T.levelAction Λ j a).app M) H ≫ T.transport Λ M hle ≫
      subgroupAvg (fun a ↦ (T.levelAction Λ j' a).app M) H' =
        T.transport Λ M hle ≫ subgroupAvg (fun a ↦ (T.levelAction Λ j' a).app M) H' :=
    subgroupAvg_comp_of_forall _ fun a ha ↦ by
      obtain ⟨b, hb, hab⟩ := h₁ a ha
      rw [← assoc, T.levelAction_app_comp_transport Λ M hle a b hab, assoc,
        comp_subgroupAvg (ρ := fun a ↦ (T.levelAction Λ j' a).app M)
          (T.levelAction_app_comp_levelAction_app Λ M j') hb]
  have e₂ : (subgroupAvg (fun a ↦ (T.levelAction Λ j a).app M) H ≫ T.transport Λ M hle) ≫
      subgroupAvg (fun a ↦ (T.levelAction Λ j' a).app M) H' =
        subgroupAvg (fun a ↦ (T.levelAction Λ j a).app M) H ≫ T.transport Λ M hle :=
    comp_subgroupAvg_of_forall _ fun b hb ↦ by
      obtain ⟨a, ha, hab⟩ := h₂ b hb
      rw [assoc, ← T.levelAction_app_comp_transport Λ M hle a b hab, ← assoc,
        subgroupAvg_comp (ρ := fun a ↦ (T.levelAction Λ j a).app M)
          (T.levelAction_app_comp_levelAction_app Λ M j) ha]
  rw [← e₁, ← assoc, e₂]

/-- The averages commute with the maps `g_{j*} g_j^* φ`. -/
lemma levelAvg_naturality {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : M ⟶ M') (j : T.J) (H : Subgroup (T.Γ j)) :
    (T.levelFunctor Λ j).map φ ≫ T.levelAvg Λ M' hd j H =
      T.levelAvg Λ M hd j H ≫ (T.levelFunctor Λ j).map φ := by
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M')
  rw [T.levelAvg_eq, T.levelAvg_eq, subgroupAvg_eq, subgroupAvg_eq, comp_nsmul, nsmul_comp,
    ← assoc, ← inv_nsmul_id_comp, assoc, assoc]
  congr 2
  unfold subgroupSum
  rw [comp_sum, sum_comp]
  exact Finset.sum_congr rfl fun a _ ↦ (T.levelAction Λ j a).naturality φ

/-- The cocone of the averages over a compatible family of subgroups `N j ≤ Γ_j`. -/
noncomputable def projCocone (N : ∀ j, Subgroup (T.Γ j))
    (hN : ∀ ⦃j j' : T.J⦄ (hle : j ≤ j'), T.transport Λ M hle ≫ T.levelAvg Λ M hd j' (N j') =
      T.levelAvg Λ M hd j (N j) ≫ T.transport Λ M hle) :
    Cocone (T.moduleDiagram Λ M) where
  pt := (infFunctor Λ ginf).obj M
  ι :=
    { app j := T.levelAvg Λ M hd j (N j) ≫ T.infTransport Λ M j
      naturality j j' f := (show T.transport Λ M (leOfHom f) ≫ T.levelAvg Λ M hd j' (N j') ≫
          T.infTransport Λ M j' = _ by rw [← assoc, hN, assoc, T.transport_comp_infTransport]).trans
        (comp_id _).symm }

/-- The **projector** `π_N : M_∞ ⟶ M_∞` of a compatible family of subgroups `N j ≤ Γ_j`, glued
from the averages `avg_{N j}` on the finite levels. -/
noncomputable def proj (hc : IsColimit (T.moduleCocone Λ M)) (N : ∀ j, Subgroup (T.Γ j))
    (hN : ∀ ⦃j j' : T.J⦄ (hle : j ≤ j'), T.transport Λ M hle ≫ T.levelAvg Λ M hd j' (N j') =
      T.levelAvg Λ M hd j (N j) ≫ T.transport Λ M hle) :
    (infFunctor Λ ginf).obj M ⟶ (infFunctor Λ ginf).obj M :=
  hc.desc (T.projCocone Λ M hd N hN)

variable {Λ M hd} (hc : IsColimit (T.moduleCocone Λ M))

/-- The projector `π_N` is the average `avg_{N j}` on the level `j`. -/
lemma infTransport_comp_proj (N : ∀ j, Subgroup (T.Γ j))
    (hN : ∀ ⦃j j' : T.J⦄ (hle : j ≤ j'), T.transport Λ M hle ≫ T.levelAvg Λ M hd j' (N j') =
      T.levelAvg Λ M hd j (N j) ≫ T.transport Λ M hle) (j : T.J) :
    T.infTransport Λ M j ≫ T.proj Λ M hd hc N hN =
      T.levelAvg Λ M hd j (N j) ≫ T.infTransport Λ M j :=
  hc.fac (T.projCocone Λ M hd N hN) j

/-- **Product of projectors**: `π_N ≫ π_N' = π_N''` if `N j ⊔ N' j = N'' j` with `N' j`
normal. -/
lemma proj_comp_proj (h₁ : ∀ j, T.ρ j 1 = 𝟙 _) (N N' N'' : ∀ j, Subgroup (T.Γ j)) (hN hN' hN'')
    (hnormal : ∀ j, (N' j).Normal) (hsup : ∀ j, N j ⊔ N' j = N'' j) :
    T.proj Λ M hd hc N hN ≫ T.proj Λ M hd hc N' hN' = T.proj Λ M hd hc N'' hN'' := by
  refine hc.hom_ext fun j ↦ ?_
  change T.infTransport Λ M j ≫ _ = T.infTransport Λ M j ≫ _
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  rw [← assoc, T.infTransport_comp_proj, assoc, T.infTransport_comp_proj, ← assoc,
    T.infTransport_comp_proj, T.levelAvg_eq, T.levelAvg_eq, T.levelAvg_eq,
    subgroupAvg_comp_subgroupAvg (T.levelAction_app_comp_levelAction_app Λ M j)
      (T.levelAction_app_eq_id Λ M j 1 (h₁ j)) _ _ (hnormal j), hsup]

/-- The projector `π_N` is the identity on the level `j` if `N j` is trivial. -/
lemma infTransport_comp_proj_of_eq_bot (h₁ : ∀ j, T.ρ j 1 = 𝟙 _) (N : ∀ j, Subgroup (T.Γ j)) (hN)
    (j : T.J) (hj : N j = ⊥) :
    T.infTransport Λ M j ≫ T.proj Λ M hd hc N hN = T.infTransport Λ M j := by
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  rw [T.infTransport_comp_proj, T.levelAvg_eq, hj,
    subgroupAvg_bot (T.levelAction_app_eq_id Λ M j 1 (h₁ j)), id_comp]

/-- The average over the whole Galois group on the level `j` is `t_j ≫ τ_j⁻¹ u`, followed to
`M_∞`: it is the invariant projector `τ ≫ u`. -/
lemma levelAvg_top_comp_infTransport (j : T.J) :
    T.levelAvg Λ M hd j ⊤ ≫ T.infTransport Λ M j =
      T.infTransport Λ M j ≫ T.trace Λ M hd hc ≫ (infUnit Λ ginf).app M := by
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  have := T.isIso_natCard_nsmul Λ hd j M
  have := T.isIso_natCard_nsmul Λ hd j ((𝟭 _).obj M)
  have hs : ∑ a, (T.levelAction Λ j a).app M =
      (T.levelTrace Λ j).app M ≫ (T.levelUnit Λ j).app M := by
    rw [← NatTrans.comp_app, levelTrace_comp_levelUnit, NatTrans.app_sum]
  rw [← assoc, T.infTransport_comp_trace, T.levelAvg_eq, subgroupAvg_top, hs, assoc, assoc,
    levelUnit_app_comp_infTransport, ← assoc, inv_nsmul_id_comp]
  simp only [normTrace, normalizedTrace, assoc]
  rw [inv_nsmul_id_congr Nat.card_eq_fintype_card]
  rfl

/-- The projector `π_N` is the invariant projector `τ ≫ u` if `N j = Γ_j` for all `j`. -/
lemma proj_eq_trace_comp_infUnit (N : ∀ j, Subgroup (T.Γ j)) (hN) (hN' : ∀ j, N j = ⊤) :
    T.proj Λ M hd hc N hN = T.trace Λ M hd hc ≫ (infUnit Λ ginf).app M := by
  refine hc.hom_ext fun j ↦ ?_
  change T.infTransport Λ M j ≫ _ = T.infTransport Λ M j ≫ _
  rw [T.infTransport_comp_proj, hN', T.levelAvg_top_comp_infTransport hc]

/-- **Summing over coset representatives**: on the level `j`, if automorphisms `σ i` of `Y_∞`
cover elements `b i ∈ Γ_j` forming a system of representatives of `Γ_j / N j`, then
`π_N ≫ ∑_i σ_i = |I| • avg_{Γ_j}`. -/
lemma infTransport_comp_proj_comp_sum (N : ∀ j, Subgroup (T.Γ j)) (hN) (j : T.J) {I : Type*}
    [Fintype I] (σ : I → (Yinf ⟶ Yinf)) (hσ : ∀ i, σ i ≫ ginf = ginf) (b : I → T.Γ j)
    (hb : ∀ i, σ i ≫ T.π j = T.π j ≫ T.ρ j (b i))
    (hbij : Function.Bijective fun x : I × N j ↦ b x.1 * x.2) :
    T.infTransport Λ M j ≫ T.proj Λ M hd hc N hN ≫ ∑ i, infAction Λ M (σ i) (hσ i) =
      Fintype.card I • (T.levelAvg Λ M hd j ⊤ ≫ T.infTransport Λ M j) := by
  have := T.isIso_natCard_nsmul Λ hd j ((T.levelFunctor Λ j).obj M)
  rw [← assoc, T.infTransport_comp_proj, assoc, comp_sum,
    Finset.sum_congr rfl fun i _ ↦ T.infTransport_comp_infAction Λ M (σ i) (hσ i) j (b i) (hb i),
    ← sum_comp, ← assoc, T.levelAvg_eq, T.levelAvg_eq,
    subgroupAvg_comp_sum (T.levelAction_app_comp_levelAction_app Λ M j) b hbij,
    Nat.card_eq_fintype_card, nsmul_comp]

/-- **Naturality of the projectors** in the module object. -/
lemma proj_naturality {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : M ⟶ M') (hc : IsColimit (T.moduleCocone Λ M))
    (hc' : IsColimit (T.moduleCocone Λ M')) (N : ∀ j, Subgroup (T.Γ j)) (hN hN') :
    (infFunctor Λ ginf).map φ ≫ T.proj Λ M' hd hc' N hN' =
      T.proj Λ M hd hc N hN ≫ (infFunctor Λ ginf).map φ := by
  refine hc.hom_ext fun j ↦ ?_
  change T.infTransport Λ M j ≫ _ = T.infTransport Λ M j ≫ _
  rw [← assoc, T.infTransport_naturality, assoc, T.infTransport_comp_proj, ← assoc,
    T.levelAvg_naturality, ← assoc (T.infTransport Λ M j), T.infTransport_comp_proj, assoc, assoc,
    T.infTransport_naturality]

end AlgebraicGeometry.ProEtale.GaloisTower
