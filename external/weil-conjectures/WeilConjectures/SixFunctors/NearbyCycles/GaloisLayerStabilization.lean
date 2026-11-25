/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCompRetraction
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisActionModule

/-!

# Nearby cycles of a Galois layer which stabilizes at a finite level

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois
extension (possibly infinite) and `L ⊆ L' ⊆ Ω` a finite Galois subextension. The Galois layer
`N_Ω` (`NearbyCyclesModel.galoisLayer`) maps to the finite layer `N_{L'}` by the change of fibres
`N.generic ×_L Ω ⟶ N.generic ×_L L'` (`NearbyCyclesModel.galoisLayerRestrict`), compatibly with
the projections to `N` and with the Galois actions along the restriction
`Gal(Ω/L) ⟶ Gal(L'/L)`.

Suppose the nearby cycles *stabilize* at the level `L'`: the pullback exchange
`β : Ψ_{N_{L'}} ⟶ Ψ_{N_Ω}` of `N_Ω ⟶ N_{L'}` is invertible. Then
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_isIso`):

* the subgroup `Gal(Ω/L')` acts trivially on `Ψ_{N_Ω}`;
* the pullback exchange `α : Ψ_N ⟶ Ψ_{N_Ω}` of the projection is a split monomorphism whose
  idempotent, times `|Gal(L'/L)|`, is the sum of the actions of lifts to `Gal(Ω/L)` of the
  elements of `Gal(L'/L)`: `α` is the inclusion of the `Gal(Ω/L)`-invariants, computed by
  averaging over the finite quotient.

This holds for any coefficients in which `|Gal(L'/L)|` is invertible, in particular `ℚ̄_ℓ` for a
`p`-group: it is the passage from the finite Galois layers (step 1 of the finite-layer route,
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_autAction`) to the pro-`p`
Galois layer, given the stabilization, which comes from the continuity of the inertia action on
nearby cycles (SGA 4½, [Th. finitude], 3.4; SGA 7, Exp. XIII, 1.3).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-- The diagram chase behind
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_isIso`, for abstract
functors: the pullback exchange `αχ` of a composite `ρ ≫ ψ` of morphisms of models over `𝟙 X`
(`hx`, the composition law) is split if `αρ` is invertible and `αψ` is split, with `n` times the
idempotent a sum of natural endomorphisms `act₁ i` of `Ψ₁` intertwined by `αρ` with natural
endomorphisms `act i` of `Ψ`. -/
private lemma retraction_of_comp_of_isIso_aux {DX DM DT DS : Type*} [Category DX] [Category DM]
    [Category DT] [Category DS] [Preadditive DT] [Preadditive DS] {L₀ : DX ⥤ DX} {Lfg : DM ⥤ DS}
    {Lg : DM ⥤ DT} {Lf : DT ⥤ DS} [Lf.Additive] {ΨM : DX ⥤ DM} {Ψ₁ : DX ⥤ DT} {Ψ : DX ⥤ DS}
    (αχ : ΨM ⋙ Lfg ⟶ L₀ ⋙ Ψ) (αψ : ΨM ⋙ Lg ⟶ L₀ ⋙ Ψ₁) (αρ : Ψ₁ ⋙ Lf ⟶ L₀ ⋙ Ψ)
    (c₀ : L₀ ≅ L₀ ⋙ L₀) (c₁ : Lfg ≅ Lg ⋙ Lf) (A : DX)
    (hx : αχ.app A ≫ Ψ.map (c₀.hom.app A) =
      c₁.hom.app (ΨM.obj A) ≫ Lf.map (αψ.app A) ≫ αρ.app (L₀.obj A))
    [IsIso (αρ.app (L₀.obj A))]
    (r : (L₀ ⋙ Ψ₁).obj A ⟶ (ΨM ⋙ Lg).obj A) (hr : αψ.app A ≫ r = 𝟙 _)
    {ι : Type*} (s : Finset ι) (n : ℕ) (act₁ : ι → (Ψ₁.obj (L₀.obj A) ⟶ Ψ₁.obj (L₀.obj A)))
    (act : ι → ∀ C, Ψ.obj C ⟶ Ψ.obj C)
    (hact : ∀ i {C C'} (g : C ⟶ C'), act i C ≫ Ψ.map g = Ψ.map g ≫ act i C')
    (havg : n • (r ≫ αψ.app A) = ∑ i ∈ s, act₁ i)
    (hcomm : ∀ i, αρ.app (L₀.obj A) ≫ act i (L₀.obj (L₀.obj A)) =
      Lf.map (act₁ i) ≫ αρ.app (L₀.obj A)) :
    ∃ r', αχ.app A ≫ r' = 𝟙 _ ∧ n • (r' ≫ αχ.app A) = ∑ i ∈ s, act i (L₀.obj A) := by
  have hχ : αχ.app A = c₁.hom.app (ΨM.obj A) ≫ Lf.map (αψ.app A) ≫ αρ.app (L₀.obj A) ≫
      Ψ.map (c₀.inv.app A) := by
    rw [← reassoc_of% hx, ← Ψ.map_comp, Iso.hom_inv_id_app, Ψ.map_id, Category.comp_id]
  refine ⟨Ψ.map (c₀.hom.app A) ≫ inv (αρ.app (L₀.obj A)) ≫ Lf.map r ≫ c₁.inv.app (ΨM.obj A),
    ?_, ?_⟩
  · have k₁ : Ψ.map (c₀.inv.app A) ≫ Ψ.map (c₀.hom.app A) = 𝟙 _ := by
      rw [← Ψ.map_comp, Iso.inv_hom_id_app]
      exact Ψ.map_id _
    have k₂ : Lf.map (αψ.app A) ≫ Lf.map r = 𝟙 _ := by
      rw [← Lf.map_comp, hr, Lf.map_id]
    rw [hχ]
    simp only [Category.assoc, reassoc_of% k₁, IsIso.hom_inv_id_assoc, reassoc_of% k₂,
      Iso.hom_inv_id_app]
    rfl
  · have he : (Ψ.map (c₀.hom.app A) ≫ inv (αρ.app (L₀.obj A)) ≫ Lf.map r ≫
        c₁.inv.app (ΨM.obj A)) ≫ αχ.app A =
        Ψ.map (c₀.hom.app A) ≫ inv (αρ.app (L₀.obj A)) ≫ Lf.map (r ≫ αψ.app A) ≫
          αρ.app (L₀.obj A) ≫ Ψ.map (c₀.inv.app A) := by
      rw [hχ]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Lf.map_comp]
    rw [he, ← Preadditive.comp_nsmul, ← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp,
      ← Lf.map_nsmul, havg, Lf.map_sum, Preadditive.sum_comp, Preadditive.comp_sum,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← reassoc_of% (hcomm i), IsIso.inv_hom_id_assoc,
      ← reassoc_of% (hact i (c₀.hom.app A)), ← Ψ.map_comp, Iso.hom_inv_id_app, Ψ.map_id,
      Category.comp_id]

private lemma eq_id_of_intertwining_of_epi_aux {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A : D} {B : E} (f : A ⟶ A) (g : B ⟶ B) (e : F.obj A ⟶ B)
    [Epi e] (h : e ≫ g = F.map f ≫ e) (hf : f = 𝟙 A) : g = 𝟙 B := by
  rw [hf, F.map_id, Category.id_comp] at h
  exact (cancel_epi e).1 (h.trans (Category.comp_id e).symm)

/-- Transfer trivial actions and an averaged retraction through an equivariant isomorphism. -/
private lemma stabilization_of_equivariant_iso_aux {DX DM DT DS : Type*}
    [Category DX] [Category DM] [Category DT] [Category DS]
    [Preadditive DT] [Preadditive DS] {L₀ : DX ⥤ DX} {Lfg : DM ⥤ DS}
    {Lg : DM ⥤ DT} {Lf : DT ⥤ DS} [Lf.Additive]
    {ΨM : DX ⥤ DM} {Ψ₁ : DX ⥤ DT} {Ψ : DX ⥤ DS}
    (αχ : ΨM ⋙ Lfg ⟶ L₀ ⋙ Ψ) (αψ : ΨM ⋙ Lg ⟶ L₀ ⋙ Ψ₁) (αρ : Ψ₁ ⋙ Lf ⟶ L₀ ⋙ Ψ)
    (c₀ : L₀ ≅ L₀ ⋙ L₀) (c₁ : Lfg ≅ Lg ⋙ Lf) (A : DX)
    (hx : αχ.app A ≫ Ψ.map (c₀.hom.app A) =
      c₁.hom.app (ΨM.obj A) ≫ Lf.map (αψ.app A) ≫ αρ.app (L₀.obj A))
    (hiso : IsIso (αρ.app (L₀.obj A)))
    {G ι : Type*} (H : Set G) (π : G → ι) (lift : ι → G) (hlift : ∀ i, π (lift i) = i)
    (s : Finset ι) (n : ℕ) (act₁ : ι → (Ψ₁.obj (L₀.obj A) ⟶ Ψ₁.obj (L₀.obj A)))
    (act : G → ∀ C, Ψ.obj C ⟶ Ψ.obj C)
    (hact : ∀ σ {C C'} (g : C ⟶ C'), act σ C ≫ Ψ.map g = Ψ.map g ≫ act σ C')
    (hfix : ∀ σ ∈ H, act₁ (π σ) = 𝟙 _)
    (hsplit : ∃ r, αψ.app A ≫ r = 𝟙 _ ∧ n • (r ≫ αψ.app A) = ∑ i ∈ s, act₁ i)
    (hcomm : ∀ σ, αρ.app (L₀.obj A) ≫ act σ (L₀.obj (L₀.obj A)) =
      Lf.map (act₁ (π σ)) ≫ αρ.app (L₀.obj A)) :
    (∀ σ ∈ H, act σ (L₀.obj A) = 𝟙 _) ∧
      ∃ r, αχ.app A ≫ r = 𝟙 _ ∧ n • (r ≫ αχ.app A) = ∑ i ∈ s, act (lift i) (L₀.obj A) := by
  constructor
  · intro σ hσ
    exact eq_id_of_naturality_of_iso (act σ) (hact σ) (c₀.app A)
      (eq_id_of_intertwining_of_epi_aux Lf _ _ _ (hcomm σ) (hfix σ hσ))
  · obtain ⟨r, hr, havg⟩ := hsplit
    exact retraction_of_comp_of_isIso_aux αχ αψ αρ c₀ c₁ A hx r hr s n act₁
      (fun i ↦ act (lift i)) (fun i ↦ hact (lift i)) havg
      (fun i ↦ by simpa only [hlift i] using hcomm (lift i))

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]
  (L' : IntermediateField L Ω)

lemma specMap_algebraMap_intermediateField :
    Spec.map (CommRingCat.ofHom (algebraMap L' Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L L')) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The morphism of Galois layers `N_Ω ⟶ N_{L'}` for an intermediate field `L ⊆ L' ⊆ Ω`, over
the identities: the identity of total spaces and the change of fibres
`N.generic ×_L Spec Ω ⟶ N.generic ×_L Spec L'` on generic fibres. -/
@[simps]
noncomputable def galoisLayerRestrict :
    (N.galoisLayer h Ω).Hom (N.galoisLayer h L') (𝟙 X) (𝟙 X') where
  total := 𝟙 _
  generic := Limits.pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap L' Ω)))
    (𝟙 _) (by simp) (specMap_algebraMap_intermediateField Ω L').symm
  comm_j := by simp [galoisLayer]
  comm_i := (Category.id_comp _).trans (Category.comp_id _).symm
  comm_ε := by simp [galoisLayer]

/-- The change of Galois layers followed by the projection of the finite layer is the projection
of `N_Ω`. -/
lemma galoisLayerRestrict_generic_comp :
    (N.galoisLayerRestrict h Ω L').generic ≫ (N.galoisLayerHom h L').generic =
      (N.galoisLayerHom h Ω).generic := by
  simp

/-- The change of Galois layers is equivariant along the restriction `Gal(Ω/L) ⟶ Gal(L'/L)`. -/
lemma galoisLayerAut_generic_comp_galoisLayerRestrict_generic [Normal L L'] (σ : Ω ≃ₐ[L] Ω) :
    (N.galoisLayerAut h Ω σ).generic ≫ (N.galoisLayerRestrict h Ω L').generic =
      (N.galoisLayerRestrict h Ω L').generic ≫
        (N.galoisLayerAut h L' (σ.restrictNormal L')).generic := by
  refine Limits.pullback.hom_ext ?_ ?_
  · simp
  · simp only [galoisLayerAut_generic, galoisLayerRestrict_generic, Category.assoc,
      Limits.pullback.lift_snd, pullbackAction_snd, pullbackAction_snd_assoc,
      Limits.pullback.lift_snd_assoc]
    rw [specGaloisAction, specGaloisAction, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    exact (AlgEquiv.restrictNormal_commutes σ L' x).symm

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The change of Galois layers intertwines the Galois actions**: the pullback exchange `β` of
`N_Ω ⟶ N_{L'}` carries the action of `σ|_{L'}` on `Ψ_{N_{L'}}` to that of `σ` on `Ψ_{N_Ω}`. -/
lemma pullbackExchange_galoisLayerRestrict_app_comp_autAction [Normal L L'] (σ : Ω ≃ₐ[L] Ω)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((N.galoisLayerRestrict h Ω L').pullbackExchange Λ).app C ≫
        (N.galoisLayerAut h Ω σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) =
      L((𝟙 X')^*⟦Λ⟧).map ((N.galoisLayerAut h L' (σ.restrictNormal L')).autAction Λ C) ≫
        ((N.galoisLayerRestrict h Ω L').pullbackExchange Λ).app C :=
  Hom.pullbackExchange_app_comp_autAction_of_comm Λ _ _ _ (by simp)
    (N.galoisLayerAut_generic_comp_galoisLayerRestrict_generic h Ω L' σ) C

/-- An element of `Gal(Ω/L')` restricts to the identity of `L'`. -/
lemma restrictNormal_eq_one_of_mem_fixingSubgroup [Normal L L'] {σ : Ω ≃ₐ[L] Ω}
    (hσ : σ ∈ L'.fixingSubgroup) : σ.restrictNormal L' = 1 := by
  ext x
  exact (AlgEquiv.restrictNormal_commutes σ L' x).trans
    ((IntermediateField.mem_fixingSubgroup_iff L' σ).1 hσ x x.2)

private lemma galoisLayerAction_restrict_eq_id_of_mem_fixingSubgroup [Normal L L']
    (σ : Ω ≃ₐ[L] Ω) (hσ : σ ∈ L'.fixingSubgroup)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (N.galoisLayerAut h L' (σ.restrictNormal L')).autAction Λ C = 𝟙 _ :=
  (congrArg (fun τ ↦ (N.galoisLayerAut h L' τ).autAction Λ C)
    (restrictNormal_eq_one_of_mem_fixingSubgroup Ω L' hσ)).trans
      (N.galoisLayerAction_one Λ h L' C)

/-- **Nearby cycles of a Galois layer stabilizing at a finite level are the invariants of a
finite quotient.** Let `L ⊆ L' ⊆ Ω` with `L'/L` finite Galois, and suppose the pullback exchange
of the change of Galois layers `N_Ω ⟶ N_{L'}` is invertible at `L(𝟙)^* C` (stabilization at the
level `L'`). If `|Gal(L'/L)|` is invertible on `Lε^* C`, then:
* every `σ ∈ Gal(Ω/L')` acts trivially on `Ψ_{N_Ω} (L(𝟙)^* C)`;
* the pullback exchange `α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_Ω} (L(𝟙)^* C)` of the projection `N_Ω ⟶ N` has
  a retraction `r` with `|Gal(L'/L)| • (r ≫ α) = ∑_{τ ∈ Gal(L'/L)} τ̃_*`, the sum of the actions
  of lifts `τ̃ ∈ Gal(Ω/L)` (`τ̃|_{L'} = τ`).

The exchange `α` is the composite of the exchange of the finite layer `N_{L'} ⟶ N`, split by
the averaged Galois action
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_autAction`), and of the
invertible exchange of `N_Ω ⟶ N_{L'}`, which intertwines the Galois actions
(`NearbyCyclesModel.pullbackExchange_galoisLayerRestrict_app_comp_autAction`). -/
theorem exists_retraction_pullbackExchange_galoisLayerHom_of_isIso [FiniteDimensional L L']
    [IsGalois L L']
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    [IsIso (Fintype.card (L' ≃ₐ[L] L') • 𝟙 (L((N.ε)^*⟦Λ⟧).obj C))]
    (hstab : IsIso (((N.galoisLayerRestrict h Ω L').pullbackExchange Λ).app
      (L((𝟙 X)^*⟦Λ⟧).obj C)))
    (lift : (L' ≃ₐ[L] L') → (Ω ≃ₐ[L] Ω)) (hlift : ∀ τ, (lift τ).restrictNormal L' = τ) :
    (∀ σ ∈ L'.fixingSubgroup,
      (N.galoisLayerAut h Ω σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) = 𝟙 _) ∧
    ∃ r, ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      Fintype.card (L' ≃ₐ[L] L') • (r ≫ ((N.galoisLayerHom h Ω).pullbackExchange Λ).app C) =
        ∑ τ, (N.galoisLayerAut h Ω (lift τ)).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) := by
  have hx := (N.galoisLayerRestrict h Ω L').pullbackExchange_comp_app_of_eq Λ
    (N.galoisLayerHom h L') (N.galoisLayerHom h Ω) (Category.id_comp (𝟙 X))
    (Category.id_comp (𝟙 X')) (by simp) (N.galoisLayerRestrict_generic_comp h Ω L') C
  have hfix := N.galoisLayerAction_restrict_eq_id_of_mem_fixingSubgroup h Ω L' Λ
  have hsplit := N.exists_retraction_pullbackExchange_galoisLayerHom_autAction Λ h L' C
  have hcomm := N.pullbackExchange_galoisLayerRestrict_app_comp_autAction h Ω L' Λ
  have key := stabilization_of_equivariant_iso_aux
    (G := Ω ≃ₐ[L] Ω) (ι := L' ≃ₐ[L] L')
    ((N.galoisLayerHom h Ω).pullbackExchange Λ)
    ((N.galoisLayerHom h L').pullbackExchange Λ)
    ((N.galoisLayerRestrict h Ω L').pullbackExchange Λ)
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X)))
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp (𝟙 X'))) C hx hstab
    (L'.fixingSubgroup : Set (Ω ≃ₐ[L] Ω)) (fun σ ↦ σ.restrictNormal L') lift hlift
    Finset.univ (Fintype.card (L' ≃ₐ[L] L'))
    (fun τ ↦ (N.galoisLayerAut h L' τ).autAction Λ _)
    (fun σ C' ↦ (N.galoisLayerAut h Ω σ).autAction Λ C')
    (fun σ _ _ g ↦ Hom.autAction_naturality Λ _ g)
    (fun σ hσ ↦ hfix σ hσ _) hsplit (fun σ ↦ hcomm σ _)
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
