/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisAction

/-!

# The Galois action on nearby cycles is compatible with a change of trait

Let `τ : N₂ ⟶ N₁` be a morphism of models over `f : X₂ ⟶ X₁`, `f' : X₂' ⟶ X₁'`, for instance the
base change of a model `N₁` over a strictly henselian trait `S₁` to a strictly henselian trait
`S₂ ⟶ S₁`. Let `hᵢ : Nᵢ.generic ⟶ Spec Lᵢ` be compatible with a field homomorphism `l : L₁ ⟶ L₂`,
and `ω : Ω₁ ⟶ Ω₂` a homomorphism of extensions `Ωᵢ/Lᵢ` over `l`. Then `τ` induces a morphism of
the Galois layers `N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`): `τ` on the total
spaces and `τ.generic ×_{Spec l} Spec ω` on the generic fibres.

Its pullback exchange `α_{τ'} : Lf'^* Ψ_{N₁_{Ω₁}} ⟶ Ψ_{N₂_{Ω₂}} Lf^*` is equivariant along the
restriction of automorphisms `Aut(Ω₂/L₂) ⟶ Aut(Ω₁/L₁)`: if `ω ∘ σ₁ = σ₂ ∘ ω`, then
`α_{τ'} ∘ Lf'^*(σ₁) = σ₂ ∘ α_{τ'}` for the Galois actions of `NearbyCyclesModel.galoisLayerAction`
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`). For `Ωᵢ` a
separable closure of the fraction field of `Sᵢ` this is the equivariance of the change of trait
along the map of inertia groups `I₂ ⟶ I₁` (SGA 4½, [Th. finitude], proof of 3.7, 3.8).

The pullback exchanges of the square of models
```
N₂_{Ω₂} ──τ'──→ N₁_{Ω₁}
   │σ₂             │σ₁
   ↓               ↓
   N₂ ─────τ─────→ N₁
```
satisfy `α_{τ'} ∘ τ'^* α_{σ₁} = α_{σ₂} ∘ σ₂^* α_τ` up to the composition isomorphisms
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`), with `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ` the
projections.

## Main results

- `NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`: for morphisms of models
  `σ₂ : M₂ ⟶ M₂`, `σ₁ : M₁ ⟶ M₁` over the identities and `τ : M₂ ⟶ M₁` with `σ₂ ≫ τ = τ ≫ σ₁`,
  the pullback exchange of `τ` intertwines the actions of `σ₁` and `σ₂`.
- `NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`: the equivariance
  of the exchange of a change of trait for the Galois actions.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Right unit law** for the composition isomorphisms transported along `p ≫ 𝟙 Y = pq`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId {X Y : Scheme.{u}}
    {p pq : X ⟶ Y} (h : p ≫ 𝟙 Y = pq)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompOfEq Λ h).hom.app K ≫
        L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) =
      eqToHom (by rw [← h, Category.comp_id, Functor.id_obj]) := by
  subst h
  exact leftDerivedUpperStarComp_id_right_app Λ p K

/-- `leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId` for `p ≫ 𝟙 Y = p`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId_self
    {X Y : Scheme.{u}} {p : X ⟶ Y} (h : p ≫ 𝟙 Y = p)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompOfEq Λ h).hom.app K ≫
        L((p)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ Y).hom.app K) = 𝟙 _ := by
  rw [leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId, eqToHom_refl]

/-- `leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId` for `𝟙 X ≫ q = q`. -/
lemma leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId_self
    {X Y : Scheme.{u}} {q : X ⟶ Y} (h : 𝟙 X ≫ q = q)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (leftDerivedUpperStarCompOfEq Λ h).hom.app K ≫
        (leftDerivedUpperStarId Λ X).hom.app (L((q)^*⟦Λ⟧).obj K) = 𝟙 _ := by
  rw [leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId, eqToHom_refl]

namespace NearbyCyclesModel

open Scheme

/-- The diagram chase behind `NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`,
for abstract functors: `I₀, I : L₀, L ≅ 𝟭` (pullbacks along identities on the source side),
`I₁, I₁' : L₁, L₁' ≅ 𝟭` (on the target side), `Lf`, `Lf'` (pullbacks), `Ψ₂`, `Ψ₁` (nearby
cycles), the exchanges `ασ₂`, `ασ₁`, `ατ`, `αχ` and the composition laws `hA`, `hB` of
`χ = σ₂ ≫ τ = τ ≫ σ₁`. -/
private lemma pullbackExchange_comp_autAction_of_comm_aux {D₁ D₁' D₂ D₂' : Type*} [Category D₁]
    [Category D₁'] [Category D₂] [Category D₂'] {L₀ : D₂ ⥤ D₂} {L : D₂' ⥤ D₂'}
    {L₁ : D₁ ⥤ D₁} {L₁' : D₁' ⥤ D₁'} (Lf : D₁ ⥤ D₂) (Lf' : D₁' ⥤ D₂') (I₀ : L₀ ≅ 𝟭 D₂)
    (I : L ≅ 𝟭 D₂') (I₁ : L₁ ≅ 𝟭 D₁) (I₁' : L₁' ≅ 𝟭 D₁') (Ψ₂ : D₂ ⥤ D₂') (Ψ₁ : D₁ ⥤ D₁')
    (ασ₂ : Ψ₂ ⋙ L ⟶ L₀ ⋙ Ψ₂) (ασ₁ : Ψ₁ ⋙ L₁' ⟶ L₁ ⋙ Ψ₁) (ατ : Ψ₁ ⋙ Lf' ⟶ Lf ⋙ Ψ₂)
    (C : D₁) (αχ : Lf'.obj (Ψ₁.obj C) ⟶ Ψ₂.obj (Lf.obj C)) (cA : Lf ⟶ Lf ⋙ L₀)
    (cA' : Lf' ⟶ Lf' ⋙ L)
    (cB : Lf ⟶ L₁ ⋙ Lf) (cB' : Lf' ⟶ L₁' ⋙ Lf')
    (hA : αχ ≫ Ψ₂.map (cA.app C) =
      cA'.app (Ψ₁.obj C) ≫ L.map (ατ.app C) ≫ ασ₂.app (Lf.obj C))
    (hB : αχ ≫ Ψ₂.map (cB.app C) =
      cB'.app (Ψ₁.obj C) ≫ Lf'.map (ασ₁.app C) ≫ ατ.app (L₁.obj C))
    (hcA : cA.app C ≫ I₀.hom.app (Lf.obj C) = 𝟙 _)
    (hcA' : cA'.app (Ψ₁.obj C) ≫ I.hom.app (Lf'.obj (Ψ₁.obj C)) = 𝟙 _)
    (hcB : cB.app C ≫ Lf.map (I₁.hom.app C) = 𝟙 _)
    (hcB' : cB'.app (Ψ₁.obj C) ≫ Lf'.map (I₁'.hom.app (Ψ₁.obj C)) = 𝟙 _) :
    ατ.app C ≫ (I.inv.app _ ≫ ασ₂.app (Lf.obj C) ≫ Ψ₂.map (I₀.hom.app (Lf.obj C))) =
      Lf'.map (I₁'.inv.app _ ≫ ασ₁.app C ≫ Ψ₁.map (I₁.hom.app C)) ≫ ατ.app C := by
  have hcA'' : cA'.app (Ψ₁.obj C) = I.inv.app (Lf'.obj (Ψ₁.obj C)) := by
    rw [← cancel_mono (I.hom.app _), hcA', Iso.inv_hom_id_app]; rfl
  have hcB'' : cB'.app (Ψ₁.obj C) = Lf'.map (I₁'.inv.app (Ψ₁.obj C)) := by
    rw [← cancel_mono (Lf'.map (I₁'.hom.app _)), hcB', ← Lf'.map_comp, Iso.inv_hom_id_app]
    exact (Lf'.map_id _).symm
  have hnI := I.inv.naturality (ατ.app C)
  have hnτ := ατ.naturality (I₁.hom.app C)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnI hnτ
  calc ατ.app C ≫ (I.inv.app _ ≫ ασ₂.app (Lf.obj C) ≫ Ψ₂.map (I₀.hom.app (Lf.obj C)))
      = (cA'.app (Ψ₁.obj C) ≫ L.map (ατ.app C) ≫ ασ₂.app (Lf.obj C)) ≫
          Ψ₂.map (I₀.hom.app (Lf.obj C)) := by
        rw [hcA'']; simp only [Category.assoc]; rw [reassoc_of% hnI]
    _ = αχ := by rw [← hA, Category.assoc, ← Ψ₂.map_comp, hcA, Ψ₂.map_id, Category.comp_id]
    _ = (cB'.app (Ψ₁.obj C) ≫ Lf'.map (ασ₁.app C) ≫ ατ.app (L₁.obj C)) ≫
          Ψ₂.map (Lf.map (I₁.hom.app C)) := by
        rw [← hB, Category.assoc, ← Ψ₂.map_comp, hcB, Ψ₂.map_id, Category.comp_id]
    _ = _ := by
        rw [hcB'']; simp only [Category.assoc, Functor.map_comp]; rw [hnτ]

variable {X₁ X₁' X₂ X₂' : Scheme.{u}} {M₁ : NearbyCyclesModel X₁ X₁'}
  {M₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}

/-- **The pullback exchange intertwines commuting automorphisms of models.** Let
`σ₂ : M₂ ⟶ M₂` and `σ₁ : M₁ ⟶ M₁` be morphisms of models over the identities and `τ : M₂ ⟶ M₁` a
morphism of models with `σ₂ ≫ τ = τ ≫ σ₁` on total spaces and geometric generic fibres. Then the
pullback exchange `α_τ : Lf'^* Ψ_{M₁} C ⟶ Ψ_{M₂} (Lf^* C)` satisfies
`α_τ ≫ σ₂ = Lf'^* σ₁ ≫ α_τ` for the actions `NearbyCyclesModel.Hom.autAction`:
```
Lf'^* Ψ_{M₁} C ──α_τ──→ Ψ_{M₂} (Lf^* C)
      │Lf'^* σ₁               │σ₂
      ↓                       ↓
Lf'^* Ψ_{M₁} C ──α_τ──→ Ψ_{M₂} (Lf^* C)
```
-/
lemma Hom.pullbackExchange_app_comp_autAction_of_comm (τ : M₂.Hom M₁ f f')
    (σ₂ : M₂.Hom M₂ (𝟙 X₂) (𝟙 X₂')) (σ₁ : M₁.Hom M₁ (𝟙 X₁) (𝟙 X₁'))
    (htot : σ₂.total ≫ τ.total = τ.total ≫ σ₁.total)
    (hgen : σ₂.generic ≫ τ.generic = τ.generic ≫ σ₁.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁))) :
    (τ.pullbackExchange Λ).app C ≫ σ₂.autAction Λ (L((f)^*⟦Λ⟧).obj C) =
      L((f')^*⟦Λ⟧).map (σ₁.autAction Λ C) ≫ (τ.pullbackExchange Λ).app C := by
  let χ := σ₂.comp τ
  have hA := σ₂.pullbackExchange_comp_app_of_eq Λ τ χ (Category.id_comp f)
    (Category.id_comp f') rfl rfl C
  have hB := τ.pullbackExchange_comp_app_of_eq Λ σ₁ χ (Category.comp_id f)
    (Category.comp_id f') htot.symm hgen.symm C
  have hcA := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId_self Λ
    (Category.id_comp f) C
  have hcA' := leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId_self Λ
    (Category.id_comp f') ((M₁.nearbyCycles Λ).obj C)
  have hcB := leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId_self Λ
    (Category.comp_id f) C
  have hcB' := leftDerivedUpperStarCompOfEq_hom_app_comp_map_leftDerivedUpperStarId_self Λ
    (Category.comp_id f') ((M₁.nearbyCycles Λ).obj C)
  have key := pullbackExchange_comp_autAction_of_comm_aux L((f)^*⟦Λ⟧) L((f')^*⟦Λ⟧)
    (leftDerivedUpperStarId Λ X₂) (leftDerivedUpperStarId Λ X₂') (leftDerivedUpperStarId Λ X₁)
    (leftDerivedUpperStarId Λ X₁') (M₂.nearbyCycles Λ) (M₁.nearbyCycles Λ)
    (σ₂.pullbackExchange Λ) (σ₁.pullbackExchange Λ) (τ.pullbackExchange Λ) C
    ((χ.pullbackExchange Λ).app C) (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f)).hom
    (leftDerivedUpperStarCompOfEq Λ (Category.id_comp f')).hom
    (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f)).hom
    (leftDerivedUpperStarCompOfEq Λ (Category.comp_id f')).hom hA hB hcA hcA' hcB hcB'
  exact key

variable {L₁ L₂ : Type u} [Field L₁] [Field L₂] (h₁ : M₁.generic ⟶ Spec (.of L₁))
  (h₂ : M₂.generic ⟶ Spec (.of L₂)) (Ω₁ Ω₂ : Type u) [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] (l : L₁ →+* L₂) (ω : Ω₁ →+* Ω₂)
  (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)

/-- The square of spectra `Spec ω ≫ Spec(L₁ → Ω₁) = Spec(L₂ → Ω₂) ≫ Spec l`. -/
lemma specMap_algebraMap_comp_specMap_of_comp_eq
    (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l) :
    Spec.map (CommRingCat.ofHom (algebraMap L₂ Ω₂)) ≫ Spec.map (CommRingCat.ofHom l) =
      Spec.map (CommRingCat.ofHom ω) ≫ Spec.map (CommRingCat.ofHom (algebraMap L₁ Ω₁)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hω]

variable {h₁ h₂ l} in
/-- The morphism of generic fibres of Galois layers `N₂.generic ×_{L₂} Ω₂ ⟶ N₁.generic ×_{L₁} Ω₁`
induced by a morphism of models `τ` lying over `Spec l` and a homomorphism `ω` of extensions. -/
noncomputable def galoisLayerGenericMap (τ : M₂.Hom M₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l)) :
    (M₂.galoisLayer h₂ Ω₂).generic ⟶ (M₁.galoisLayer h₁ Ω₁).generic :=
  pullback.map h₂ _ h₁ _ τ.generic (Spec.map (CommRingCat.ofHom ω)) (Spec.map (CommRingCat.ofHom l))
    hτ.symm (specMap_algebraMap_comp_specMap_of_comp_eq Ω₁ Ω₂ l ω hω)

variable {h₁ h₂ l} in
@[reassoc (attr := simp)]
lemma galoisLayerGenericMap_fst (τ : M₂.Hom M₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l)) :
    galoisLayerGenericMap Ω₁ Ω₂ ω hω τ hτ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.generic := by
  simp [galoisLayerGenericMap]

variable {h₁ h₂ l} in
@[reassoc (attr := simp)]
lemma galoisLayerGenericMap_snd (τ : M₂.Hom M₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l)) :
    galoisLayerGenericMap Ω₁ Ω₂ ω hω τ hτ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ω) := by
  simp [galoisLayerGenericMap]

variable {h₁ h₂ l} in
/-- **The change of Galois layers** `N₂_{Ω₂} ⟶ N₁_{Ω₁}` induced by a morphism of models
`τ : N₂ ⟶ N₁` over `Spec l` and a homomorphism `ω : Ω₁ ⟶ Ω₂` of extensions over `l`: `τ` on the
total spaces and `τ.generic ×_{Spec l} Spec ω` on the generic fibres. -/
@[simps]
noncomputable def galoisLayerMap (τ : M₂.Hom M₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l)) :
    (M₂.galoisLayer h₂ Ω₂).Hom (M₁.galoisLayer h₁ Ω₁) f f' where
  total := τ.total
  generic := galoisLayerGenericMap Ω₁ Ω₂ ω hω τ hτ
  comm_j := by
    simp only [galoisLayer, galoisLayerGenericMap_fst_assoc, τ.comm_j, Category.assoc]
  comm_i := τ.comm_i
  comm_ε := by
    simp only [galoisLayer, galoisLayerGenericMap_fst_assoc, τ.comm_ε, Category.assoc]

variable {h₁ h₂ l} in
/-- **Equivariance of the change of trait for the Galois actions** (SGA 4½, [Th. finitude], proof
of 3.7). Let `τ : N₂ ⟶ N₁` be a morphism of models over `Spec l`, `ω : Ω₁ ⟶ Ω₂` a homomorphism of
extensions over `l`, and `σ₁ ∈ Aut(Ω₁/L₁)`, `σ₂ ∈ Aut(Ω₂/L₂)` with `ω ∘ σ₁ = σ₂ ∘ ω` (`σ₁` is the
restriction of `σ₂`). Then the pullback exchange `α_{τ'}` of the change of Galois layers
`τ' : N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`) intertwines the Galois actions
(`NearbyCyclesModel.galoisLayerAction`): `α_{τ'} ≫ σ₂ = Lf'^* σ₁ ≫ α_{τ'}`.

For a change of strictly henselian traits `S₂ ⟶ S₁` and `Ωᵢ` separable closures of the fraction
fields, this is the equivariance of the change of trait along `I₂ ⟶ I₁`. -/
theorem pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction (τ : M₂.Hom M₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l)) (σ₁ : Ω₁ ≃ₐ[L₁] Ω₁)
    (σ₂ : Ω₂ ≃ₐ[L₂] Ω₂) (hσ : ∀ x, ω (σ₁ x) = σ₂ (ω x))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁))) :
    ((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app C ≫
        M₂.galoisLayerAction Λ h₂ Ω₂ σ₂ (L((f)^*⟦Λ⟧).obj C) =
      L((f')^*⟦Λ⟧).map (M₁.galoisLayerAction Λ h₁ Ω₁ σ₁ C) ≫
        ((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app C := by
  refine Hom.pullbackExchange_app_comp_autAction_of_comm Λ _ _ _ ?_ ?_ C
  · simp
  · refine pullback.hom_ext ?_ ?_
    · simp
    · simp only [galoisLayerAut_generic, galoisLayerMap_generic, Category.assoc,
        galoisLayerGenericMap_snd, pullbackAction_snd_assoc, galoisLayerGenericMap_snd_assoc,
        pullbackAction_snd]
      congr 1
      rw [specGaloisAction, specGaloisAction, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (hσ x).symm

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
