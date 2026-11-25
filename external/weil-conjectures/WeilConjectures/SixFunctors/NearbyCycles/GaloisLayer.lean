/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFieldCover
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionComp
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeGenericUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisCoverTrace

/-!

# Finite Galois layers of the generic fibre of a model

Let `N` be a model of `X` with special fibre `X'`, let `h : N.generic ⟶ Spec L` be a morphism to
the spectrum of a field and let `L'/L` be a finite Galois extension with group `Γ`. The
*Galois layer* `N_{L'}` (`NearbyCyclesModel.galoisLayer`) is the model with the total space and
special fibre of `N` and generic fibre `G = N.generic ×_{Spec L} Spec L'`, mapped to `N` by the
projection `g : G ⟶ N.generic` (`NearbyCyclesModel.galoisLayerHom`). The group `Γ` acts on
`N_{L'}` over the identities (`NearbyCyclesModel.galoisLayerAut`), and this action on the nearby
cycles is multiplicative (`NearbyCyclesModel.galoisLayerAut_autAction_mul`). This is the step
"finite layers" of SGA 4½ [Th. finitude] §3.

## Main results

- `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom`: if multiplication by
  `|Γ|` is invertible on `Lε^* C`, the pullback exchange `α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_{L'}} L(𝟙)^* C`
  of the projection has a retraction `r`, whose idempotent is the average of the transported
  derived Galois actions: `|Γ| • (r ≫ α) = ∑ σ, κ⁻¹ ≫ Ψ'(ρ_σ) ≫ κ`, for `Ψ' = Li^* Rj_*`, the
  derived action `ρ_σ` of `σ` on `Rg_* Lg^*` and the canonical isomorphism
  `κ : Li^* Rj_* Rg_* Lg^* Lε^* C ≅ Ψ_{N_{L'}} L(𝟙)^* C`
  (`NearbyCyclesModel.galoisLayerExchangeIso`).

The proof computes `α` as `Ψ'` of the unit of `Lg^* ⊣ Rg_*` up to canonical isomorphisms
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`) and splits that unit by the
normalized derived Galois trace (`ProEtale.CondensedRing.derivedUnit_comp_normalizedTrace`); the
abstract part is `CategoryTheory.exists_retraction_of_eq_comp_map_comp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- **Transporting a split averaging unit along two functors.** Let `α = i ≫ F₂ (F₁ u ≫ c)` for an
isomorphism `i`, additive functors `F₁`, `F₂` and a morphism `c` with `F₂ c = κ` an isomorphism,
where `u` has a retraction `t` whose idempotent is an average, `n • (t ≫ u) = ∑ a, ρ a`. Then `α`
has a retraction `r` with `n • (r ≫ α) = ∑ a, κ⁻¹ ≫ F₂ (F₁ (ρ a)) ≫ κ`. -/
lemma exists_retraction_of_eq_comp_map_comp {C D E : Type*} [Category C] [Category D]
    [Category E] [Preadditive C] [Preadditive D] [Preadditive E] (F₁ : C ⥤ D) (F₂ : D ⥤ E)
    [F₁.Additive] [F₂.Additive] {A T : C} {W : D} {P : E} (α : P ⟶ F₂.obj W)
    (i : P ≅ F₂.obj (F₁.obj A)) (c : F₁.obj T ⟶ W) (κ : F₂.obj (F₁.obj T) ≅ F₂.obj W)
    (hκ : κ.hom = F₂.map c) (u : A ⟶ T) (t : T ⟶ A) (n : ℕ) {ι : Type*} [Fintype ι]
    (ρ : ι → (T ⟶ T)) (hα : α = i.hom ≫ F₂.map (F₁.map u ≫ c)) (hut : u ≫ t = 𝟙 A)
    (havg : n • (t ≫ u) = ∑ a, ρ a) :
    ∃ r : F₂.obj W ⟶ P, α ≫ r = 𝟙 P ∧
      n • (r ≫ α) = ∑ a, κ.inv ≫ F₂.map (F₁.map (ρ a)) ≫ κ.hom := by
  rw [F₂.map_comp, ← hκ] at hα
  refine ⟨κ.inv ≫ F₂.map (F₁.map t) ≫ i.inv, ?_, ?_⟩
  · rw [hα]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F₂.map_comp_assoc, ← F₁.map_comp, hut, F₁.map_id, F₂.map_id, Category.id_comp,
      Iso.hom_inv_id]
  · have h : (κ.inv ≫ F₂.map (F₁.map t) ≫ i.inv) ≫ α =
        κ.inv ≫ F₂.map (F₁.map (t ≫ u)) ≫ κ.hom := by
      rw [hα]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, F₁.map_comp, F₂.map_comp]
    rw [h, ← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp, ← F₂.map_nsmul, ← F₁.map_nsmul,
      havg, F₁.map_sum, F₂.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (L' : Type u) [Field L'] [Algebra L L']

/-- The **finite Galois layer** `N_{L'}` of a model `N` along `h : N.generic ⟶ Spec L` and a field
extension `L'/L`: the model with the total space and special fibre of `N`, generic fibre
`G = N.generic ×_{Spec L} Spec L'`, `j = g ≫ j_N` and `ε = g ≫ ε_N` for the projection
`g : G ⟶ N.generic`. -/
noncomputable def galoisLayer : NearbyCyclesModel X X' where
  total := N.total
  generic := pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L')))
  j := pullback.fst _ _ ≫ N.j
  i := N.i
  ε := pullback.fst _ _ ≫ N.ε

/-- The projection `N_{L'} ⟶ N` of the Galois layer, over the identities: the identity of the
total spaces and the projection `G ⟶ N.generic` of the generic fibres. -/
@[simps]
noncomputable def galoisLayerHom : (N.galoisLayer h L').Hom N (𝟙 X) (𝟙 X') where
  total := 𝟙 _
  generic := pullback.fst _ _
  comm_j := (Category.comp_id _).symm
  comm_i := (Category.id_comp _).trans (Category.comp_id _).symm
  comm_ε := (Category.comp_id _).symm

/-- The action of `σ ∈ Gal(L'/L)` on the Galois layer `N_{L'}`, over the identities: the identity
of the total spaces and the base change `pullbackAction` of `Spec σ` on the generic fibre. -/
@[simps]
noncomputable def galoisLayerAut (σ : L' ≃ₐ[L] L') :
    (N.galoisLayer h L').Hom (N.galoisLayer h L') (𝟙 X) (𝟙 X') where
  total := 𝟙 _
  generic := pullbackAction h _ (specGaloisAction_comp (F := L) (L := L')) σ
  comm_j := by
    simp only [galoisLayer, Category.comp_id, pullbackAction_fst_assoc]
  comm_i := (Category.id_comp _).trans (Category.comp_id _).symm
  comm_ε := by
    simp only [galoisLayer, Category.comp_id, pullbackAction_fst_assoc]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The Galois action on the nearby cycles of the Galois layer is multiplicative**: `σ * τ`
acts as `τ` followed by `σ` (the action `σ ↦ Spec σ` is a right action). -/
lemma galoisLayerAut_autAction_mul (σ τ : L' ≃ₐ[L] L')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (N.galoisLayerAut h L' (σ * τ)).autAction Λ C =
      (N.galoisLayerAut h L' τ).autAction Λ C ≫ (N.galoisLayerAut h L' σ).autAction Λ C :=
  Hom.autAction_comp_of_eq Λ _ _ _ (Category.id_comp _)
    (pullbackAction_mul _ _ specGaloisAction_comp specGaloisAction_mul σ τ) C

/-- The canonical isomorphism `κ : Li^* Rj_* Rg_* Lg^* Lε^* C ≅ Ψ_{N_{L'}} L(𝟙)^* C` for the
projection `g` of the Galois layer: the composition isomorphisms `Rj_* Rg_* ≅ R(g ≫ j)_*` and
`Lg^* Lε^* ≅ L(g ≫ ε)^*` and the identity isomorphism `L(𝟙)^* ≅ 𝟭`. -/
noncomputable def galoisLayerExchangeIso
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    L((N.i)^*⟦Λ⟧).obj (R((N.j)_*⟦Λ⟧).obj (R((pullback.fst h
      (Spec.map (CommRingCat.ofHom (algebraMap L L'))))_*⟦Λ⟧).obj
        (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L'))))^*⟦Λ⟧).obj
          (L((N.ε)^*⟦Λ⟧).obj C)))) ≅
      ((N.galoisLayer h L').nearbyCycles Λ).obj (L((𝟙 X)^*⟦Λ⟧).obj C) :=
  L((N.i)^*⟦Λ⟧).mapIso ((rightDerivedLowerStarComp Λ _ N.j).app _ ≪≫
    R((_ ≫ N.j)_*⟦Λ⟧).mapIso ((leftDerivedUpperStarComp Λ _ N.ε).symm.app C ≪≫
      L((_ ≫ N.ε)^*⟦Λ⟧).mapIso ((leftDerivedUpperStarId Λ X).symm.app C)))

variable [FiniteDimensional L L'] [IsGalois L L']

-- the pullback exchange and the derived Galois data are large terms
/-- **The pullback exchange of a finite Galois layer is split by the averaged Galois action.**
If multiplication by `|Gal(L'/L)|` is invertible on `Lε^* C`, the pullback exchange
`α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_{L'}} L(𝟙)^* C` of the projection `N_{L'} ⟶ N` has a retraction `r`
with `|Γ| • (r ≫ α) = ∑ σ, κ⁻¹ ≫ Li^* Rj_* (ρ_σ) ≫ κ`, where `ρ_σ` is the derived action of `σ`
on `Rg_* Lg^* Lε^* C` and `κ` is `NearbyCyclesModel.galoisLayerExchangeIso`: the image of `α` is
the space of invariants of the transported Galois action. -/
theorem exists_retraction_pullbackExchange_galoisLayerHom
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    [IsIso (Fintype.card (L' ≃ₐ[L] L') • 𝟙 (L((N.ε)^*⟦Λ⟧).obj C))] :
    ∃ r, ((N.galoisLayerHom h L').pullbackExchange Λ).app C ≫ r = 𝟙 _ ∧
      Fintype.card (L' ≃ₐ[L] L') • (r ≫ ((N.galoisLayerHom h L').pullbackExchange Λ).app C) =
        ∑ σ, (N.galoisLayerExchangeIso h L' Λ C).inv ≫
          L((N.i)^*⟦Λ⟧).map (R((N.j)_*⟦Λ⟧).map ((derivedGaloisAction Λ (pullback.fst _ _)
            (pullbackAction_fst h _ specGaloisAction_comp) σ).app (L((N.ε)^*⟦Λ⟧).obj C))) ≫
          (N.galoisLayerExchangeIso h L' Λ C).hom := by
  have hgal := IsGaloisAction.pullback h _ specGaloisAction_comp (isGaloisAction_spec (F := L)
    (L := L'))
  have hα := Hom.pullbackExchange_app_of_total_eq_id Λ N
    (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L')))) _ rfl
    (N.galoisLayerHom h L') rfl rfl C
  simp only [eqToHom_refl, Category.id_comp] at hα
  exact exists_retraction_of_eq_comp_map_comp R((N.j)_*⟦Λ⟧) L((N.i)^*⟦Λ⟧) _
    ((leftDerivedUpperStarId Λ X').app _) _ (N.galoisLayerExchangeIso h L' Λ C) rfl _ _ _ _ hα
    (derivedUnit_comp_normalizedTrace Λ _ _ (pullbackAction_mul _ _ _ specGaloisAction_mul)
      hgal _)
    (nsmul_normalizedTrace_comp_derivedUnit Λ _ _
      (pullbackAction_mul _ _ _ specGaloisAction_mul) hgal _)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
