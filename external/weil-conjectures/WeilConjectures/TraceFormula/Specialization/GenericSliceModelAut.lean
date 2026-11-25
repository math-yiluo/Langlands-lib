/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup

/-!

# Generic automorphisms acting on the generic slice model

Let `M` be a model over the trait `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and `x ∈ K`.
The generic slice model `M''` of `b` (`NearbyCyclesModel.genericSliceModel`, a model of the base
`X₂` of the generic slice) and the base change `M_b` of `M` along the slice
`Spec K⟦t⟧ ⟶ 𝔸¹_S` (`NearbyCyclesModel.baseChange`, a model of the base `X` of `M`) have the
same total space, geometric generic fibre and special fibre; they differ only by the
identification `ε` of the geometric generic fibre with a base. This file compares them:

* `NearbyCyclesModel.genericSliceToBaseChange`: the morphism of models `κ : M'' ⟶ M_b` over a map
  of bases `c : X₂ ⟶ X` compatible with the identifications `ε`, whose components are identities.
  Its pullback exchange is invertible.
* `NearbyCyclesModel.genericSliceAut`: a generic automorphism `σ` (`NearbyCyclesModel.GenericAut`,
  an element of the pro-`p` kernel `P'` of the map of inertia groups) acts on `M''` by a morphism of
  models over the identities, with the same components as its action
  `NearbyCyclesModel.baseChangeAut` on `M_b`. The action on nearby cycles is an
  anti-homomorphism (`NearbyCyclesModel.autAction_genericSliceAut_mul`).
* `NearbyCyclesModel.pullbackExchange_genericSliceToBaseChange_app_comp_autAction`: `κ`
  intertwines the two actions of `σ` on nearby cycles.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- A generic automorphism fixes the generic point `Spec Ω_K ⟶ Spec Frac K⟦t⟧` of the trait
`Spec K⟦t⟧`, the generic point of the trait being an open immersion. -/
lemma GenericAut.τ_comp_traitGenericPointToSpec (σ : GenericAut k' K) :
    σ.τ ≫ traitGenericPointToSpec K = traitGenericPointToSpec K := by
  rw [← cancel_mono (traitGenericSpec K), Category.assoc, traitGenericPointToSpec_traitGenericSpec,
    σ.over_trait]

/-- The action of a generic automorphism `σ` on the generic slice model `M''`: the morphism of
models over the identities which is the identity on the total space and `σ` on the geometric
generic fibre `𝒳'' ×_{K⟦t⟧} Spec Ω_K`. Its components are those of
`NearbyCyclesModel.baseChangeAut`. -/
noncomputable def genericSliceAut (σ : GenericAut k' K) :
    (genericSliceModel x hb).Hom (genericSliceModel x hb) (𝟙 _) (𝟙 _) where
  total := 𝟙 _
  generic := pullback.map _ _ _ _ (𝟙 _) σ.τ (𝟙 _) (by simp) (by simp [σ.over_trait])
  comm_j := by simp
  comm_i := by simp
  comm_ε := by
    simp only [genericSliceModel_ε, Category.comp_id]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp [σ.τ_comp_traitGenericPointToSpec]

@[simp]
lemma genericSliceAut_total (σ : GenericAut k' K) : (genericSliceAut x hb σ).total = 𝟙 _ := rfl

lemma genericSliceAut_generic (σ : GenericAut k' K) :
    (genericSliceAut x hb σ).generic =
      (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ).generic := rfl

@[reassoc (attr := simp)]
lemma genericSliceAut_generic_snd (σ : GenericAut k' K) :
    (genericSliceAut x hb σ).generic ≫ pullback.snd _ _ = pullback.snd _ _ ≫ σ.τ :=
  pullback.lift_snd _ _ _

instance (σ : GenericAut k' K) : IsIso (genericSliceAut x hb σ).generic := by
  dsimp [genericSliceAut]
  infer_instance

lemma genericSliceAut_mul_generic (σ τ : GenericAut k' K) :
    (genericSliceAut x hb (σ * τ)).generic =
      (genericSliceAut x hb σ).generic ≫ (genericSliceAut x hb τ).generic := by
  apply pullback.hom_ext <;> simp [genericSliceAut]

lemma genericSliceAut_one_generic : (genericSliceAut x hb 1).generic = 𝟙 _ := by
  apply pullback.hom_ext <;> simp only [genericSliceAut, GenericAut.one_τ, Category.comp_id,
    Category.id_comp, limit.lift_π, PullbackCone.mk_π_app]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The action of generic automorphisms on the nearby cycles of the generic slice model is an
anti-homomorphism. -/
lemma autAction_genericSliceAut_mul (σ τ : GenericAut k' K)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (genericSliceBase x hb).left)
      Ab.{u + 1}) (condensedRingObj Λ (genericSliceBase x hb).left))) :
    (genericSliceAut x hb (σ * τ)).autAction Λ C =
      (genericSliceAut x hb τ).autAction Λ C ≫ (genericSliceAut x hb σ).autAction Λ C :=
  Hom.autAction_comp_of_eq Λ _ _ _ (Category.id_comp _)
    (genericSliceAut_mul_generic x hb σ τ).symm C

/-- The identity generic automorphism acts trivially on the nearby cycles of the generic slice
model. -/
lemma autAction_genericSliceAut_one
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (genericSliceBase x hb).left)
      Ab.{u + 1}) (condensedRingObj Λ (genericSliceBase x hb).left))) :
    (genericSliceAut x hb 1).autAction Λ C = 𝟙 _ :=
  Hom.autAction_of_eq_id Λ _ rfl (genericSliceAut_one_generic x hb) C

/-- The morphism of models `κ : M'' ⟶ M_b` from the generic slice model to the base change of `M`
along the slice, over a map of bases `c : X₂ ⟶ X` compatible with the identifications `ε`: all
its components are identities. -/
@[simps]
noncomputable def genericSliceToBaseChange {c : (genericSliceBase x hb).left ⟶ X}
    (hc : (genericSliceModel x hb).ε ≫ c =
      baseChangeGenericMap hM b hb (traitSlice x) (traitSlice_over x) ≫ M.ε) :
    (genericSliceModel x hb).Hom (baseChange hM b hb (traitSlice x) (traitSlice_over x)) c
      (𝟙 _) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := rfl
  comm_i := rfl
  comm_ε := by rw [Category.id_comp, hc]; rfl

/-- The pullback exchange of `κ : M'' ⟶ M_b` is invertible, its components being identities. -/
lemma isIso_pullbackExchange_genericSliceToBaseChange {c : (genericSliceBase x hb).left ⟶ X}
    (hc : (genericSliceModel x hb).ε ≫ c =
      baseChangeGenericMap hM b hb (traitSlice x) (traitSlice_over x) ≫ M.ε) :
    IsIso ((genericSliceToBaseChange x hM hb hc).pullbackExchange Λ) := by
  have : IsIso (genericSliceToBaseChange x hM hb hc).total := by
    rw [genericSliceToBaseChange_total]; infer_instance
  have : IsIso (genericSliceToBaseChange x hM hb hc).generic := by
    rw [genericSliceToBaseChange_generic]; infer_instance
  exact Hom.isIso_pullbackExchange_of_isIso Λ _

/-- **`κ` intertwines the actions of a generic automorphism**: the pullback exchange
`α_κ : L𝟙^* Ψ_{M_b} C ⟶ Ψ_{M''} (Lc^* C)` of `κ : M'' ⟶ M_b` carries the action of `σ` on
`Ψ_{M_b}` (`NearbyCyclesModel.baseChangeAut`) to its action on `Ψ_{M''}`
(`NearbyCyclesModel.genericSliceAut`). -/
lemma pullbackExchange_genericSliceToBaseChange_app_comp_autAction
    {c : (genericSliceBase x hb).left ⟶ X}
    (hc : (genericSliceModel x hb).ε ≫ c =
      baseChangeGenericMap hM b hb (traitSlice x) (traitSlice_over x) ≫ M.ε)
    (σ : GenericAut k' K)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((genericSliceToBaseChange x hM hb hc).pullbackExchange Λ).app C ≫
        (genericSliceAut x hb σ).autAction Λ (L((c)^*⟦Λ⟧).obj C) =
      L((𝟙 (baseChangeSpecial b (traitSlice x)).left)^*⟦Λ⟧).map
          ((baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ).autAction Λ C) ≫
        ((genericSliceToBaseChange x hM hb hc).pullbackExchange Λ).app C := by
  have h1 : (genericSliceAut x hb σ).total ≫ (genericSliceToBaseChange x hM hb hc).total =
      (genericSliceToBaseChange x hM hb hc).total ≫
        (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ).total := by
    simp
  have h2 : (genericSliceAut x hb σ).generic ≫ (genericSliceToBaseChange x hM hb hc).generic =
      (genericSliceToBaseChange x hM hb hc).generic ≫
        (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ).generic := by
    apply pullback.hom_ext <;> simp [genericSliceAut, baseChangeAut]
  have key := Hom.pullbackExchange_app_comp_autAction_of_comm Λ
    (genericSliceToBaseChange x hM hb hc)
    (genericSliceAut x hb σ) (baseChangeAut hM b hb (traitSlice x) (traitSlice_over x) σ) h1 h2 C
  exact key

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
