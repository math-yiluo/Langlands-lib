/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# Uniqueness of the dualizing maps of nearby cycles

The two properties of a family of dualizing maps (`NearbyCyclesModel.NearbyDualizingData`)
determine it (blueprint `prose-E-15`):

* on a proper `k'`-scheme `Z`, a map `A ⟶ ω_Z` is determined by its trace
  `RΓ(A) ⟶ RΓ(ω_Z) ⟶ ℚ̄_ℓ` (`NearbyCyclesModel.eq_of_map_comp_trace_eq`), the trace being the
  counit of `Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`;
* so for a proper model whose geometric generic fibre is all of `X ×_k Spec Ω`, where the proper
  exchange `χ_a` is invertible, the trace property determines `θ_M`
  (`NearbyCyclesModel.NearbyDualizingData.θ_eq_of_isProper`);
* every trait model over the base is an open sub-model of such a proper model
  (`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`), and open restriction
  determines `θ_N` from `θ_M`, the exchange `α_j` being invertible
  (`NearbyCyclesModel.NearbyDualizingData.θ_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **A map to the dualizing complex of a proper scheme is determined by its trace**: the
composite `RΓ(θ) ≫ tr_Z` is the image of `θ` under the adjunction `Ra_! ⊣ Ra^!`, read through
`Ra_! ≅ Ra_*`. -/
theorem eq_of_map_comp_trace_eq (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left]
    {A : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {θ₁ θ₂ : A ⟶ dualizingComplex ℓ Z}
    (h : (boundedConstructibleLowerStar ℓ (toPoint Z)).map θ₁ ≫ trace ℓ Z =
      (boundedConstructibleLowerStar ℓ (toPoint Z)).map θ₂ ≫ trace ℓ Z) :
    θ₁ = θ₂ := by
  have key (θ : A ⟶ dualizingComplex ℓ Z) :
      (boundedConstructibleLowerStar ℓ (toPoint Z)).map θ ≫ trace ℓ Z =
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).inv.app A ≫
          ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).homEquiv _ _).symm θ := by
    rw [trace, Adjunction.homEquiv_counit, ← Category.assoc, ← Category.assoc,
      NatTrans.naturality]
  rw [key, key, cancel_epi] at h
  exact ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).homEquiv _ _).symm.injective h

variable {k' : Type u} [Field k'] [Algebra k k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

/-- **Uniqueness of the dualizing maps of proper models**: for a proper model whose geometric
generic fibre is all of `X ×_k Spec Ω`, two families of dualizing maps agree, both being
determined by the trace property through the invertible proper exchange `χ_a`. -/
theorem NearbyDualizingData.θ_eq_of_isProper (D₁ D₂ : NearbyDualizingData k k' ℓ)
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom] [IsSeparated X'.hom] [IsProper (toPoint X).left]
    [IsProper (toPoint X').left] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOfBase k q g)
    [IsProper q] (hgen : IsPullback M.ε g X.hom (traitGenericPoint k' ≫ traitToBase k k')) :
    D₁.θ h = D₂.θ h := by
  have h₁ := D₁.pushforwardExchange_comp_map_θ_comp_trace h hgen
  have h₂ := D₂.pushforwardExchange_comp_map_θ_comp_trace h hgen
  have : IsIso ((h.pushforwardExchange ℓ).app (dualizingComplex ℓ X)) :=
    h.isIso_pushforwardExchange_app ℓ hgen _
  rw [← h₂, cancel_epi] at h₁
  exact eq_of_map_comp_trace_eq ℓ X' h₁

/-- **Uniqueness of the dualizing maps** (blueprint `prose-E-15`): two families of
dualizing maps of nearby cycles over the trait agree. The model is an open sub-model of a proper
model with full geometric generic fibre, on which they agree
(`NearbyCyclesModel.NearbyDualizingData.θ_eq_of_isProper`), and open restriction determines the
dualizing map of the sub-model, the exchange `α_j` and the identification `ρ` being invertible. -/
theorem NearbyDualizingData.θ_eq (D₁ D₂ : NearbyDualizingData k k' ℓ)
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom] [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfBase k q g) :
    D₁.θ h = D₂.θ h := by
  obtain ⟨Xc, _, _, _, _, Xc', _, _, _, _, Mc, qc, gc, hc, hcgen, _, j, _, j', _, φ, _, hφ, hq,
    hg⟩ := h.exists_isProper_openSubmodel
  have e₁ := D₁.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  have e₂ := D₂.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  rw [NearbyDualizingData.θ_eq_of_isProper ℓ D₁ D₂ hc hcgen, e₂] at e₁
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ (h.preservesBoundedConstructible ℓ)
      (hc.preservesBoundedConstructible ℓ)) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  rw [cancel_epi, cancel_epi] at e₁
  exact e₁.symm

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
