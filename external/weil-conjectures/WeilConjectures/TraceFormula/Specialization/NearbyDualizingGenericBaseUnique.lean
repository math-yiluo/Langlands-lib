/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseProper
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseCompactification

/-!

# Uniqueness of the dualizing maps of nearby cycles over a generic base

The two properties of a family of dualizing maps over generic bases
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`) determine it, as over a base field
(`TraceFormula.Specialization.NearbyDualizingUnique`, blueprint `prose-E-15`):

* for a proper model whose geometric generic fibre is all of `X₁ ×_F Spec Ω`, the proper exchange
  `χ_a` along `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)` is invertible
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_pushforwardExchange_app`), so the trace
  property determines `θ_M`
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_of_isProper`);
* every trait model over a generic base is an open sub-model of such a proper model
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`), and open
  restriction determines `θ_N` from `θ_M`, the exchange `α_j` being invertible
  (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

namespace NearbyDualizingDataOfGenericBase

variable {k' : Type u} [Field k'] {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Uniqueness of the dualizing maps of proper models over a generic base**: for a proper
model whose geometric generic fibre is all of `X₁ ×_F Spec Ω`, two families of dualizing maps
agree, both being determined by the trace property through the invertible proper exchange `χ_a`
along `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`. -/
theorem θ_eq_of_isProper (D₁ D₂ : NearbyDualizingDataOfGenericBase k' ℓ)
    {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
    {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [IsProper (CondensedRing.toPoint X₁).left]
    [IsProper (CondensedRing.toPoint X').left] {M : NearbyCyclesModel X₁.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)) :
    D₁.θ h = D₂.θ h := by
  have h₁ := D₁.pushforwardExchange_comp_map_θ_comp_trace h hgen _ hgen.w.symm
  have h₂ := D₂.pushforwardExchange_comp_map_θ_comp_trace h hgen _ hgen.w.symm
  have : IsIso ((h.pushforwardExchange ℓ _ hgen.w.symm).app (dualizingComplex ℓ X₁)) :=
    h.isIso_pushforwardExchange_app ℓ _ hgen.w.symm hgen _
  rw [← h₂, cancel_epi] at h₁
  exact eq_of_map_comp_trace_eq ℓ X' h₁

/-- **Uniqueness of the dualizing maps over generic bases** (blueprint
`prose-E-15`): two families of dualizing maps of nearby cycles over generic bases
agree. The model is an open sub-model of a proper model with full geometric generic fibre
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_isProper_openSubmodel`), on which they agree
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_of_isProper`), and open restriction
determines the dualizing map of the sub-model, the exchange `α_j` and the identification `ρ`
being invertible. -/
theorem θ_eq (D₁ D₂ : NearbyDualizingDataOfGenericBase k' ℓ)
    {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
    {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    D₁.θ h = D₂.θ h := by
  obtain ⟨Xc, _, _, _, _, Xc', _, _, _, _, Mc, qc, gc, hc, hcgen, _, _, j, _, j', _, φ, _, hφ,
    hq, hg⟩ := h.exists_isProper_openSubmodel
  have e₁ := D₁.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  have e₂ := D₂.map_θ_comp_dualizingComplexUpperStarIso hc h j j' φ hφ hq hg
  rw [θ_eq_of_isProper D₁ D₂ hc hcgen, e₂] at e₁
  have : IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    φ.isIso_pullbackExchange_of_isOpenImmersion _ hφ
  have : IsIso (φ.boundedConstructiblePullbackExchange ℓ
      (h.preservesBoundedConstructible (ℓ := ℓ)) (hc.preservesBoundedConstructible (ℓ := ℓ))) :=
    φ.isIso_boundedConstructiblePullbackExchange ℓ _ _
  rw [cancel_epi, cancel_epi] at e₁
  exact e₁.symm

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
