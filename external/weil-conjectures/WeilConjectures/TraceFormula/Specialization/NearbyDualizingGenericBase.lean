/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingUnique
public import WeilConjectures.TraceFormula.Specialization.TraitModelGenericPoint
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseFiniteness

/-!

# The dualizing maps of nearby cycles over a generic base

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `k'` separably closed, and `M` a trait model
of an `F`-scheme `X₁` over the generic base `(F, X₁)` along `ι : η ⟶ Spec F`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`). For every `ε₀ : Spec Ω ⟶ Spec F` with
`g ≫ ε₀ = ε ≫ (X₁ ⟶ Spec F)`, the model maps to the trait as a model of the point `Spec F` along
`ε₀` (`ProEtale.CondensedRing.traitModelOfPoint`) over the structure morphisms
(`NearbyCyclesModel.IsTraitModelOfGenericBase.toPoint`), with proper exchange
`χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` (`NearbyCyclesModel.IsTraitModelOfGenericBase.pushforwardExchange`).

A *family of dualizing maps over a generic base*
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`) is a map `θ_M : Ψ_M ω_{X₁} ⟶ ω_{X'}` for
every trait model over a generic base, with the trace property for proper models with full
generic fibre and the open restriction property, as for the dualizing maps of trait models over
a base field (`NearbyCyclesModel.NearbyDualizingData`). Its existence is the node lemma
`NearbyCyclesModel.nonempty_nearbyDualizingDataOfGenericBase`, proved downstream in
`TraceFormula.Specialization.NearbyDualizingGenericBaseExistence` from the compact-support
exchanges of compactifications. It restricts to a family of dualizing maps
over every base field `k` of `k'`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.toNearbyDualizingData`), so that it agrees
with every such family (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_θ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Hom

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The morphism of models `a : M ⟶ S` from a trait model of `X₁` over the generic base to the
trait as a model of the point `Spec F` along `ε₀ : Spec Ω ⟶ Spec F`, over the structure morphisms
`X₁ ⟶ Spec F` and `X' ⟶ Spec k'`, for `ε₀` compatible with `ε`. -/
noncomputable def IsTraitModelOfGenericBase.toPoint (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = M.ε ≫ X₁.hom) :
    M.Hom (traitModelOfPoint ε₀) (CondensedRing.toPoint X₁).left
      (CondensedRing.toPoint X').left where
  total := q
  generic := g
  comm_j := h.isTraitModelOver.isPullback_j.w.symm
  comm_i := by
    rw [toPoint_left]
    exact h.isTraitModelOver.isPullback_i.w.symm
  comm_ε := by
    rw [toPoint_left]
    exact hε₀

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` of the structure morphism of a trait model
of `X₁` over the generic base, for the trait as a model of the point `Spec F` along `ε₀`. -/
noncomputable def IsTraitModelOfGenericBase.pushforwardExchange
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = M.ε ≫ X₁.hom) :
    boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁) ⋙
        traitPointSpecialization ε₀ ℓ ⟶
      boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X') :=
  (h.toPoint ε₀ hε₀).boundedConstructiblePushforwardExchange ℓ
    (h.preservesBoundedConstructible (ℓ := ℓ))
    (preservesBoundedConstructible_traitModelOfPoint ε₀ ℓ)

end Hom

variable (k' : Type u) [Field k'] (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- A *family of dualizing maps* of nearby cycles over the trait `S = Spec k'⟦t⟧` over generic
bases: a map `θ_M : Ψ_M ω_{X₁} ⟶ ω_{X'}` for every trait model `M` of an `F`-scheme `X₁` over the
generic base `(F, X₁)`, with the two characteristic properties of the dualizing maps
`θ_M = β_a(ℚ̄_ℓ)` of blueprint `prose-E-15` (see
`NearbyCyclesModel.nonempty_nearbyDualizingDataOfGenericBase`). This is the analogue over generic
bases of `NearbyCyclesModel.NearbyDualizingData`. -/
structure NearbyDualizingDataOfGenericBase where
  /-- the dualizing map `θ_M : Ψ_M ω_{X₁} ⟶ ω_{X'}`. -/
  θ {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
    {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom] [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left}
    {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
      (dualizingComplex ℓ X₁) ⟶ dualizingComplex ℓ X'
  /-- proper models whose generic fibre is all of `X₁ ×_F η`: for every `ε₀` compatible with `ε`,
  `tr_{X'} ∘ Ra'_*(θ_M) ∘ χ_a(ω_{X₁}) = σ⁻¹ ∘ Ψ_S(tr_{X₁})`. -/
  pushforwardExchange_comp_map_θ_comp_trace {F : Type u} [Field F] [Fact (ringChar F).Prime]
    [Fact (ringChar F ≠ ℓ)] {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom]
    [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [IsProper (CondensedRing.toPoint X₁).left]
    [IsProper (CondensedRing.toPoint X').left]
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = M.ε ≫ X₁.hom) :
    (h.pushforwardExchange ℓ ε₀ hε₀).app (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
          (θ h) ≫ trace ℓ X' =
      (traitPointSpecialization ε₀ ℓ).map (trace ℓ X₁) ≫
        inv (traitPointSpecializationUnit ε₀ ℓ)
  /-- open restriction: `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_{X₁})`. -/
  map_θ_comp_dualizingComplexUpperStarIso {F : Type u} [Field F] [Fact (ringChar F).Prime]
    [Fact (ringChar F ≠ ℓ)] {X₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom]
    [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {Y₁ : Over (Spec (.of F))} [LocallyOfFiniteType Y₁.hom]
    [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom] {Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    {N : NearbyCyclesModel Y₁.left Y'.left} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    (j : Y₁ ⟶ X₁) [IsOpenImmersion j.left] (j' : Y' ⟶ X') [IsOpenImmersion j'.left]
    (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : qN = φ.total ≫ q)
    (hg : gN = φ.generic ≫ g) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map (θ hM) ≫
        (dualizingComplexUpperStarIso ℓ j').hom =
      (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible (ℓ := ℓ))
          (hM.preservesBoundedConstructible (ℓ := ℓ))).app (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).map
          (dualizingComplexUpperStarIso ℓ j).hom ≫ θ hN

namespace NearbyDualizingDataOfGenericBase

variable {k' ℓ} (D : NearbyDualizingDataOfGenericBase k' ℓ)
  (k : Type u) [Field k] [Algebra k k'] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- A family of dualizing maps over generic bases restricts to a family of dualizing maps over
the base field `k`, along `IsTraitModelOfBase.isTraitModelOfGenericBase`: for `ι : η ⟶ S ⟶ Spec k`
the trait model of the base point is the trait as a model of the point along its `ε`. -/
noncomputable def toNearbyDualizingData : NearbyDualizingData k k' ℓ where
  θ h := D.θ h.isTraitModelOfGenericBase
  pushforwardExchange_comp_map_θ_comp_trace h _ hgen := by
    rw [← traitGenericPointToSpec_traitGenericSpec_assoc] at hgen
    convert D.pushforwardExchange_comp_map_θ_comp_trace h.isTraitModelOfGenericBase hgen
      (traitModel k k').ε (h.toTrait.comm_ε.trans (congrArg _ (toPoint_left _))) using 2
    · rw [traitPointSpecialization_traitModel_ε]
    · congr 1
    · rw [traitPointSpecialization_traitModel_ε]
    · rw [traitPointSpecialization_traitModel_ε]
    · congr 1
    · congr 1
  map_θ_comp_dualizingComplexUpperStarIso hM hN j _ j' _ φ _ hφ hq hg :=
    D.map_θ_comp_dualizingComplexUpperStarIso hM.isTraitModelOfGenericBase
      hN.isTraitModelOfGenericBase j j' φ hφ hq hg

/-- A family of dualizing maps over generic bases agrees with every family of dualizing maps over
the base field `k` (`NearbyCyclesModel.NearbyDualizingData.θ_eq`). -/
theorem θ_eq_θ (D₀ : NearbyDualizingData k k' ℓ) {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (h : M.IsTraitModelOfBase k q g) :
    D₀.θ h = D.θ h.isTraitModelOfGenericBase :=
  NearbyDualizingData.θ_eq ℓ D₀ (D.toNearbyDualizingData k) h

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
