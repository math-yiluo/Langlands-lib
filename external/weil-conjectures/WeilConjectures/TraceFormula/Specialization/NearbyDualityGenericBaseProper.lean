/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityProper
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBase
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# Nearby duality over a generic base: global sections of proper models

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)` along
`ι : η ⟶ Spec F` (`NearbyCyclesModel.IsTraitModelOfGenericBase`), with proper total space, proper
`X₁` and `X'`, and whose geometric generic fibre is all of `X₁ ×_F Spec Ω`. This file proves the
proper part of nearby duality for such models, as for trait models over the base
(`TraceFormula.Specialization.NearbyDualityCompactification`):

* the proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure morphism, for the trait as a
  model of the point `Spec F` along `ε₀` (`NearbyCyclesModel.IsTraitModelOfGenericBase.toPoint`),
  is an isomorphism (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_pushforwardExchange_app`),
  by the proper exchange of blueprint `prose-E-03` (2)
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`), the square of geometric
  generic fibres being cartesian;
* the global sections `RΓ(X', δ_{M,K})` of the duality map with dualizing map `θ_M` of a family
  of dualizing maps over generic bases are isomorphisms
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_lowerStar_nearbyDualityMap_of_isProper`),
  by the abstract identity `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans`
  (blueprint `lemma-nearby-duality-proper-direct-image` (1), (3)) with the trace property of `θ_M`
  for `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`, global Verdier duality on both fibres and the duality of the
  trait as a model of a point (`NearbyCyclesModel.isIso_nearbyDualityMap_traitModelOfPoint`);
* hence the duality map `δ_{M,K}` is an isomorphism as soon as it is so away from finitely many
  closed points of the special fibre
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_nearbyDualityMap_of_isProper_of_finset`,
  by `ProEtale.CondensedRing.isIso_of_isIso_upperStar_finsetComplOpens_of_isIso_lowerStar`).

The duality map is stated as `Verdier.nearbyDualityMap (boundedConstructibleTensorMap _) (D.θ h) K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] {k' : Type u} [Field k']
  {X₁ : Over (Spec (.of F))} {X' : Over (Spec (.of k'))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

/-- **Proper exchange for a proper trait model over a generic base**, on the ambient derived
categories: if the total space of `M` is proper over the trait, `X₁` is proper over `F` and the
square of geometric generic fibres `𝒳_Ω ⟶ X₁`, `Spec Ω ⟶ Spec F` (along `ε₀`) is cartesian, the
proper exchange `χ_a : Ψ_S Ra_* K ⟶ Ra'_* Ψ_M K` of the morphism of models
`NearbyCyclesModel.IsTraitModelOfGenericBase.toPoint` is invertible at every bounded
constructible `K` (blueprint `prose-E-03` (2),
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`). -/
theorem IsTraitModelOfGenericBase.isIso_pushforwardExchange_app_ambient [Fact (ringChar F ≠ ℓ)]
    [Fact (ringChar k' ≠ ℓ)]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    [IsProper (CondensedRing.toPoint X₁).left]
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = M.ε ≫ X₁.hom)
    (hgen : IsPullback M.ε g X₁.hom ε₀)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj 𝐐 X₁.left)))
    (hA : boundedConstructible _ A) :
    IsIso (((h.toPoint ε₀ hε₀).pushforwardExchange 𝐐).app A) := by
  have : IsProper (h.toPoint ε₀ hε₀).total := ‹IsProper q›
  have hi : IsPullback M.i (CondensedRing.toPoint X').left q (traitClosedPoint k') := by
    rw [toPoint_left]
    exact h.isTraitModelOver.isPullback_i
  have hε : IsPullback M.ε g (CondensedRing.toPoint X₁).left ε₀ := by
    rw [toPoint_left]
    exact hgen
  have : IsNoetherian (point F).left := inferInstanceAs (IsNoetherian (Spec (.of F)))
  exact (h.toPoint ε₀ hε₀).isIso_pushforwardExchange_app_of_isProper (point F).hom
    h.isTraitModelOver.isTraitModel.exists_over (isTraitModel_traitModelOfPoint ε₀).exists_over hi
    hε hA

/-- **Proper exchange for a proper trait model over a generic base**: if `X₁` is proper over
`F`, the total space of `M` is proper over the trait and the square of geometric generic fibres
along `ε₀` is cartesian, the proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure
morphism (`NearbyCyclesModel.IsTraitModelOfGenericBase.pushforwardExchange`) is an isomorphism on
bounded constructible complexes. For the full generic fibre
`IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι)`, take
`ε₀ = traitGenericPointToSpec k' ≫ ι`. -/
theorem IsTraitModelOfGenericBase.isIso_pushforwardExchange_app [IsSepClosed k']
    [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar k').Prime]
    [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    (h : M.IsTraitModelOfGenericBase X₁ ι q g) [IsProper q]
    [IsProper (CondensedRing.toPoint X₁).left]
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = M.ε ≫ X₁.hom)
    (hgen : IsPullback M.ε g X₁.hom ε₀) (K : Dᵇc(X₁.left)⟦𝐐⟧) :
    IsIso ((h.pushforwardExchange ℓ ε₀ hε₀).app K) :=
  Hom.isIso_boundedConstructiblePushforwardExchange_app (f := CondensedRing.toPoint X₁)
    (f' := CondensedRing.toPoint X') ℓ (h.toPoint ε₀ hε₀) _ _ K
    (h.isIso_pushforwardExchange_app_ambient ℓ ε₀ hε₀ hgen K.obj K.property)

variable [IsSepClosed k'] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType X₁.hom]
  [QuasiCompact X₁.hom] [IsSeparated X₁.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]

/-- **Global sections of the duality map of a proper model over a generic base** (blueprint
`lemma-nearby-duality-proper-direct-image` (1), (3)): if `X₁`, `X'` and the total space of the trait
model `M` over the generic base are proper and the geometric generic fibre of `M` is all of
`X₁ ×_F Spec Ω`, then `RΓ(X', δ_{M,K})` is an isomorphism, for the duality map `δ_{M,K}` with
dualizing map `θ_M` of a family `D` of dualizing maps over generic bases. This is
`CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans` for the proper exchange
`χ_a` along `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_pushforwardExchange_app`), its compatibility
with the lax tensor maps (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`),
the trace property of `D`, global Verdier duality on both fibres
(`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`) and the duality of the trait as
a model of the point `Spec F` (`NearbyCyclesModel.isIso_nearbyDualityMap_traitModelOfPoint`). -/
theorem IsTraitModelOfGenericBase.isIso_lowerStar_nearbyDualityMap_of_isProper
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (K : Dᵇc(X₁.left)⟦𝐐⟧) :
    IsIso ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
      (Verdier.nearbyDualityMap
        (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ))) (D.θ h) K)) := by
  have hθ := (D.pushforwardExchange_comp_map_θ_comp_trace h hgen _ hgen.w.symm).symm
  have hχ (A : Dᵇc(X₁.left)⟦𝐐⟧) :=
    h.isIso_pushforwardExchange_app ℓ _ hgen.w.symm hgen A
  have t₁ : h.pushforwardExchange ℓ _ hgen.w.symm =
      (h.toPoint _ hgen.w.symm).boundedConstructiblePushforwardExchange ℓ
        (h.preservesBoundedConstructible (ℓ := ℓ))
        (preservesBoundedConstructible_traitModelOfPoint _ ℓ) := rfl
  rw [t₁] at hθ hχ
  have := isIso_nearbyDualityMap_traitModelOfPoint ℓ (traitGenericPointToSpec k' ≫ ι)
    ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁)).obj K)
  exact Verdier.isIso_map_nearbyDualityMap_of_proper_natTrans
    (fun A B ↦ Hom.boundedConstructiblePushforwardExchange_tensor
      (f := CondensedRing.toPoint X₁) (f' := CondensedRing.toPoint X') (h.toPoint _ hgen.w.symm)
      (h.preservesBoundedConstructible (ℓ := ℓ))
      (preservesBoundedConstructible_traitModelOfPoint _ ℓ) A B) hθ
    (fun A _ _ y ↦
      letI := boundedConstructibleLowerStarLaxMonoidal ℓ (CondensedRing.toPoint X')
      Functor.LaxMonoidal.μ_natural_right _ A y)
    (fun x y ↦ boundedConstructibleTensorMap_natural _ x y) K (hχ K) (hχ _)
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X₁ K)
    (isIso_nearbyDualityMap_lowerStar_trace ℓ X' _) this

/-- **Nearby duality for a proper model over a generic base with finite support** (blueprint
`proposition-nearby-cycles-commute-verdier-duality`, "Dimension induction", last step): if `X₁`,
`X'` and the total space of the trait model `M` over the generic base are proper and its geometric
generic fibre is all of `X₁ ×_F Spec Ω`, the duality map `δ_{M,K}` is an isomorphism as soon as it
is an isomorphism away from finitely many closed points of the special fibre: its global sections
are isomorphisms
(`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_lowerStar_nearbyDualityMap_of_isProper`), so
its cone vanishes
(`ProEtale.CondensedRing.isIso_of_isIso_upperStar_finsetComplOpens_of_isIso_lowerStar`). -/
theorem IsTraitModelOfGenericBase.isIso_nearbyDualityMap_of_isProper_of_finset
    (D : NearbyDualizingDataOfGenericBase k' ℓ) (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint X').left]
    [IsProper q] (hgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (K : Dᵇc(X₁.left)⟦𝐐⟧)
    (hfin : ∃ (S : Finset X'.left) (hS : ∀ x ∈ S, IsClosed {x}),
      IsIso ((boundedConstructibleUpperStar 𝐐 ℓ (opensOverι (finsetComplOpens S hS))).map
        (Verdier.nearbyDualityMap
          (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ))) (D.θ h) K))) :
    IsIso (Verdier.nearbyDualityMap
      (boundedConstructibleTensorMap (h.preservesBoundedConstructible (ℓ := ℓ))) (D.θ h) K) := by
  obtain ⟨S, hS, hU⟩ := hfin
  exact isIso_of_isIso_upperStar_finsetComplOpens_of_isIso_lowerStar ℓ S hS _ hU
    (h.isIso_lowerStar_nearbyDualityMap_of_isProper ℓ D hgen K)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
