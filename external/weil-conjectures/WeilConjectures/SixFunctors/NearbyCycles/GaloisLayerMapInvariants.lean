/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.GaloisRestriction
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsProjector
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisTraitChange
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait from the change of Galois layers, for torsion coefficients of étale origin

Let `τ : N₂ ⟶ N₁` be a morphism of models over `Spec l : Spec L₂ ⟶ Spec L₁`, `ω : Ω₁ ⟶ Ω₂` a
homomorphism of Galois extensions over `l` such that `L₁` is relatively closed in `L₂` inside
`Ω₂`, and `Λ = C(-, T₀)` for a finite discrete ring `T₀` in which the degrees of the finite Galois
subextensions of `Ωᵢ/Lᵢ` are invertible. For `C` such that `Lεᵢ^*` of `C` (resp. of `Lf^* C`) is
bounded below of étale origin, if the change of Galois layers `α_{τ'}` is invertible, so is the
change of trait `α_τ` (SGA 4½, [Th. finitude], proof of 3.7, 3.8)
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic`).

This combines `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap` with the
projectors onto the Galois invariants
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`)
for the family `σ ↦ (σ|_{Ω₁}, σ)` of `Aut(Ω₂/L₂)`, whose restrictions to every finite Galois
subextension of `Ω₁/L₁` are surjective (`AlgEquiv.exists_restrictNormalHomAlong_eq`).

Compared with
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin`
(`WeilConjectures.SixFunctors.NearbyCycles.GaloisTraitChangeTorsion`), the étale-origin hypotheses
are only asked on the generic fibres, which is the form available in the slice step.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}
  {hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l}

/-- **Change of trait from the change of Galois layers** (SGA 4½, [Th. finitude], proof of 3.7,
3.8), for coefficients `Λ = C(-, T₀)` with `T₀` finite discrete in which the degrees of the finite
Galois subextensions of `Ωᵢ/Lᵢ` are invertible. Let `τ : N₂ ⟶ N₁` be a morphism of models over
`Spec l`, `ω : Ω₁ ⟶ Ω₂` a homomorphism of Galois extensions over `l` with `L₁` relatively closed in
`L₂` inside `Ω₂`, and `C` such that `Lε₁^* C` and `Lε₂^* Lf^* C` are bounded below of étale origin.
If the change of Galois layers `α_{τ'}` is invertible, so is the change of trait `α_τ`. -/
theorem Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] [IsGalois L₁ Ω₁] [IsGalois L₂ Ω₂] (τ : N₂.Hom N₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    [QuasiCompact N₁.j] [QuasiSeparated N₁.j] [QuasiCompact N₂.j] [QuasiSeparated N₂.j]
    (hp₁ : ∀ L' : FiniteGaloisIntermediateField L₁ Ω₁, IsUnit ((Module.finrank L₁ L' : ℕ) : T₀))
    (hp₂ : ∀ L' : FiniteGaloisIntermediateField L₂ Ω₂, IsUnit ((Module.finrank L₂ L' : ℕ) : T₀))
    (hclosed : ∀ x : Ω₁, ω x ∈ Set.range (algebraMap L₂ Ω₂) →
      x ∈ Set.range (algebraMap L₁ Ω₁))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X₁)))
    (hC₁ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N₁.generic
      ((finiteCoefficientDerivedEquivalence N₁.generic T₀).functor.obj
        (L((N₁.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)))
    (hC₂ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) N₂.generic
      ((finiteCoefficientDerivedEquivalence N₂.generic T₀).functor.obj
        (L((N₂.ε)^*⟦Profinite.continuousMapRingObj T₀⟧).obj
          (L((f)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))))
    [hiso : IsIso (((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app
        (L((𝟙 X₁)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))] :
    IsIso ((τ.pullbackExchange (Profinite.continuousMapRingObj T₀)).app C) := by
  obtain ⟨r₁, hr₁, -, hproj₁⟩ :=
    exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector.{u, u} N₁ h₁ Ω₁
      T₀ hp₁ C hC₁
  obtain ⟨r₂, hr₂, hinv₂, -⟩ :=
    exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector.{u, u} N₂ h₂ Ω₂
      T₀ hp₂ _ hC₂
  with_reducible
    have key := τ.isIso_pullbackExchange_app_of_galoisLayerMap (Profinite.continuousMapRingObj T₀)
      (hω := hω) hτ C (fun k : Ω₂ ≃ₐ[L₂] Ω₂ ↦ (AlgEquiv.restrictNormalHomAlong hω k, k))
      (fun k x ↦ AlgEquiv.restrictNormalHomAlong_commutes hω k x)
      ⟨r₁, hr₁, fun q W φ hφ ↦ hproj₁ f' q φ _
        (fun L' a ↦ AlgEquiv.exists_restrictNormalHomAlong_eq hω hclosed L' a) hφ⟩
      (L((f)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) rfl
    -- the instances `Precoherent Profinite` in the statement of `key` and here are elaborated
    -- differently; unifying them through the derived categories is too slow
    have key₂ := @key ⟨r₂, hr₂, fun σ₂ ↦ (hinv₂ σ₂).1⟩ ?inst
  · exact_mod_proofs key₂
  · exact_mod_proofs hiso

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
