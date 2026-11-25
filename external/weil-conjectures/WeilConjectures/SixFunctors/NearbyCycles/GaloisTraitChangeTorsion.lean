/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisTraitChange
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsCoinvariant
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.FieldTheory.GaloisRestriction

/-!

# Change of trait on nearby cycles from change of Galois layers, torsion coefficients

For torsion coefficients `Λ = C(-, T₀)`, the hypotheses of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap` on the two invariant
summands are supplied by SGA 4½, [Th. finitude], Lemme 3.4
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant` and
`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin`).
What remains is the hypothesis that the restriction `Aut(Ω₂/L₂) ⟶ Aut(Ω₁/L₁)` along `ω` meets every
element of every finite quotient `Gal(L'/L₁)`; it holds when `L₁` is relatively closed in `L₂`
(`AlgEquiv.exists_eq_of_forall_mem_range`).

## Main results

- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin`: if the
  change of Galois layers `α_{τ'}` is invertible, so is the change of trait `α_τ`, for complexes of
  étale origin with torsion coefficients.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀]
  {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] [IsGalois L₁ Ω₁] [IsGalois L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}
  {hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l}

-- the statement involves several large derived functor objects
/-- **Change of trait from change of Galois layers, torsion coefficients** (SGA 4½,
[Th. finitude], proof of 3.7, 3.8: "taking the invariants under a pro-`p` group"). Let
`τ : N₂ ⟶ N₁` be a morphism of models over `Spec l`, `ω : Ω₁ ⟶ Ω₂` a homomorphism of Galois
extensions `Ωᵢ/Lᵢ` over `l` whose finite subextensions have degrees invertible in `T₀`, and assume
that every element of every finite quotient `Gal(L'/L₁)` is the restriction of an element of
`Aut(Ω₂/L₂)` (the pro-`p` groups `Pᵢ = Gal(Ωᵢ/Lᵢ)` map onto each other). Let `C` be bounded below of
étale origin on `X₁`. If the exchange `α_{τ'}` of the change of Galois layers is invertible at
`C`, so is the exchange `α_τ` of `τ`. -/
theorem Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin [QuasiCompact N₁.j]
    [QuasiSeparated N₁.j] (τ : N₂.Hom N₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    (hp₁ : ∀ L' : FiniteGaloisIntermediateField L₁ Ω₁, IsUnit ((Module.finrank L₁ L' : ℕ) : T₀))
    (hp₂ : ∀ L' : FiniteGaloisIntermediateField L₂ Ω₂, IsUnit ((Module.finrank L₂ L' : ℕ) : T₀))
    (hlift : ∀ (L' : FiniteGaloisIntermediateField L₁ Ω₁) (a : L' ≃ₐ[L₁] L'),
      ∃ σ₂ : Ω₂ ≃ₐ[L₂] Ω₂, ∃ σ₁ : Ω₁ ≃ₐ[L₁] Ω₁, (∀ x : L', σ₁ x = a x) ∧
        ∀ x, ω (σ₁ x) = σ₂ (ω x))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X₁)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) X₁
      ((finiteCoefficientDerivedEquivalence X₁ T₀).functor.obj C))
    (hβ : IsIso (((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app
        (L((𝟙 X₁)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    IsIso ((τ.pullbackExchange (Profinite.continuousMapRingObj T₀)).app C) := by
  have h₁split := N₁.exists_retraction_pullbackExchange_galoisLayerHom_coinvariant T₀ h₁ Ω₁ hp₁ C
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀ N₁.ε hC)
    f' (fun k : {p : (Ω₁ ≃ₐ[L₁] Ω₁) × (Ω₂ ≃ₐ[L₂] Ω₂) // ∀ x, ω (p.1 x) = p.2 (ω x)} ↦ k.1.1)
    fun L' a ↦ by
      obtain ⟨σ₂, σ₁, h₁, h₂⟩ := hlift L' a
      exact ⟨⟨(σ₁, σ₂), h₂⟩, h₁⟩
  obtain ⟨r, hr, hinv⟩ := N₂.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin
    T₀ h₂ Ω₂ hp₂ (L((f)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C)
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀ N₂.ε
      (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀ f hC))
  have key := Hom.isIso_pullbackExchange_app_of_galoisLayerMap
    (Profinite.continuousMapRingObj T₀) τ hτ C
    (fun k : {p : (Ω₁ ≃ₐ[L₁] Ω₁) × (Ω₂ ≃ₐ[L₂] Ω₂) // ∀ x, ω (p.1 x) = p.2 (ω x)} ↦ k.1)
    (fun k ↦ k.2) (by exact_mod_proofs h₁split) _ rfl
    (by
      refine ⟨r, ?_, fun σ₂ ↦ ?_⟩
      · exact_mod_proofs hr
      · exact_mod_proofs (hinv σ₂).1)
    (hω := hω) (by exact_mod_proofs hβ)
  exact_mod_proofs key

-- the statement involves several large derived functor objects
/-- **Change of trait from change of Galois layers, from the map of inertia groups** (SGA 4½,
[Th. finitude], proof of 3.7, 3.8).
`Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin` with its lifting hypothesis
replaced by the setting of the change of trait: with towers
`Kᵢ ⊆ Lᵢ ⊆ Ωᵢ` (inertia `Iᵢ = Aut(Ωᵢ/Kᵢ)`, pro-`p` kernels `Pᵢ = Aut(Ωᵢ/Lᵢ)`), the induced map
`I₂ ⟶ I₁` is surjective (`hI`) and injective on the quotients `Iᵢ/Pᵢ` (`htame`, e.g. identified
tame inertia). Then the pro-`p` kernels map onto each other
(`AlgEquiv.exists_eq_of_exists_comp_eq_of_fixes`), and the change of trait `α_τ` is invertible as
soon as the change of Galois layers `α_{τ'}` is. -/
theorem Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_of_inertia
    [QuasiCompact N₁.j] [QuasiSeparated N₁.j] {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    [Algebra K₁ L₁] [Algebra K₁ Ω₁] [IsScalarTower K₁ L₁ Ω₁] [Algebra K₂ Ω₂]
    (τ : N₂.Hom N₁ f f') (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    (hp₁ : ∀ L' : FiniteGaloisIntermediateField L₁ Ω₁, IsUnit ((Module.finrank L₁ L' : ℕ) : T₀))
    (hp₂ : ∀ L' : FiniteGaloisIntermediateField L₂ Ω₂, IsUnit ((Module.finrank L₂ L' : ℕ) : T₀))
    (hI : ∀ σ₁ : Ω₁ ≃ₐ[K₁] Ω₁, ∃ σ₂ : Ω₂ ≃ₐ[K₂] Ω₂, ∀ x, ω (σ₁ x) = σ₂ (ω x))
    (htame : ∀ σ₂ : Ω₂ ≃ₐ[K₂] Ω₂,
      (∀ x : L₁, σ₂ (ω (algebraMap L₁ Ω₁ x)) = ω (algebraMap L₁ Ω₁ x)) →
        ∀ y : L₂, σ₂ (algebraMap L₂ Ω₂ y) = algebraMap L₂ Ω₂ y)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X₁)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) X₁
      ((finiteCoefficientDerivedEquivalence X₁ T₀).functor.obj C))
    (hβ : IsIso (((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app
        (L((𝟙 X₁)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C))) :
    IsIso ((τ.pullbackExchange (Profinite.continuousMapRingObj T₀)).app C) :=
  Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin T₀ τ hτ hp₁ hp₂
    (AlgEquiv.exists_eq_of_exists_comp_eq_of_fixes hI htame) C hC hβ

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
