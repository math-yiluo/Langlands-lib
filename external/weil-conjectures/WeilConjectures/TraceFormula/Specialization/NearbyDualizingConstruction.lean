/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchangeProper

/-!

# The dualizing maps of nearby cycles over the trait

For a trait model `N` of `Y` over the base, the dualizing map `θ_N : Ψ_N ω_Y ⟶ ω_{Y'}` (blueprint
`prose-E-15` (5)) is the exceptional adjoint of the compact-support exchange
`ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of the structure morphism, read through the specialization unit of
the trait (`NearbyCyclesModel.IsTraitModelOfBase.dualizingMap`, an instance of
`ProEtale.CondensedRing.dualizingExchange`). The compact-support exchange is defined through a
compactification and does not depend on it
(`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange`).

The two characteristic properties of `NearbyCyclesModel.NearbyDualizingData` hold:

* for a proper model, a compactification is proper over `Y`, and `ν_a = χ_a⁻¹` under `Ra_! ≅ Ra_*`
  (`Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app`),
  so `θ` is compatible with the traces;
* for an open sub-model `N ⊆ M`, a compactification of `M` is one of `N`, along which the
  compact-support exchange of `N` is the composite of the exchange `ν_j = (α_j⁻¹)♯` and that of
  `M`, so the composition law of the dualizing maps
  (`ProEtale.CondensedRing.dualizingExchange_eq_comp`) gives the open restriction property.

Hence `NearbyCyclesModel.nonempty_nearbyDualizingData` (blueprint `prose-E-15`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

namespace IsTraitModelOfBase

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The dualizing map of a trait model over the base** (blueprint `prose-E-15`
(5)): `θ_N = β_a(ℚ̄_ℓ) : Ψ_N ω_Y ⟶ ω_{Y'}`, the exceptional adjoint of the compact-support
exchange `ν_a` (`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange`), read through the
specialization unit `σ : ℚ̄_ℓ ≅ Ψ_S ℚ̄_ℓ` of the trait. -/
noncomputable def dualizingMap (h : N.IsTraitModelOfBase k q g) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
      (dualizingComplex ℓ Y) ⟶ dualizingComplex ℓ Y' :=
  dualizingExchange ℓ (traitSpecializationUnit k k' (ℓ := ℓ)) (h.compactSupportExchange ℓ)

-- matching the objects `ω_Y` and `Ra^! ℚ̄_ℓ` of the two sides unfolds the monoidal units
/-- **The dualizing map of a proper model is compatible with the traces**:
`tr_{Y'} ∘ Ra'_*(θ_N) ∘ χ_a(ω_Y) = σ⁻¹ ∘ Ψ_S(tr_Y)`, for `q` proper and geometric generic fibre
all of `Y ×_k Spec Ω` (then `χ_a` is invertible, and `ν_a = χ_a⁻¹` under `Ra_! ≅ Ra_*`). -/
theorem pushforwardExchange_app_comp_map_dualizingMap_comp_trace [IsProper (toPoint Y).left]
    [IsProper (toPoint Y').left] (h : N.IsTraitModelOfBase k q g) [IsProper q]
    (hgen : IsPullback N.ε g Y.hom (traitGenericPoint k' ≫ traitToBase k k')) :
    (h.pushforwardExchange ℓ).app (dualizingComplex ℓ Y) ≫
        (boundedConstructibleLowerStar ℓ (toPoint Y')).map (h.dualizingMap ℓ) ≫ trace ℓ Y' =
      (traitSpecialization k k' (ℓ := ℓ)).map (trace ℓ Y) ≫
        inv (traitSpecializationUnit k k' (ℓ := ℓ)) := by
  obtain ⟨C⟩ := h.nonempty_compactification
  have hL := C.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app ℓ
    (dualizingComplex ℓ Y)
  rw [← compactSupportExchange_eq_compactSupportExchange ℓ C] at hL
  have := h.isIso_pushforwardExchange_app ℓ hgen (dualizingComplex ℓ Y)
  simp only [dualizingMap, dualizingExchange, exceptionalExchange, trace, Functor.map_comp,
    Category.assoc, NatTrans.naturality_assoc]
  rw [Adjunction.counit_naturality, reassoc_of% (mateEquiv_counit
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y))
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y')) (h.compactSupportExchange ℓ) (𝟙_ _))]
  have key : ∀ {P Q R U V : Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧} (χ : P ⟶ Q)
      [IsIso χ] (e : R ≅ Q) (ν : R ⟶ U) (f : U ≅ P) (_ : ν ≫ f.hom ≫ χ = e.hom) (x : U ⟶ V),
      χ ≫ e.inv ≫ ν ≫ x = f.inv ≫ x := by
    intro P Q R U V χ _ e ν f hL x
    have h₁ : e.inv ≫ ν ≫ f.hom ≫ χ = 𝟙 _ := by rw [hL, Iso.inv_hom_id]
    calc χ ≫ e.inv ≫ ν ≫ x = χ ≫ (e.inv ≫ ν ≫ f.hom ≫ χ) ≫ inv χ ≫ f.inv ≫ x := by simp
      _ = f.inv ≫ x := by rw [h₁]; simp
  exact key ((h.pushforwardExchange ℓ).app (dualizingComplex ℓ Y))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y')).app
      ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
        (dualizingComplex ℓ Y)))
    ((h.compactSupportExchange ℓ).app (dualizingComplex ℓ Y))
    ((traitSpecialization k k' (ℓ := ℓ)).mapIso
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).app
        (dualizingComplex ℓ Y))) hL
    ((traitSpecialization k k' (ℓ := ℓ)).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (toPoint Y)).counit.app (𝟙_ _)) ≫
      inv (traitSpecializationUnit k k' (ℓ := ℓ)))

end IsTraitModelOfBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
