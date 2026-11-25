/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchangeGenericBase

/-!

# The dualizing maps of nearby cycles over a generic base

For a trait model `N` of `Y` over the generic base `(F, ι : η ⟶ Spec F)`, the dualizing map
`θ_N : Ψ_N ω_Y ⟶ ω_{Y'}` (blueprint `prose-E-15` (5)) is the exceptional adjoint of
the compact-support exchange `ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of the structure morphism, for the trait
as a model of the point `Spec F` along `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`, read through its
specialization unit (`NearbyCyclesModel.IsTraitModelOfGenericBase.dualizingMap`, an instance of
`ProEtale.CondensedRing.dualizingExchange`).

For a proper model with geometric generic fibre all of `Y ×_F Spec Ω`, a compactification is
proper over `Y`, and `ν_a = χ_a⁻¹` under `Ra_! ≅ Ra_*`, so `θ` is compatible with the traces
(`IsTraitModelOfGenericBase.pushforwardExchange_app_comp_map_dualizingMap_comp_trace`),
as over a base field
(`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange_app_comp_map_dualizingMap_comp_trace`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

/-- If `ν ≫ f.hom ≫ χ = e.hom` with `χ` invertible, then `χ ≫ e.inv ≫ ν ≫ x = f.inv ≫ x`. -/
lemma comp_inv_comp_comp_eq_of_comp_eq {C : Type*} [Category C] {P Q R U V : C} (χ : P ⟶ Q)
    [IsIso χ] (e : R ≅ Q) (ν : R ⟶ U) (f : U ≅ P) (hL : ν ≫ f.hom ≫ χ = e.hom) (x : U ⟶ V) :
    χ ≫ e.inv ≫ ν ≫ x = f.inv ≫ x := by
  have h₁ : e.inv ≫ ν ≫ f.hom ≫ χ = 𝟙 _ := by rw [hL, Iso.inv_hom_id]
  calc χ ≫ e.inv ≫ ν ≫ x = χ ≫ (e.inv ≫ ν ≫ f.hom ≫ χ) ≫ inv χ ≫ f.inv ≫ x := by simp
    _ = f.inv ≫ x := by simp [h₁]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}

namespace IsTraitModelOfGenericBase

variable {Y : Over (Spec (.of F))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The dualizing map of a trait model over a generic base** (blueprint
`prose-E-15` (5)): `θ_N = β_a(ℚ̄_ℓ) : Ψ_N ω_Y ⟶ ω_{Y'}`, the exceptional adjoint of
the compact-support exchange `ν_a`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.compactSupportExchange`), read through the
specialization unit `σ : ℚ̄_ℓ ≅ Ψ_S ℚ̄_ℓ` of the trait as a model of the point `Spec F` along
`ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`. -/
noncomputable def dualizingMap (h : N.IsTraitModelOfGenericBase Y ι q g) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
      (dualizingComplex ℓ Y) ⟶ dualizingComplex ℓ Y' :=
  dualizingExchange ℓ (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ)
    (h.compactSupportExchange ℓ)

-- matching the objects `ω_Y` and `Ra^! ℚ̄_ℓ` of the two sides unfolds the monoidal units
/-- **The dualizing map of a proper model over a generic base is compatible with the traces**:
`tr_{Y'} ∘ Ra'_*(θ_N) ∘ χ_a(ω_Y) = σ⁻¹ ∘ Ψ_S(tr_Y)` for `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`, `q`
proper and geometric generic fibre all of `Y ×_F Spec Ω` (then `χ_a` is invertible, and
`ν_a = χ_a⁻¹` under `Ra_! ≅ Ra_*`). -/
theorem pushforwardExchange_app_comp_map_dualizingMap_comp_trace
    [IsProper (CondensedRing.toPoint Y).left] [IsProper (CondensedRing.toPoint Y').left]
    (h : N.IsTraitModelOfGenericBase Y ι q g) [IsProper q]
    (hgen : IsPullback N.ε g Y.hom (traitGenericPointToSpec k' ≫ ι)) :
    (h.pushforwardExchange ℓ _ h.ε_hom.symm).app (dualizingComplex ℓ Y) ≫
        (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint Y')).map (h.dualizingMap ℓ) ≫
          trace ℓ Y' =
      (traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ).map (trace ℓ Y) ≫
        inv (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ) := by
  obtain ⟨C⟩ := h.nonempty_compactification
  have hL := C.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app ℓ
    (dualizingComplex ℓ Y)
  rw [← compactSupportExchange_eq_compactSupportExchange ℓ C] at hL
  have := h.isIso_pushforwardExchange_app ℓ _ h.ε_hom.symm hgen (dualizingComplex ℓ Y)
  simp only [dualizingMap, dualizingExchange, exceptionalExchange, trace, Functor.map_comp,
    Category.assoc, NatTrans.naturality_assoc]
  rw [Adjunction.counit_naturality, reassoc_of% (mateEquiv_counit
    (boundedConstructibleUpperShriekAdjunction ℓ (CondensedRing.toPoint Y))
    (boundedConstructibleUpperShriekAdjunction ℓ (CondensedRing.toPoint Y'))
    (h.compactSupportExchange ℓ) (𝟙_ _))]
  exact comp_inv_comp_comp_eq_of_comp_eq
    ((h.pushforwardExchange ℓ _ h.ε_hom.symm).app (dualizingComplex ℓ Y))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (CondensedRing.toPoint Y')).app
      ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj
        (dualizingComplex ℓ Y)))
    ((h.compactSupportExchange ℓ).app (dualizingComplex ℓ Y))
    ((traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ).mapIso
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (CondensedRing.toPoint Y)).app
        (dualizingComplex ℓ Y))) hL
    ((traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ).map
        ((boundedConstructibleUpperShriekAdjunction ℓ (CondensedRing.toPoint Y)).counit.app
          (𝟙_ _)) ≫
      inv (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ))

end IsTraitModelOfGenericBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
