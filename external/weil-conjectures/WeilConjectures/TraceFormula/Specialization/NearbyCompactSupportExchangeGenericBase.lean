/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchangeProper
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseProper
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseCommonRefinement

/-!

# The compact-support exchange of a trait model over a generic base

Let `N` be a trait model of a separated `F`-scheme `Y` of finite type over the generic base
`(F, ι : η ⟶ Spec F)` (`NearbyCyclesModel.IsTraitModelOfGenericBase`), with special fibre `Y'`,
over the strictly henselian trait `S = Spec k'⟦t⟧`, and let `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`. For a
compactification `C` of `N`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification`: `N ⊆ P` open in a trait model
over the generic base with proper total space, over `ιX : Y ⟶ X`, `ιX' : Y' ⟶ X'`), the
compact-support exchange of the structure morphism `a : Y ⟶ Spec F` (blueprint
`prose-E-15` (3)), for the trait as a model of the point `Spec F` along `ε₀`
(`ProEtale.CondensedRing.traitModelOfPoint`), is
```
ν_C = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) : Ra'_! Ψ_N ⟶ Ψ_S Ra_!
```
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.compactSupportExchange`, an
instance of `ProEtale.CondensedRing.compactSupportExchangeOfCompactification`).

As over a base field (`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange`), it does not
depend on the compactification: it is unchanged along refinements
(`IsTraitModelOfGenericBase.Compactification.compactSupportExchange_eq_of_refinement`),
and any two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.exists_refinement`). Hence the
compact-support exchange `ν_a` of the trait model is well defined
(`NearbyCyclesModel.IsTraitModelOfGenericBase.compactSupportExchange`). For a proper model, it is
the inverse of the proper exchange `χ_a` under `Ra_! ≅ Ra_*`
(`Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfGenericBase

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {Y : Over (Spec (.of F))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left} {q : N.total ⟶ trait k'}
  {g : N.generic ⟶ Spec (.of (traitGenericField k'))} {h : N.IsTraitModelOfGenericBase Y ι q g}

namespace Compactification

variable (C : h.Compactification)

omit [Fact (ringChar F).Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_P` of the structure morphism of a
compactification, for `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`, is invertible on bounded constructible
complexes (`NearbyCyclesModel.IsTraitModelOfGenericBase.isIso_pushforwardExchange_app_ambient`).
-/
lemma isIsoOn_pushforwardExchange :
    IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) C.X.left)).ι
      ((C.isTraitModelOfGenericBase.toPoint (traitGenericPointToSpec k' ≫ ι)
        C.isPullback_ε.w.symm).pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) :=
  fun K ↦ C.isTraitModelOfGenericBase.isIso_pushforwardExchange_app_ambient ℓ _
    C.isPullback_ε.w.symm C.isPullback_ε _ K.property

instance : IsIso (C.hom.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
  C.hom.isIso_pullbackExchange_of_isOpenImmersion _ C.isPullback_hom_j

/-- **The compact-support exchange of a compactification** (blueprint `prose-E-15`
(3)): for the structure morphisms `a : Y ⟶ Spec F`, `a' : Y' ⟶ Spec k'` and a compactification
`N ⊆ P` over `ιX : Y ⟶ X`, `ιX' : Y' ⟶ X'`, the exchange `ν = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) :
Ra'_! Ψ_N ⟶ Ψ_S Ra_!` for the trait as a model of the point `Spec F` along
`ε₀ = (Spec Ω ⟶ η ⟶ Spec F)` (`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`).
-/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        boundedConstructibleLowerShriek ℓ (CondensedRing.toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (CondensedRing.toPoint Y) ⋙
        traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ :=
  compactSupportExchangeOfCompactification ℓ (h.preservesBoundedConstructible (ℓ := ℓ))
    (preservesBoundedConstructible_traitModelOfPoint _ ℓ) (comp_toPoint C.ιX)
    (comp_toPoint C.ιX') C.hom
    (C.isTraitModelOfGenericBase.toPoint _ C.isPullback_ε.w.symm)
    (C.isIsoOn_pushforwardExchange ℓ)

/-- **The compact-support exchange is unchanged along a refinement** (blueprint
`prose-E-15`, proof): an instance of
`ProEtale.CondensedRing.compactSupportExchangeOfCompactification_eq_of_refinement`. -/
theorem compactSupportExchange_eq_of_refinement {C₃ C₁ : h.Compactification}
    (r : C₃.Refinement C₁) : C₃.compactSupportExchange ℓ = C₁.compactSupportExchange ℓ :=
  compactSupportExchangeOfCompactification_eq_of_refinement ℓ
    (h.preservesBoundedConstructible (ℓ := ℓ))
    (preservesBoundedConstructible_traitModelOfPoint _ ℓ) C₃.hom C₁.hom
    (C₃.isTraitModelOfGenericBase.toPoint _ C₃.isPullback_ε.w.symm)
    (C₁.isTraitModelOfGenericBase.toPoint _ C₁.isPullback_ε.w.symm)
    (C₃.isIsoOn_pushforwardExchange ℓ) (C₁.isIsoOn_pushforwardExchange ℓ) r.π r.ιX_comp
    r.ιX'_comp r.hom_total_comp r.hom_generic_comp r.qc_eq.symm r.gc_eq.symm r.isPullback_ιX
    r.isPullback_ιX'

/-- **The compact-support exchange does not depend on the compactification** (blueprint
`prose-E-15`): two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.exists_refinement`), along which
the compact-support exchange is unchanged. -/
theorem compactSupportExchange_eq (C₁ C₂ : h.Compactification) :
    C₁.compactSupportExchange ℓ = C₂.compactSupportExchange ℓ := by
  obtain ⟨C₃, ⟨r₁⟩, ⟨r₂⟩⟩ := C₁.exists_refinement C₂
  rw [← compactSupportExchange_eq_of_refinement ℓ r₁, compactSupportExchange_eq_of_refinement ℓ r₂]

end Compactification

variable (h) in
/-- The compact-support exchange `ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of the structure morphism of a
trait model over a generic base (blueprint `prose-E-15` (3)), for the trait as a
model of the point `Spec F` along `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`: the exchange of any
compactification, which does not depend on it
(`NearbyCyclesModel.IsTraitModelOfGenericBase.compactSupportExchange_eq_compactSupportExchange`).
-/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        boundedConstructibleLowerShriek ℓ (CondensedRing.toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (CondensedRing.toPoint Y) ⋙
        traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ :=
  h.nonempty_compactification.some.compactSupportExchange ℓ

/-- The compact-support exchange of a trait model over a generic base is that of any of its
compactifications. -/
lemma compactSupportExchange_eq_compactSupportExchange (C : h.Compactification) :
    h.compactSupportExchange ℓ = C.compactSupportExchange ℓ :=
  Compactification.compactSupportExchange_eq ℓ _ _

/-- **The compact-support exchange of a proper model is the inverse of the proper exchange**: for
a trait model `N` over a generic base of a proper `Y` with proper special fibre and a
compactification `C`, the exchange `ν_C` followed by `Ra_! ≅ Ra_*` and the proper exchange `χ_a`
(for `ε₀ = (Spec Ω ⟶ η ⟶ Spec F)`) is `Ra'_! ≅ Ra'_*`. -/
theorem Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app
    [IsProper (CondensedRing.toPoint Y).left] [IsProper (CondensedRing.toPoint Y').left]
    (C : h.Compactification) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (C.compactSupportExchange ℓ).app K ≫
        (traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
            (CondensedRing.toPoint Y)).hom.app K) ≫
        (h.pushforwardExchange ℓ _ h.ε_hom.symm).app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
          (CondensedRing.toPoint Y')).hom.app
        ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj K) := by
  have : IsProper C.ιX.left := by
    have : IsProper (C.ιX.left ≫ C.X.hom) := by
      rw [Over.w, ← CondensedRing.toPoint_left]
      infer_instance
    exact IsProper.of_comp C.ιX.left C.X.hom
  have : IsProper C.ιX'.left := by
    have : IsProper (C.ιX'.left ≫ C.X'.hom) := by
      rw [Over.w, ← CondensedRing.toPoint_left]
      infer_instance
    exact IsProper.of_comp C.ιX'.left C.X'.hom
  -- rewriting first makes the instances of the goal those of the general statement
  have e₂ : h.pushforwardExchange ℓ _ h.ε_hom.symm = Hom.boundedConstructiblePushforwardExchange
      (f := CondensedRing.toPoint Y) (f' := CondensedRing.toPoint Y') ℓ
      (h.toPoint _ h.ε_hom.symm) (h.preservesBoundedConstructible (ℓ := ℓ))
      (preservesBoundedConstructible_traitModelOfPoint _ ℓ) := rfl
  rw [Compactification.compactSupportExchange, e₂]
  delta traitPointSpecialization
  cast_proofs compactSupportExchangeOfCompactification_app_comp_map_comp_pushforwardExchange_app ℓ
    (h.preservesBoundedConstructible (ℓ := ℓ))
    (preservesBoundedConstructible_traitModelOfPoint _ ℓ) C.hom
    (C.isTraitModelOfGenericBase.toPoint _ C.isPullback_ε.w.symm)
    (C.isIsoOn_pushforwardExchange ℓ) (h.toPoint _ h.ε_hom.symm) C.q_eq.symm C.g_eq.symm K

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfGenericBase
