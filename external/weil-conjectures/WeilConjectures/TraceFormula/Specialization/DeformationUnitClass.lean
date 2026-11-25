/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ProperUnitClass
public import WeilConjectures.TraceFormula.Specialization.SupportCompactSupportExchange

/-!

# The unit class of a proper deformation over the trait

For a `k`-scheme `X` and an ideal sheaf `I`, the structure map `𝒳 ⟶ S` of the deformation to the
normal cone over the trait `S = Spec k'⟦t⟧` is a morphism of models from the deformation model of
`X` to the trait (`ProEtale.CondensedRing.deformationToTraitModelHom`), whose squares of special
and of geometric generic fibres are cartesian. When `X` and `𝒳 ⟶ S` are proper (for instance for
a thickened point `X` and `I` the ideal of its rational point, the deformation `𝒳` being then a
nilpotent thickening of `S`), the inverse of its pushforward exchange maps the specialization of
the unit class of the special fibre to the specialization of the unit class of `X`
(`ProEtale.CondensedRing.unitClass_comp_map_comp_deformationCompactSupportExchange_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']

/-- The special fibre square of the deformation model, with the structure map `toPoint`. -/
lemma isPullback_deformationSpecialFibre_toPoint :
    IsPullback (deformationModel X I k').i (toPoint (deformationSpecialFibre X I k')).left
      (deformationTotalToTrait X I k') (traitClosedPoint k') := by
  have h := isPullback_deformationSpecialFibre X I k'
  rw [← toPoint_left (deformationSpecialFibre X I k')] at h
  exact h

/-- The geometric generic fibre square of the deformation model, with the structure map
`toPoint`. -/
lemma isPullback_deformationModel_ε_toPoint :
    IsPullback (deformationModel X I k').ε
      (pullback.snd (deformationTotalToTrait X I k') (traitGenericPoint k')) (toPoint X).left
      (traitModel k k').ε := by
  have h := isPullback_deformationModel_ε_traitModel (X := X) k' I
  rw [← toPoint_left X] at h
  exact h

/-- The structure map `𝒳 ⟶ S` of the deformation to the normal cone over the trait, as a morphism
of models over the structure maps of `X` and of the special fibre. -/
noncomputable def deformationToTraitModelHom :
    (deformationModel X I k').Hom (traitModel k k') (toPoint X).left
      (toPoint (deformationSpecialFibre X I k')).left where
  total := deformationTotalToTrait X I k'
  generic := pullback.snd (deformationTotalToTrait X I k') (traitGenericPoint k')
  comm_j := pullback.condition.symm
  comm_i := (isPullback_deformationSpecialFibre_toPoint X I k').w.symm
  comm_ε := (isPullback_deformationModel_ε_toPoint X I k').w.symm

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [IsProper X.hom]
  [IsProper (deformationTotalToTrait X I k')]

instance : IsProper (deformationSpecialFibre X I k').hom :=
  MorphismProperty.of_isPullback (isPullback_deformationSpecialFibre X I k') inferInstance

instance : IsProper (deformationToTraitModelHom X I k').total :=
  inferInstanceAs (IsProper (deformationTotalToTrait X I k'))

/-- The compact-support exchange `ν_a : Ra'_! Ψ_𝒳 ⟶ Ψ_s Ra_!` of a proper deformation over the
trait: the inverse of the pushforward exchange of `𝒳 ⟶ S`
(`NearbyCyclesModel.Hom.properCompactSupportExchange`). -/
noncomputable def deformationCompactSupportExchange :=
  (deformationToTraitModelHom X I k').properCompactSupportExchange (ℓ := ℓ)
    ((deformationModel X I k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X I k') (deformationModel_exists_comp_ε X I k'))
    ((traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
      (isTraitModel_traitModel k k') ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩)
    (isTraitModel_deformationModel X I k')
    (isPullback_deformationSpecialFibre_toPoint X I k')
    (isPullback_deformationModel_ε_toPoint X I k')

/-- **The inverse proper exchange of a proper deformation specializes the unit class**:
`ν_a(ℚ̄_ℓ) ∘ Ra'_!(σ_𝒳) ∘ [𝒳_s] = Ψ_s([X]) ∘ σ_s`. -/
theorem unitClass_comp_map_comp_deformationCompactSupportExchange_app :
    BorelMooreSection.unitClass ℓ (deformationSpecialFibre X I k') ≫
        (boundedConstructibleLowerShriek ℓ
          (toPoint (deformationSpecialFibre X I k'))).map
          (NearbyCyclesModel.boundedConstructibleUnit ℓ
            ((deformationModel X I k').preservesBoundedConstructible_of_isTraitModel
              (isTraitModel_deformationModel X I k') (deformationModel_exists_comp_ε X I k'))) ≫
        (deformationCompactSupportExchange X I k').app (𝟙_ _) =
      traitSpecializationUnit k k' ≫
        (traitSpecialization k k').map (BorelMooreSection.unitClass ℓ X) :=
  (deformationToTraitModelHom X I k').unitClass_comp_map_comp_properCompactSupportExchange_app _ _
    (isTraitModel_deformationModel X I k')
    (isPullback_deformationSpecialFibre_toPoint X I k')
    (isPullback_deformationModel_ε_toPoint X I k')

end AlgebraicGeometry.ProEtale.CondensedRing
