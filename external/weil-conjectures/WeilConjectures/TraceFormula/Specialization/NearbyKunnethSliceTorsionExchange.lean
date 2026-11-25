/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegralFactor
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethLocal
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginTensor

/-!

# Künneth squares with invertible exchanges, and the changes of trait modulo `ϖ`

* For morphisms of models `ρ_M`, `ρ_N`, `ρ_P` between two product configurations whose pullback
  exchanges are invertible at the relevant complexes, the pullback of the Künneth map of the
  target configuration is invertible (after any functor) if and only if the Künneth map of the
  source configuration is
  (`NearbyCyclesModel.isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange`),
  by the square `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`.
* With `𝔽_E`-coefficients, the pullback exchanges of the change of trait `Spec K⟦t⟧ ⟶ S'` to a
  generic slice trait
  (`NearbyCyclesModel.isIso_pullbackExchange_coordinateSliceTraitChangeHom_residueField`)
  and of the change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`, on the models of the geometric generic
  fibres (`NearbyCyclesModel.isIso_pullbackExchange_toGeneric_baseChangeHom_traitMap_residueField`),
  are invertible at complexes bounded below of étale origin (SGA 4½, [Th. finitude], 3.7).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Square

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' XU XU' YU YU' ZU ZU' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'} {MU : NearbyCyclesModel XU XU'}
  {NU : NearbyCyclesModel YU YU'} {PU : NearbyCyclesModel ZU ZU'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'} {e₁ : ZU ⟶ XU}
  {e₁' : ZU' ⟶ XU'} {e₂ : ZU ⟶ YU} {e₂' : ZU' ⟶ YU'} {r₁ : XU ⟶ X} {r₁' : XU' ⟶ X'}
  {r₂ : YU ⟶ Y} {r₂' : YU' ⟶ Y'} {r : ZU ⟶ Z} {r' : ZU' ⟶ Z'}

-- the Künneth maps of the two product configurations are large terms
/-- **Künneth maps along morphisms of models with invertible exchanges**: for morphisms of models
`ρ_M : MU ⟶ M`, `ρ_N : NU ⟶ N`, `ρ_P : PU ⟶ P` compatible with two product configurations, whose
pullback exchanges are invertible at `A`, `B` and `Lf₁^* A ⊗ Lf₂^* B`, and any functor `F`,
`F(Lρ'^* Π_{A,B})` is invertible if and only if `F(Π^U_{Lρ_M^* A, Lρ_N^* B})` is. -/
theorem isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁')
    (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hM : IsIso ((ρM.pullbackExchange Λ).app A)) (hN : IsIso ((ρN.pullbackExchange Λ).app B))
    (hP : IsIso ((ρP.pullbackExchange Λ).app (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)))
    {T : Type*} [Category T]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology ZU') Ab.{u + 1})
      (condensedRingObj Λ ZU')) ⥤ T) :
    IsIso (F.map (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) ↔
      IsIso (F.map (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) := by
  have h := map_kunnethMap_comp_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁ hgen₁ htot₂
    hgen₂ hb₁ hs₁ hb₂ hs₂ A B
  have h' := congrArg F.map h
  simp only [Functor.map_comp] at h'
  exact isIso_iff_of_comp_eq h'

-- the Künneth maps of the two product configurations are large terms
/-- `NearbyCyclesModel.isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange` with the pullback
exchange of `ρ_P` invertible as a natural transformation. -/
theorem isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange' (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') (φ₁U : PU.Hom MU e₁ e₁') (φ₂U : PU.Hom NU e₂ e₂') (ρM : MU.Hom M r₁ r₁')
    (ρN : NU.Hom N r₂ r₂') (ρP : PU.Hom P r r')
    (htot₁ : φ₁U.total ≫ ρM.total = ρP.total ≫ φ₁.total)
    (hgen₁ : φ₁U.generic ≫ ρM.generic = ρP.generic ≫ φ₁.generic)
    (htot₂ : φ₂U.total ≫ ρN.total = ρP.total ≫ φ₂.total)
    (hgen₂ : φ₂U.generic ≫ ρN.generic = ρP.generic ≫ φ₂.generic)
    (hb₁ : e₁ ≫ r₁ = r ≫ f₁) (hs₁ : e₁' ≫ r₁' = r' ≫ f₁') (hb₂ : e₂ ≫ r₂ = r ≫ f₂)
    (hs₂ : e₂' ≫ r₂' = r' ≫ f₂')
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hM : IsIso ((ρM.pullbackExchange Λ).app A)) (hN : IsIso ((ρN.pullbackExchange Λ).app B))
    (hP : IsIso (ρP.pullbackExchange Λ)) {T : Type*} [Category T]
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology ZU') Ab.{u + 1})
      (condensedRingObj Λ ZU')) ⥤ T) :
    IsIso (F.map (L((r')^*⟦Λ⟧).map (kunnethMap Λ φ₁ φ₂ A B))) ↔
      IsIso (F.map (kunnethMap Λ φ₁U φ₂U (L((r₁)^*⟦Λ⟧).obj A) (L((r₂)^*⟦Λ⟧).obj B))) :=
  isIso_map_map_kunnethMap_iff_of_isIso_pullbackExchange Λ φ₁ φ₂ φ₁U φ₂U ρM ρN ρP htot₁ hgen₁
    htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ A B hM hN inferInstance F

end Square

section TraitChange

open GenericSliceTrait

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [Fact (ringChar k' ≠ ℓ)]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

set_option hygiene false in
/-- The condensed field `𝔽̲_E`. -/
local notation "𝔽" => Profinite.continuousMapRingObj (PadicAlgCl.integersResidueField ℓ E.1)

/-- **Change of trait to the generic slice trait, `𝔽_E`-coefficients** (SGA 4½, [Th. finitude],
3.7): on the models of the geometric generic fibres, the pullback exchange of the change of
strictly henselian trait `τ : (𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ over Spec K⟦t⟧) ⟶ (X' over S')` with
`𝔽_E`-coefficients is an isomorphism at every complex on the geometric generic fibre of `X'`
which is bounded below of étale origin. -/
theorem isIso_pullbackExchange_coordinateSliceTraitChangeHom_residueField
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))) Ab.{u + 1})
      (condensedRingObj 𝔽
        (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1)))
      (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
      ((finiteCoefficientDerivedEquivalence
        (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj B)) :
    IsIso (((coordinateSliceTraitChangeHom hM b hb D).pullbackExchange 𝔽).app B) := by
  have : Fact (ringChar D.κ ≠ ℓ) := ⟨D.ringChar_κ ▸ Fact.out⟩
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have : LocallyOfFiniteType b := by
    subst hb
    exact locallyOfFiniteType_of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : QuasiCompact b := by
    subst hb
    exact QuasiCompact.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : IsSeparated b := by
    subst hb
    exact IsSeparated.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have hB' := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    _ (𝟙 _) hB
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait_residueField (ι := D.ι) (a₁ := D.a)
    (a₂ := algebraMap _ _) (c := D.ωK) (b₁ := D.b) (b₂ := PowerSeries.constantCoeff)
    D.injective_ι D.maximalIdeal_eq_map_ι D.injective_a
    (algebraMap_traitGenericField_injective _) D.isAlgebraic_a
    (isAlgebraic_traitGenericField _) D.ωK_comp_a D.ker_b
    PowerSeries.ker_coeff_eq_max_ideal (coordinateSliceTraitChangeHom hM b hb D)
    (pullback.snd b D.toAffineLine) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (pullback.snd _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (isPullback_coordinateSliceTraitChangeTotal b D) (pullback.lift_snd _ _ _) E hB'

variable [IsSepClosed k'] {K : Type u} [Field K] [Algebra k' K] [IsSepClosed K]

/-- **Change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`, `𝔽_E`-coefficients, on the geometric generic
fibres** (SGA 4½, [Th. finitude], 3.7): on the models of the geometric generic fibres, the
pullback exchange of the change of trait of a model of finite type over `Spec k'⟦t⟧` is an
isomorphism at every complex bounded below of étale origin. -/
theorem isIso_pullbackExchange_toGeneric_baseChangeHom_traitMap_residueField
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj 𝔽 M.generic))}
    (hB : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integersResidueField ℓ E.1))) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic
        (PadicAlgCl.integersResidueField ℓ E.1)).functor.obj B)) :
    IsIso (((baseChangeHom hM q (Category.comp_id q) (traitMap k' K)
      (Category.comp_id _)).toGeneric.pullbackExchange 𝔽).app B) := by
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have hT := IsTraitModelOver.baseChange hM q (Category.comp_id q) (traitMap k' K)
    (Category.comp_id _)
  have hB' := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    _ (𝟙 _) hB
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait_residueField
    (PowerSeries.map_injective _ (algebraMap k' K).injective)
    (maximalIdeal_powerSeries_eq_map k' K) (algebraMap_traitGenericField_injective k')
    (algebraMap_traitGenericField_injective K) (isAlgebraic_traitGenericField k')
    (isAlgebraic_traitGenericField K) (traitGenericFieldMap_comp_algebraMap k' K)
    PowerSeries.ker_coeff_eq_max_ideal PowerSeries.ker_coeff_eq_max_ideal
    (baseChangeHom hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)).toGeneric q g
    hM.isPullback_j X'.hom hM.isPullback_i _ _ hT.isPullback_j _ hT.isPullback_i
    (IsPullback.of_hasPullback q (traitMap k' K))
    (baseChangeGenericMap_g hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _))
    E hB'

end TraitChange

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
