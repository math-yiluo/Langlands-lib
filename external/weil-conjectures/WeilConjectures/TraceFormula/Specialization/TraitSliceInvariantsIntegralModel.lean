/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationBoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisLayerAut
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisLayerFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisDegree
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessPadicIntegers
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The data of the stabilization theorem for the Galois layer of a slice

Let `M''` be the base change of a model `M` of finite type over `S = Spec k'⟦t⟧` along
`Spec K⟦t⟧ ⟶ Y` (`NearbyCyclesModel.baseChange`), `N''` the model of its change of traits
(`NearbyCyclesModel.baseChangeGaloisModel`, generic fibre over `L = Ω(K⟦t⟧)`) and `N''_{L^sep}` its
Galois layer. This file provides the data for the stabilization of the nearby cycles of
`N''_{L^sep}` with `ℚ̄_ℓ`-coefficients
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_integralModel`):

* integral models pull back (`ProEtale.CondensedRing.integralModelPullbackIso`);
* if `Lε^* A` extends to a bounded constructible `B` on the total space of `M`, an integral model of
  `Lε^* A` on the generic fibre of `N''` whose reduction has bounded constructible nearby cycles
  on the Galois layer (`NearbyCyclesModel.exists_integralModel_baseChangeGaloisModel`, from
  Deligne's finiteness theorem with finite coefficients);
* the intertwining of the actions by `ρ : M'' ⟶ N''_{L^sep}`, indexed by `Gal(L^sep / L)`
  (`NearbyCyclesModel.pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction_symm`).

-/

@[expose] public section


universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option maxHeartbeats 1000000 in
-- the derived extensions of scalars and pullbacks of module objects are large terms
/-- **Integral models pull back**: an isomorphism `ℚ̄_ℓ ⊗ (E ⊗ B₀) ≅ B` gives
`ℚ̄_ℓ ⊗ (E ⊗ Lw^* B₀) ≅ Lw^* B`, by the compatibility of the extensions of scalars with the derived
pullback (`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso`). -/
noncomputable def integralModelPullbackIso {Z W : Scheme.{u}} (w : Z ⟶ W)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (B₀ : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) W)))
    {B : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) W))}
    (e₀ : (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        W)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) W)).leftDerivedFunctor.obj B₀) ≅ B) :
    (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        Z)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) Z)).leftDerivedFunctor.obj
            (L((w)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧).obj B₀)) ≅
      L((w)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B :=
  (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      Z)).leftDerivedFunctor.mapIso
      ((derivedUpperStarExtendScalarsIso (padicIntegersRingObjToContinuousMapRingObj ℓ E) w).app
        B₀) ≪≫
    (derivedUpperStarExtendScalarsIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) w).app _ ≪≫
    L((w)^*⟦Profinite.padicAlgClRingObj ℓ⟧).mapIso e₀

/-- An isomorphism of an integral model in the ambient derived categories, as an isomorphism of
bounded constructible complexes (the form required by the stabilization theorem). -/
noncomputable def integralModelIso {Z : Scheme.{u}} (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))
    {C : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z) C)
    (e : (Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
        Z)).leftDerivedFunctor.obj ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) Z)).leftDerivedFunctor.obj K₀.obj) ≅
        C) :
    (constructibleToPadicAlgCl Z ℓ E).obj ((boundedConstructibleExtendScalars Z ℓ E).obj K₀) ≅
      ⟨C, hC⟩ :=
  ObjectProperty.isoMk _ e

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)
  {ℓ : ℕ} [Fact ℓ.Prime]

/-- `j'' ≫ φ = (r₂ ≫ pr) ≫ j`. -/
lemma baseChangeGaloisModel_j_comp_total :
    ((baseChangeHom hM b hb v hv).traitChangeThickening (traitGenericField K)
      (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
      (baseChangeHom_total_comp hM b hb v hv) ≫ pullback.fst _ _) ≫ M.j =
    (baseChangeGaloisModel hM b hb v hv).j ≫ (baseChangeHom hM b hb v hv).total := by
  simp only [baseChangeGaloisModel, Hom.traitChangeModel_j, Hom.cartesianModel_j, Category.assoc]
  rw [pullback.condition]

/-- The identification `L(j'')^* Lφ^* B ≅ L(ε'')^* A` on the generic fibre of `N''`. -/
noncomputable def baseChangeGaloisModelPullbackIso
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) :
    L(((baseChangeGaloisModel hM b hb v hv).j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (L(((baseChangeHom hM b hb v hv).total)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B) ≅
      L(((baseChangeGaloisModel hM b hb v hv).ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A :=
  ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (rfl : (baseChangeGaloisModel hM b hb v hv).j ≫ (baseChangeHom hM b hb v hv).total = _)).app
      B).symm ≪≫
    (leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (baseChangeGaloisModel_j_comp_total hM b hb v hv)).app B ≪≫
    L((((baseChangeHom hM b hb v hv).traitChangeThickening (traitGenericField K)
          (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
          (baseChangeHom_total_comp hM b hb v hv) ≫ pullback.fst _ _))^*⟦
            Profinite.padicAlgClRingObj ℓ⟧).mapIso eB ≪≫
    ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
      (Category.assoc _ _ _ : ((baseChangeHom hM b hb v hv).traitChangeThickening
        (traitGenericField K) (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
          (baseChangeHom_total_comp hM b hb v hv) ≫ pullback.fst _ _) ≫ M.ε =
            (baseChangeGaloisModel hM b hb v hv).ε)).app A).symm

set_option maxHeartbeats 4000000 in
-- the integral model is transported along several derived pullbacks of the base change model
/-- **An integral model on the generic fibre of `N''` with finite torsion nearby cycles**: if
`Lε^* A ≅ Lj^* B` for a bounded constructible `B` on the total space of `M`, then `L(ε'')^* A` has
an integral model `K₀` (the pullback of an integral model of `B`) such that the nearby cycles of
the reduction of `K₀` on the Galois layer of `N''` are bounded constructible. -/
theorem exists_integralModel_baseChangeGaloisModel [IsSeparated p] [IsSepClosed K]
    [Fact (ringChar k' ≠ ℓ)]
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total))}
    (hB : boundedConstructible _ B)
    (eB : L((M.j)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B ≅
      L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)
    (hC : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (baseChangeGaloisModel hM b hb v hv).generic)
      (L(((baseChangeGaloisModel hM b hb v hv).ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
        (baseChangeGaloisModel hM b hb v hv).generic))
      (_ : (constructibleToPadicAlgCl _ ℓ E).obj
        ((boundedConstructibleExtendScalars _ ℓ E).obj K₀) ≅ ⟨_, hC⟩),
      boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))
          (baseChangeSpecial b v).left)
        (((((baseChangeGaloisModel hM b hb v hv).toGenericWithSpecial
          (baseChangeGaloisModel hM b hb v hv).i).galoisLayer
            (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
              (traitGenericField k') (traitGenericField K))).nearbyCycles
          (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).obj
          (L((𝟙 (baseChangeGaloisModel hM b hb v hv).generic)^*⟦Profinite.continuousMapRingObj.{u}
            (integersResidueField ℓ E.1)⟧).obj
            ((Mod.extendScalars (coefficientMap
              (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
                (baseChangeGaloisModel hM b hb v hv).generic)).leftDerivedFunctor.obj
                  K₀.obj))) := by
  have : IsNoetherian M.total := hM.isTraitModel.isNoetherian_total
  obtain ⟨E, B₀, ⟨e₀⟩⟩ := exists_padicAlgCl_iso_integralModel_obj ℓ M.total B hB
  have hK₀ := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
    (baseChangeGaloisModel hM b hb v hv).j _
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _
      (baseChangeHom hM b hb v hv).total _ B₀.property)
  refine ⟨E, ⟨_, hK₀⟩, integralModelIso ℓ E ⟨_, hK₀⟩ hC
    (integralModelPullbackIso ℓ (baseChangeGaloisModel hM b hb v hv).j E _
      (integralModelPullbackIso ℓ (baseChangeHom hM b hb v hv).total E B₀.obj e₀) ≪≫
      baseChangeGaloisModelPullbackIso hM b hb v hv eB), ?_⟩
  obtain ⟨p, hp, hpℓ, hpk⟩ := exists_prime_ne_dvd_of_natCast_eq_zero k'
    (Fact.out : ringChar k' ≠ ℓ)
  have : Fact p.Prime := ⟨hp⟩
  have := hasInvertibleExponent_integersResidueField (k' := k') E
  have hred := boundedConstructible_derivedExtendScalars_residueField M.total ℓ E.1 B₀.obj
    B₀.property
  have h := boundedConstructible_nearbyCycles_galoisLayer_baseChangeGaloisModel_of_finite hM b hb
    v hv (integersResidueField ℓ E.1) hpk (isUnit_natCast_integersResidueField E.1 hp hpℓ)
    (L(((baseChangeHom hM b hb v hv).total)^*⟦Profinite.continuousMapRingObj.{u}
      (integersResidueField ℓ E.1)⟧).obj ((Mod.extendScalars (coefficientMap
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) M.total)).leftDerivedFunctor.obj
          B₀.obj))
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ _ (by exact_mod_proofs hred))
  refine (boundedConstructible _).prop_of_iso
    (((((baseChangeGaloisModel hM b hb v hv).toGenericWithSpecial
      (baseChangeGaloisModel hM b hb v hv).i).galoisLayer
        (baseChangeGaloisResidue hM b hb v hv) (traitTensorCompositumSep (PowerSeries K)
          (traitGenericField k') (traitGenericField K))).nearbyCycles
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1))).mapIso
      (L((𝟙 (baseChangeGaloisModel hM b hb v hv).generic)^*⟦Profinite.continuousMapRingObj.{u}
        (integersResidueField ℓ E.1)⟧).mapIso
        ((L(((baseChangeGaloisModel hM b hb v hv).j)^*⟦Profinite.continuousMapRingObj.{u}
          (integersResidueField ℓ E.1)⟧)).mapIso
          ((derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
            (baseChangeHom hM b hb v hv).total).app B₀.obj).symm ≪≫
          ((derivedUpperStarExtendScalarsIso (Profinite.padicIntegersRingObjToResidueField ℓ E.1)
            (baseChangeGaloisModel hM b hb v hv).j).app _).symm))) h

set_option linter.style.whitespace false in
/-- **`ρ` intertwines the actions, indexed by `Gal(L^sep / L)`**: the exchange of
`ρ : M'' ⟶ N''_{L^sep}` carries the action of `τ` on the Galois layer to that of the generic
automorphism `galoisEquiv⁻¹ τ`. -/
lemma pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction_symm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (τ : Gal(traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K) /
      traitTensorCompositum (PowerSeries K) (traitGenericField k') (traitGenericField K)))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((baseChangeToGaloisLayer hM b hb v hv).pullbackExchange Λ).app C ≫
        (baseChangeAut hM b hb v hv (GenericAut.galoisEquiv.symm τ)).autAction Λ
          (L((𝟙 X)^*⟦Λ⟧).obj C) =
      L((𝟙 (baseChangeSpecial b v).left)^*⟦Λ⟧).map
          (((baseChangeGaloisModel hM b hb v hv).galoisLayerAut
            (baseChangeGaloisResidue hM b hb v hv)
            (traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
              (traitGenericField K)) τ).autAction Λ C) ≫
        ((baseChangeToGaloisLayer hM b hb v hv).pullbackExchange Λ).app C := by
  obtain ⟨σ, rfl⟩ := GenericAut.galoisEquiv.surjective τ
  simpa only [MulEquiv.symm_apply_apply] using
    pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction hM b hb v hv Λ σ C

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
