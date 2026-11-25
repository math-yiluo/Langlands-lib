/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceTraitAlgebra
public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom
public import WeilConjectures.SixFunctors.NearbyCycles.UniversalHomeomorphismExchange

/-!

# The Galois layer of a base change model over `Spec K⟦t⟧`

Let `M` be a model of finite type over the trait `S = Spec k'⟦t⟧` and `M''` its base change along
`v : Spec K⟦t⟧ ⟶ Y` (`NearbyCyclesModel.baseChange`), with projection `φ : M'' ⟶ M`
(`NearbyCyclesModel.baseChangeHom`). With the algebra structures of
`AlgebraicGeometry.traitGenericFieldAlgebra`, `φ` is a morphism of models over the
change of traits `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` with geometric generic points `Spec Ω_K ⟶ Spec Ω`, so
the factorisation of `NearbyCyclesModel.Hom.traitChangeModel` applies:

* `NearbyCyclesModel.baseChangeGaloisModel`: the model `N''` with the total space and special
  fibre of `M''` and generic fibre `Z₂ = (𝒳'' ×_{K⟦t⟧} Spec(Ω ⊗_{k'⟦t⟧} K⟦t⟧)) ×_T Spec L`,
  `L = Ω(K⟦t⟧) ⊆ Ω_K` the compositum;
* `NearbyCyclesModel.baseChangeGaloisLayer`: its Galois layer `N''_{L^sep}` along `Z₂ ⟶ Spec L`
  and the Galois extension `L^sep / L`;
* `NearbyCyclesModel.baseChangeToGaloisLayer`: the morphism of models `ρ : M'' ⟶ N''_{L^sep}`,
  the identity on total spaces and a universal homeomorphism on generic fibres, whose pullback
  exchange is invertible (`NearbyCyclesModel.isIso_pullbackExchange_baseChangeToGaloisLayer`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)

/-- The structure morphism `𝒳'' ⟶ Spec K⟦t⟧` of the total space of the base change `M''` (typed
by the total space of the model, so that terms built from it are syntactically well typed). -/
noncomputable def baseChangeTotalStructure : (baseChange hM b hb v hv).total ⟶ trait K :=
  pullback.snd b v

/-- The structure morphism `𝒳''_η̄ ⟶ Spec Ω_K` of the geometric generic fibre of the base change
`M''`. -/
noncomputable def baseChangeGenericStructure :
    (baseChange hM b hb v hv).generic ⟶ Spec (.of (traitGenericField K)) :=
  pullback.snd _ _

/-- The geometric generic fibre of `M''` is the base change of `Spec Ω_K ⟶ Spec K⟦t⟧`. -/
lemma isPullback_baseChange_j :
    IsPullback (baseChange hM b hb v hv).j (baseChangeGenericStructure hM b hb v hv)
      (baseChangeTotalStructure hM b hb v hv) (traitGenericPoint K) :=
  IsPullback.of_hasPullback _ _

/-- `M'' ⟶ M` lies over the change of traits `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`. -/
lemma baseChangeHom_total_comp :
    (baseChangeHom hM b hb v hv).total ≫ q =
      baseChangeTotalStructure hM b hb v hv ≫ traitMap k' K :=
  pullback_fst_comp_eq_snd_comp_traitMap b hb v hv

/-- `M'' ⟶ M` lies over the map of geometric generic points `Spec Ω_K ⟶ Spec Ω`. -/
lemma baseChangeHom_generic_comp :
    (baseChangeHom hM b hb v hv).generic ≫ g =
      baseChangeGenericStructure hM b hb v hv ≫ traitGenericPointMap k' K :=
  baseChangeGenericMap_g hM b hb v hv

/-- The model `N''` of the change of traits `φ : M'' ⟶ M` from the base change
(`NearbyCyclesModel.Hom.traitChangeModel`): the total space and special fibre of `M''` and the
generic fibre `Z₂ = (𝒳'' ×_{K⟦t⟧} Spec(Ω ⊗_{k'⟦t⟧} K⟦t⟧)) ×_T Spec L`. -/
noncomputable abbrev baseChangeGaloisModel : NearbyCyclesModel X (baseChangeSpecial b v).left :=
  (baseChangeHom hM b hb v hv).traitChangeModel (traitGenericField K)
    (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
    (baseChangeHom_total_comp hM b hb v hv)

/-- The structure map `Z₂ ⟶ Spec L` of the generic fibre of `N''`, `L = Ω(K⟦t⟧)`. -/
noncomputable abbrev baseChangeGaloisResidue :
    (baseChangeGaloisModel hM b hb v hv).generic ⟶
      Spec (.of (traitTensorCompositum (PowerSeries K) (traitGenericField k')
        (traitGenericField K))) :=
  (baseChangeHom hM b hb v hv).traitChangeResidue (traitGenericField K)
    (baseChangeTotalStructure hM b hb v hv) q g hM.isPullback_j.w
    (baseChangeHom_total_comp hM b hb v hv)

/-- The Galois layer `N''_{L^sep}` of `N''` along `Z₂ ⟶ Spec L` and `L^sep / L`. -/
noncomputable abbrev baseChangeGaloisLayer : NearbyCyclesModel X (baseChangeSpecial b v).left :=
  (baseChangeGaloisModel hM b hb v hv).galoisLayer (baseChangeGaloisResidue hM b hb v hv)
    (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))

/-- The morphism of models `ρ : M'' ⟶ N''_{L^sep}` from the base change to the Galois layer: the
identity of total spaces and the purely inseparable part `r₁` on generic fibres. -/
noncomputable abbrev baseChangeToGaloisLayer :
    (baseChange hM b hb v hv).Hom (baseChangeGaloisLayer hM b hb v hv) (𝟙 X) (𝟙 _) :=
  (baseChangeHom hM b hb v hv).toTraitChangeGaloisLayer (traitGenericField K)
    (baseChangeTotalStructure hM b hb v hv) (baseChangeGenericStructure hM b hb v hv) q g
    hM.isPullback_j.w (baseChangeHom_total_comp hM b hb v hv)
    (isPullback_baseChange_j hM b hb v hv).w (baseChangeHom_generic_comp hM b hb v hv)

/-- The projection `Z₁ ⟶ Z₂` of the generic fibre of the Galois layer `N''_{L^sep}`. -/
noncomputable def baseChangeGaloisLayerFst :
    (baseChangeGaloisLayer hM b hb v hv).generic ⟶ (baseChangeGaloisModel hM b hb v hv).generic :=
  pullback.fst _ _

/-- The projection `Z₁ ⟶ Spec L^sep` of the generic fibre of the Galois layer `N''_{L^sep}`. -/
noncomputable def baseChangeGaloisLayerSnd :
    (baseChangeGaloisLayer hM b hb v hv).generic ⟶
      Spec (.of (traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
        (traitGenericField K))) :=
  pullback.snd _ _

/-- The thickening `Z₂ ⟶ 𝒳''_η̄ ×_𝒳 𝒳''` of the generic fibre of `N''`. -/
noncomputable def baseChangeGaloisModelFst :
    (baseChangeGaloisModel hM b hb v hv).generic ⟶
      (baseChangeHom hM b hb v hv).cartesianModel.generic :=
  pullback.fst _ _

/-- Morphisms to the generic fibre `Z₁` of the Galois layer are determined by their projections
to `Z₂` and `Spec L^sep`. -/
lemma baseChangeGaloisLayer_generic_hom_ext {Z : Scheme.{u}}
    {x y : Z ⟶ (baseChangeGaloisLayer hM b hb v hv).generic}
    (h₁ : x ≫ baseChangeGaloisLayerFst hM b hb v hv = y ≫ baseChangeGaloisLayerFst hM b hb v hv)
    (h₂ : x ≫ baseChangeGaloisLayerSnd hM b hb v hv = y ≫ baseChangeGaloisLayerSnd hM b hb v hv) :
    x = y :=
  pullback.hom_ext h₁ h₂

/-- Morphisms to the generic fibre `Z₂` of `N''` are determined by their projections to
`𝒳''_η̄ ×_𝒳 𝒳''` and `Spec L`. -/
lemma baseChangeGaloisModel_generic_hom_ext {Z : Scheme.{u}}
    {x y : Z ⟶ (baseChangeGaloisModel hM b hb v hv).generic}
    (h₁ : x ≫ baseChangeGaloisModelFst hM b hb v hv = y ≫ baseChangeGaloisModelFst hM b hb v hv)
    (h₂ : x ≫ baseChangeGaloisResidue hM b hb v hv = y ≫ baseChangeGaloisResidue hM b hb v hv) :
    x = y :=
  pullback.hom_ext h₁ h₂

/-- The first components of the generic part `r₁` of `ρ`: `r₁ ≫ q ≫ r₂` is the change of generic
fibres of the cartesian model of `M'' ⟶ M`. -/
@[reassoc]
lemma baseChangeToGaloisLayer_generic_fst_fst :
    (baseChangeToGaloisLayer hM b hb v hv).generic ≫ baseChangeGaloisLayerFst hM b hb v hv ≫
        baseChangeGaloisModelFst hM b hb v hv =
      (baseChangeHom hM b hb v hv).toCartesian.generic :=
  (baseChangeHom hM b hb v hv).traitChangeInsepMap_comp_traitChangeGaloisMap_comp
    hM.isPullback_j.w (baseChangeHom_total_comp hM b hb v hv)
    (isPullback_baseChange_j hM b hb v hv).w (baseChangeHom_generic_comp hM b hb v hv)

/-- The component in `Spec L` of the generic part `r₁` of `ρ`. -/
@[reassoc]
lemma baseChangeToGaloisLayer_generic_fst_residue :
    (baseChangeToGaloisLayer hM b hb v hv).generic ≫ baseChangeGaloisLayerFst hM b hb v hv ≫
        baseChangeGaloisResidue hM b hb v hv =
      baseChangeGenericStructure hM b hb v hv ≫ traitTensorSepPoint (PowerSeries K)
        (traitGenericField k') (traitGenericField K) ≫ traitTensorCompositumGalois (PowerSeries K)
          (traitGenericField k') (traitGenericField K) :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

/-- The component in `Spec L^sep` of the generic part `r₁` of `ρ`. -/
@[reassoc]
lemma baseChangeToGaloisLayer_generic_snd :
    (baseChangeToGaloisLayer hM b hb v hv).generic ≫ baseChangeGaloisLayerSnd hM b hb v hv =
      baseChangeGenericStructure hM b hb v hv ≫ traitTensorSepPoint (PowerSeries K)
        (traitGenericField k') (traitGenericField K) :=
  pullback.lift_snd _ _ _

/-- The Galois action on the layer lies over `Z₂`. -/
@[reassoc (attr := simp)]
lemma galoisLayerAut_generic_comp_baseChangeGaloisLayerFst
    (e : Gal(traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
      (traitGenericField K)/traitTensorCompositum (PowerSeries K) (traitGenericField k')
        (traitGenericField K))) :
    ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut (baseChangeGaloisResidue hM b hb v hv)
        _ e).generic ≫ baseChangeGaloisLayerFst hM b hb v hv =
      baseChangeGaloisLayerFst hM b hb v hv :=
  pullbackAction_fst _ _ specGaloisAction_comp e

/-- The Galois action on the layer acts through `Spec e` on `Spec L^sep`. -/
@[reassoc (attr := simp)]
lemma galoisLayerAut_generic_comp_baseChangeGaloisLayerSnd
    (e : Gal(traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
      (traitGenericField K)/traitTensorCompositum (PowerSeries K) (traitGenericField k')
        (traitGenericField K))) :
    ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut (baseChangeGaloisResidue hM b hb v hv)
        _ e).generic ≫ baseChangeGaloisLayerSnd hM b hb v hv =
      baseChangeGaloisLayerSnd hM b hb v hv ≫ specGaloisAction _ _ e :=
  pullbackAction_snd _ _ specGaloisAction_comp e

/-- The generic part of `ρ : M'' ⟶ N''_{L^sep}` is a universal homeomorphism: it is the base
change of `Spec Ω_K ⟶ Spec L^sep`, `Ω_K / L^sep` being purely inseparable. -/
instance isUniversalHomeomorphism_baseChangeToGaloisLayer_generic :
    IsUniversalHomeomorphism (baseChangeToGaloisLayer hM b hb v hv).generic := by
  exact (baseChangeHom hM b hb v hv).isUniversalHomeomorphism_traitChangeInsepMap
    (baseChangeHom_total_comp hM b hb v hv) (isPullback_baseChange_j hM b hb v hv) hM.isPullback_j
    (baseChangeHom_generic_comp hM b hb v hv)

/-- **The pullback exchange of `ρ : M'' ⟶ N''_{L^sep}` is invertible** (all coefficients): `ρ`
is the identity of total spaces and the universal homeomorphism `r₁` on generic fibres. -/
theorem isIso_pullbackExchange_baseChangeToGaloisLayer
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    IsIso (((baseChangeToGaloisLayer hM b hb v hv).pullbackExchange Λ).app C) :=
  Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ
    (baseChangeGaloisLayer hM b hb v hv) (baseChangeToGaloisLayer hM b hb v hv).generic
    (baseChange hM b hb v hv)
    (by
      have hj : (baseChange hM b hb v hv).j = (baseChangeToGaloisLayer hM b hb v hv).generic ≫
          (baseChangeGaloisLayer hM b hb v hv).j := by
        exact (Category.comp_id _).symm.trans (baseChangeToGaloisLayer hM b hb v hv).comm_j.symm
      exact congrArg (fun j ↦ (⟨(baseChange hM b hb v hv).total,
        (baseChange hM b hb v hv).generic, j, (baseChange hM b hb v hv).i,
        (baseChange hM b hb v hv).ε⟩ : NearbyCyclesModel _ _)) hj)
    (baseChangeToGaloisLayer hM b hb v hv) HEq.rfl HEq.rfl C

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
