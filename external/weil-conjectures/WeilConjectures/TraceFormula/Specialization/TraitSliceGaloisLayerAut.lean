/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisGroup
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap

/-!

# Generic automorphisms act on the Galois layer through `Gal(L^sep / L)`

Let `M''` be the base change of a model `M` over `Spec k'⟦t⟧` to `Spec K⟦t⟧`, and
`ρ : M'' ⟶ N''_{L^sep}` the morphism of models to the Galois layer of
`NearbyCyclesModel.baseChangeToGaloisLayer`. A generic automorphism `σ`
(`NearbyCyclesModel.GenericAut`) acts on `M''` (`NearbyCyclesModel.baseChangeAut`) and, through
its restriction `e σ ∈ Gal(L^sep / L)` (`NearbyCyclesModel.GenericAut.galoisEquiv`), on the Galois
layer (`NearbyCyclesModel.galoisLayerAut`). These actions are intertwined by `ρ`:

* on generic fibres, `σ ≫ ρ = ρ ≫ e σ`
  (`NearbyCyclesModel.baseChangeAut_generic_comp_baseChangeToGaloisLayer_generic`);
* hence the pullback exchange of `ρ` intertwines the actions on nearby cycles
  (`NearbyCyclesModel.pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

attribute [local instance] traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- A generic automorphism is `Spec` of its ring automorphism of `Ω_K`. -/
lemma GenericAut.specMap_toRingAut (σ : GenericAut k' K) :
    Spec.map (CommRingCat.ofHom ((GenericAut.toRingAut σ : traitGenericField K ≃+* _) :
      traitGenericField K →+* traitGenericField K)) = σ.τ := by
  conv_rhs => rw [← Spec.map_preimage σ.τ]
  rfl

/-- **The restriction to `L^sep` of a generic automorphism**: `σ ≫ (Spec Ω_K ⟶ Spec L^sep)` is
`(Spec Ω_K ⟶ Spec L^sep) ≫ Spec (e σ)`. -/
@[reassoc]
lemma GenericAut.τ_comp_traitTensorSepPoint (σ : GenericAut k' K) :
    σ.τ ≫ traitTensorSepPoint (PowerSeries K) (traitGenericField k') (traitGenericField K) =
      traitTensorSepPoint (PowerSeries K) (traitGenericField k') (traitGenericField K) ≫
        specGaloisAction _ _ (GenericAut.galoisEquiv σ) := by
  rw [← GenericAut.specMap_toRingAut, traitTensorSepPoint, specGaloisAction, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext y
  exact (GenericAut.algebraMap_toGalois_apply σ y).symm

variable {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {Y : Scheme.{u}} (b : M.total ⟶ Y) {p : Y ⟶ trait k'}
  (hb : b ≫ p = q) (v : trait K ⟶ Y) (hv : v ≫ p = traitMap k' K)

/-- The action of `σ` on `M''` commutes with the projection to the geometric generic fibre of
the cartesian model of `M'' ⟶ M`. -/
lemma baseChangeAut_generic_comp_toCartesian_generic (σ : GenericAut k' K) :
    (baseChangeAut hM b hb v hv σ).generic ≫ (baseChangeHom hM b hb v hv).toCartesian.generic =
      (baseChangeHom hM b hb v hv).toCartesian.generic := by
  rw [Hom.toCartesian_generic]
  apply pullback.hom_ext
  · erw [Category.assoc, pullback.lift_fst]
    exact baseChangeAut_generic_comp hM b hb v hv σ
  · erw [Category.assoc, pullback.lift_snd]
    exact (baseChangeAut hM b hb v hv σ).comm_j.trans (Category.comp_id _)

/-- The action of `σ` on `M''` lies over `σ` on `Spec Ω_K`. -/
@[reassoc]
lemma baseChangeAut_generic_comp_snd (σ : GenericAut k' K) :
    (baseChangeAut hM b hb v hv σ).generic ≫ baseChangeGenericStructure hM b hb v hv =
      baseChangeGenericStructure hM b hb v hv ≫ σ.τ :=
  pullback.lift_snd _ _ _

/-- **`ρ` intertwines the generic automorphisms and the Galois action on the layer**, on generic
fibres: `σ ≫ ρ = ρ ≫ e σ`. -/
theorem baseChangeAut_generic_comp_baseChangeToGaloisLayer_generic (σ : GenericAut k' K) :
    (baseChangeAut hM b hb v hv σ).generic ≫ (baseChangeToGaloisLayer hM b hb v hv).generic =
      (baseChangeToGaloisLayer hM b hb v hv).generic ≫
        ((baseChangeGaloisModel hM b hb v hv).galoisLayerAut (baseChangeGaloisResidue hM b hb v hv)
          (traitTensorCompositumSep (PowerSeries K) (traitGenericField k') (traitGenericField K))
          (GenericAut.galoisEquiv σ)).generic := by
  refine baseChangeGaloisLayer_generic_hom_ext hM b hb v hv ?_ ?_
  · refine baseChangeGaloisModel_generic_hom_ext hM b hb v hv ?_ ?_
    · simp only [Category.assoc, galoisLayerAut_generic_comp_baseChangeGaloisLayerFst_assoc,
        baseChangeToGaloisLayer_generic_fst_fst]
      exact baseChangeAut_generic_comp_toCartesian_generic hM b hb v hv σ
    · simp only [Category.assoc, galoisLayerAut_generic_comp_baseChangeGaloisLayerFst_assoc,
        baseChangeToGaloisLayer_generic_fst_residue]
      rw [baseChangeAut_generic_comp_snd_assoc, GenericAut.τ_comp_traitTensorSepPoint_assoc,
        traitTensorCompositumGalois, specGaloisAction_comp]
  · simp only [Category.assoc, galoisLayerAut_generic_comp_baseChangeGaloisLayerSnd,
      baseChangeToGaloisLayer_generic_snd, baseChangeToGaloisLayer_generic_snd_assoc]
    rw [baseChangeAut_generic_comp_snd_assoc, GenericAut.τ_comp_traitTensorSepPoint]

/-- **The exchange of `ρ` intertwines the actions on nearby cycles**: the action of a generic
automorphism `σ` on `Ψ_{M''}` and the Galois action of its restriction `e σ` on the nearby cycles
of the layer `N''_{L^sep}`. -/
theorem pullbackExchange_baseChangeToGaloisLayer_app_comp_autAction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (σ : GenericAut k' K)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    ((baseChangeToGaloisLayer hM b hb v hv).pullbackExchange Λ).app C ≫
        (baseChangeAut hM b hb v hv σ).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj C) =
      L((𝟙 (baseChangeSpecial b v).left)^*⟦Λ⟧).map
          (((baseChangeGaloisModel hM b hb v hv).galoisLayerAut
            (baseChangeGaloisResidue hM b hb v hv)
            (traitTensorCompositumSep (PowerSeries K) (traitGenericField k')
              (traitGenericField K)) (GenericAut.galoisEquiv σ)).autAction Λ C) ≫
        ((baseChangeToGaloisLayer hM b hb v hv).pullbackExchange Λ).app C := by
  exact Hom.pullbackExchange_app_comp_autAction_of_comm Λ (baseChangeToGaloisLayer hM b hb v hv)
    (baseChangeAut hM b hb v hv σ) _ rfl
    (baseChangeAut_generic_comp_baseChangeToGaloisLayer_generic hM b hb v hv σ) C

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
