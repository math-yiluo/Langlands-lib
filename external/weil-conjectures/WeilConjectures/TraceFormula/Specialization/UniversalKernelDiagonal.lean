/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.DiagExternalProduct
public import WeilConjectures.TraceFormula.Specialization.UniversalKernel
public import WeilConjectures.Tactic.TransportExact

/-!

# Nearby cycles of the universal kernel, the second identity

For the specialization `Sp_{X,x}` to the normal cone of a rational point, the comparison
`ρ = (1 ⊠ δ_K) ∘ Π⁻¹ : Sp(K ⊠ D K) ⟶ K' ⊠ D K'` of the universal kernels
(`ProEtale.CondensedRing.universalKernelSpecialization`) satisfies the second identity of
blueprint `lemma-nearby-cycles-universal-kernel`,

`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`

(`ProEtale.CondensedRing.universalKernelSpecialization_comp_evaluationKernel`). It is the
instance of the abstract `CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange` and
`CategoryTheory.map_comp_ev_eq_of_kunneth`, the input being that the restriction of the Künneth
map to the diagonal is the lax tensor map of nearby cycles
(`ProEtale.CondensedRing.map_specializationKunnethMap_comp_pullbackExchange`). The latter is
transported from its ambient form
`ProEtale.CondensedRing.NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction`
with `transport_exact`, since the two differ only in the spelling of the objects.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X)

-- the ambient identity is transported to the bounded constructible forms of the objects
/-- The restriction of the Künneth map `Π_{K,L}` to the diagonal is the lax tensor map `μ_X` of
the specialization, through the pullback exchange `α_Δ` and the identifications
`LΔ^*(M ⊠ N) ≅ M ⊗ N` (the composition law and monoidality of the pullback exchanges, with
`p_i ∘ Δ = 1`). -/
lemma map_specializationKunnethMap_comp_pullbackExchange
    (K L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
        (specializationKunnethMap k' x K L) ≫
      ((deformationDiagModelHom X x.left.ker k').boundedConstructiblePullbackExchange ℓ
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k'))
        (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
          (deformationProdModel X x.left.ker X x.left.ker k')
          (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
          (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))).app
        (externalProduct ℓ K L) ≫
      (specialization k' x).map (diagUpperStarExternalProductIso ℓ K L).hom =
    (diagUpperStarExternalProductIso ℓ _ _).hom ≫
      NearbyCyclesModel.boundedConstructibleTensorMap
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k')) K L := by
  have hb₁ : (diag X).left ≫ (prod.fst : X ⨯ X ⟶ X).left = 𝟙 X.left := by
    rw [← Over.comp_left, diag, prod.lift_fst, Over.id_left]
  have hb₂ : (diag X).left ≫ (prod.snd : X ⨯ X ⟶ X).left = 𝟙 X.left := by
    rw [← Over.comp_left, diag, prod.lift_snd, Over.id_left]
  have hs₁ : (diag (deformationSpecialFibre X x.left.ker k')).left ≫
      (prod.fst : _ ⨯ _ ⟶ deformationSpecialFibre X x.left.ker k').left = 𝟙 _ := by
    rw [← Over.comp_left, diag, prod.lift_fst, Over.id_left]
  have hs₂ : (diag (deformationSpecialFibre X x.left.ker k')).left ≫
      (prod.snd : _ ⨯ _ ⟶ deformationSpecialFibre X x.left.ker k').left = 𝟙 _ := by
    rw [← Over.comp_left, diag, prod.lift_snd, Over.id_left]
  have htot₁ : (deformationDiagModelHom X x.left.ker k').total ≫
      (deformationProdFstModelHom X x.left.ker X x.left.ker k').total = 𝟙 _ :=
    pullback.lift_fst _ _ _
  have htot₂ : (deformationDiagModelHom X x.left.ker k').total ≫
      (deformationProdSndModelHom X x.left.ker X x.left.ker k').total = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hgen₁ : (deformationDiagModelHom X x.left.ker k').generic ≫
      (deformationProdFstModelHom X x.left.ker X x.left.ker k').generic = 𝟙 _ := by
    change deformationDiagGeneric X x.left.ker k' ≫
      deformationProdFstGeneric X x.left.ker X x.left.ker k' = 𝟙 _
    apply pullback.hom_ext <;>
      simp only [deformationDiagGeneric, deformationProdFstGeneric, deformationDiagTotal,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.comp_id, Category.id_comp]
  have hgen₂ : (deformationDiagModelHom X x.left.ker k').generic ≫
      (deformationProdSndModelHom X x.left.ker X x.left.ker k').generic = 𝟙 _ := by
    change deformationDiagGeneric X x.left.ker k' ≫
      deformationProdSndGeneric X x.left.ker X x.left.ker k' = 𝟙 _
    apply pullback.hom_ext <;>
      simp only [deformationDiagGeneric, deformationProdSndGeneric, deformationDiagTotal,
        Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        Category.comp_id, Category.id_comp]
  have hmapU : ∀ {A B : Dᵇc((deformationSpecialFibre X x.left.ker k' ⨯
      deformationSpecialFibre X x.left.ker k').left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : A ⟶ B),
      ((boundedConstructibleUpperStar _ ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
        g).hom =
        L(((diag (deformationSpecialFibre X x.left.ker k')).left)^*⟦Profinite.padicAlgClRingObj
          ℓ⟧).map g.hom :=
    fun _ ↦ rfl
  have hmapS : ∀ {A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (g : A ⟶ B),
      ((specialization k' x).map g).hom =
        ((deformationModel X x.left.ker k').nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
          g.hom := fun _ ↦ rfl
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, hmapU, hmapS,
    NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_app_hom,
    diagUpperStarExternalProductIso_hom_hom ℓ _ _ hb₁ hb₂,
    diagUpperStarExternalProductIso_hom_hom ℓ _ _ hs₁ hs₂, specializationKunnethMap,
    ObjectProperty.homMk_hom, NearbyCyclesModel.boundedConstructibleTensorMap, Category.assoc]
  have hamb := NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange_of_retraction
    (Profinite.padicAlgClRingObj ℓ) (deformationProdFstModelHom X x.left.ker X x.left.ker k')
    (deformationProdSndModelHom X x.left.ker X x.left.ker k')
    (deformationDiagModelHom X x.left.ker k') htot₁ hgen₁ htot₂ hgen₂ hb₁ hs₁ hb₂ hs₂ K.obj L.obj
  transport_exact hamb

variable (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)

-- matching the abstract statements against the concrete functors
/-- **Nearby cycles of the universal kernel**, second identity (blueprint
`lemma-nearby-cycles-universal-kernel`): for `ρ = (1 ⊠ δ_K) ∘ Π⁻¹`, the evaluation kernels satisfy
`e_{K'} ∘ ρ = RΔ_{s*} θ_X ∘ χ_Δ ∘ S(e_K)`, with `K' = Sp_{X,x}(K)`. -/
theorem universalKernelSpecialization_comp_evaluationKernel
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    universalKernelSpecialization k' x D K ≫ evaluationKernel ℓ ((specialization k' x).obj K) =
      (specializationProd k' x).map (evaluationKernel ℓ K) ≫
        (Correspondence.IsContractingAt.diagPushforwardExchange ℓ X k' x).app
          (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar ℓ (diag (deformationSpecialFibre X x.left.ker k'))).map
          (D.θ (isTraitModelOfBase_deformationModel k' x)) := by
  have hρ := CategoryTheory.map_comp_ev_eq_of_kunneth
    ((deformationDiagModelHom X x.left.ker k').boundedConstructiblePullbackExchange ℓ
      ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel X x.left.ker k')
        (deformationModel_exists_comp_ε X x.left.ker k'))
      (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
        (deformationProdModel X x.left.ker X x.left.ker k')
        (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
        (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k')))
    (diagUpperStarExternalProductIso ℓ K (verdierDual ℓ K))
    (diagUpperStarExternalProductIso ℓ ((specialization k' x).obj K)
      ((specialization k' x).obj (verdierDual ℓ K)))
    (diagUpperStarExternalProductIso ℓ ((specialization k' x).obj K)
      (verdierDual ℓ ((specialization k' x).obj K)))
    (NearbyCyclesModel.boundedConstructibleTensorMap
        ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
          (isTraitModel_deformationModel X x.left.ker k')
          (deformationModel_exists_comp_ε X x.left.ker k')) K (verdierDual ℓ K))
    ((ihom.ev K).app (dualizingComplex' ℓ X)) (D.θ (isTraitModelOfBase_deformationModel k' x))
    (specializationDualityMap k' x D K)
    (Verdier.whiskerLeft_nearbyDualityMap_comp_ev _ _ K)
    (specializationKunnethMap k' x K (verdierDual ℓ K))
    (map_specializationKunnethMap_comp_pullbackExchange k' x K (verdierDual ℓ K))
    (_ ◁ (boundedConstructibleUpperStar _ ℓ _).map (specializationDualityMap k' x D K))
    (diagUpperStarExternalProductIso_hom_naturality_right ℓ _ (specializationDualityMap k' x D K))
  have hχ :=
    NearbyCyclesModel.Hom.map_boundedConstructiblePushforwardExchange_app_comp_counit_app (ℓ := ℓ)
    (deformationDiagModelHom X x.left.ker k')
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
  unfold universalKernelSpecialization evaluationKernel
  simp only [specialization, specializationProd,
    Correspondence.IsContractingAt.diagPushforwardExchange] at hρ ⊢
  apply_by_match CategoryTheory.comp_homEquiv_eq_map_homEquiv_comp_exchange
    [a := boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X),
      a' := boundedConstructibleUpperStarLowerStarAdjunction ℓ
        (diag (deformationSpecialFibre X x.left.ker k')), hχ := hχ, hρ := hρ]

end AlgebraicGeometry.ProEtale.CondensedRing
