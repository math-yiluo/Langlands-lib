/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCyclesBraided
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen
public import WeilConjectures.Tactic.TransportExact

/-!

# Inputs of the first identity of the universal kernel

The pullback exchanges `α_{p_i}` of the projections of the product of deformation models
(`ProEtale.CondensedRing.specializationFstExchange`,
`ProEtale.CondensedRing.specializationSndExchange`), in
the lax monoidal form used by the first identity of blueprint
`lemma-nearby-cycles-universal-kernel`: the monoidality of `α_{p₂}`
(`ProEtale.CondensedRing.specializationSndExchange_tensor`) and the defining property of the duality
map `δ_K` (`ProEtale.CondensedRing.whiskerLeft_specializationDualityMap_comp_ev`).

-/
@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding
  NearbyCyclesModel.boundedConstructibleNearbyCyclesLaxMonoidal

attribute [local instance] specializationLaxMonoidal specializationProdLaxMonoidal

namespace NearbyCyclesModel

/-- The restricted pullback exchange respects the lax monoidal tensor maps. Keeping the models
abstract here avoids rewriting tensor maps after substituting the deformation models. -/
private lemma Hom.boundedConstructiblePullbackExchange_lax_tensor
    {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k] [Field k']
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {X' Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
    {j : Y ⟶ X} {j' : Y' ⟶ X'} (φ : N.Hom M j.left j'.left)
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app A ⊗ₘ
        (φ.boundedConstructiblePullbackExchange ℓ hN hM).app B) ≫
        Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hN) _ _ ≫
          (boundedConstructibleNearbyCycles hN).map (Functor.LaxMonoidal.μ
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j) A B) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j')
          _ _ ≫ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
          (Functor.LaxMonoidal.μ (boundedConstructibleNearbyCycles hM) A B) ≫
        (φ.boundedConstructiblePullbackExchange ℓ hN hM).app (A ⊗ B) := by
  rw [boundedConstructibleNearbyCycles_μ, boundedConstructibleNearbyCycles_μ]
  transport_exact φ.boundedConstructiblePullbackExchange_tensor hN hM A B

end NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X) (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)

/-- The pullback exchange `α_{p₁} : p_{1s}^* Sp_X ⟶ Sp_{X×X} p₁^*` of the first projection. -/
noncomputable abbrev specializationFstExchange :
    specialization (ℓ := ℓ) k' x ⋙ boundedConstructibleUpperStar _ ℓ
        (prod.fst : deformationSpecialFibre X x.left.ker k' ⨯
          deformationSpecialFibre X x.left.ker k' ⟶ _) ⟶
      boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X) ⋙ specializationProd k' x :=
  (deformationProdFstModelHom X x.left.ker X x.left.ker k').boundedConstructiblePullbackExchange ℓ
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))

/-- The pullback exchange `α_{p₂} : p_{2s}^* Sp_X ⟶ Sp_{X×X} p₂^*` of the second projection. -/
noncomputable abbrev specializationSndExchange :
    specialization (ℓ := ℓ) k' x ⋙ boundedConstructibleUpperStar _ ℓ
        (prod.snd : deformationSpecialFibre X x.left.ker k' ⨯
          deformationSpecialFibre X x.left.ker k' ⟶ _) ⟶
      boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X) ⋙ specializationProd k' x :=
  (deformationProdSndModelHom X x.left.ker X x.left.ker k').boundedConstructiblePullbackExchange ℓ
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k'))

/-- **The pullback exchange of the second projection is monoidal**, in the lax form:
`(α ⊗ α) ≫ μ ≫ Sp(μ) = μ ≫ p_{2s}^*(μ) ≫ α`. -/
lemma specializationSndExchange_tensor (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((specializationSndExchange k' x).app K ⊗ₘ (specializationSndExchange k' x).app N) ≫
        Functor.LaxMonoidal.μ (specializationProd k' x) _ _ ≫
        (specializationProd k' x).map
          (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)) K N) =
      Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
          (prod.snd : deformationSpecialFibre X x.left.ker k' ⨯
            deformationSpecialFibre X x.left.ker k' ⟶ _)) _ _ ≫
        (boundedConstructibleUpperStar _ ℓ _).map
          (Functor.LaxMonoidal.μ (specialization k' x) K N) ≫
        (specializationSndExchange k' x).app (K ⊗ N) := by
  have h :=
    NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_lax_tensor
      (deformationProdSndModelHom X x.left.ker X x.left.ker k')
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
    ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
      (isTraitModel_deformationModel X x.left.ker k')
      (deformationModel_exists_comp_ε X x.left.ker k')) K N
  transport_exact h

/-- The duality map `δ_K` of the specialization is the adjoint of `θ ∘ Sp(ev) ∘ μ`. -/
lemma whiskerLeft_specializationDualityMap_comp_ev
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specialization k' x).obj K ◁ specializationDualityMap k' x D K ≫
        (ihom.ev ((specialization k' x).obj K)).app
          (dualizingComplex ℓ (deformationSpecialFibre X x.left.ker k')) =
      Functor.LaxMonoidal.μ (specialization k' x) K (verdierDual ℓ K) ≫
        (specialization k' x).map ((ihom.ev K).app (dualizingComplex ℓ X)) ≫
        D.θ (isTraitModelOfBase_deformationModel k' x) := by
  have h := Verdier.whiskerLeft_nearbyDualityMap_comp_ev
    (NearbyCyclesModel.boundedConstructibleTensorMap
      ((deformationModel X x.left.ker k').preservesBoundedConstructible_of_isTraitModel
        (isTraitModel_deformationModel X x.left.ker k')
        (deformationModel_exists_comp_ε X x.left.ker k')))
    (D.θ (isTraitModelOfBase_deformationModel k' x)) K
  rw [← NearbyCyclesModel.boundedConstructibleNearbyCycles_μ] at h
  transport_exact h

/-- The Künneth map `Π` of the specialization is `(α_{p₁} ⊗ α_{p₂}) ≫ μ`, on the ambient derived
category. -/
lemma specializationKunnethMap_hom (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (specializationKunnethMap k' x K N).hom =
      (((specializationFstExchange k' x).app K ⊗ₘ (specializationSndExchange k' x).app N) ≫
        Functor.LaxMonoidal.μ (specializationProd k' x) _ _).hom := by
  have hμ : ∀ A B, (Functor.LaxMonoidal.μ (specializationProd (ℓ := ℓ) k' x) A B).hom =
      (deformationProdModel X x.left.ker X x.left.ker k').tensorMap _ A.obj B.obj :=
    fun A B ↦ congrArg InducedCategory.Hom.hom
      (NearbyCyclesModel.boundedConstructibleNearbyCycles_μ _ A B)
  simp only [specializationKunnethMap, ObjectProperty.homMk_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.tensorHom_hom',
    NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_app_hom, hμ,
    NearbyCyclesModel.kunnethMap]
  transport_rfl

end AlgebraicGeometry.ProEtale.CondensedRing
