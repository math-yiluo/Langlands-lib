/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.UniversalKernelFirstInputs
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityOpen
public import WeilConjectures.Tactic.TransportExact

/-!

# Nearby cycles of the universal kernel, the first identity

For the specialization `Sp` to the normal cone of a rational point `x` of `X`, the Künneth–Verdier
maps `λ_K : K ⊠ D K ⟶ RHom(p₂^* K, p₁^! K)` (`ProEtale.CondensedRing.kunnethVerdierMap`) satisfy
the first identity of blueprint `lemma-nearby-cycles-universal-kernel`,

`𝔥 ∘ Sp(λ_K) = λ_{K'} ∘ ρ`,

with `K' = Sp K` and `ρ = (1 ⊠ δ_K) ∘ Π⁻¹` (`ProEtale.CondensedRing.universalKernelSpecialization`)
(`ProEtale.CondensedRing.map_kunnethVerdierMap_comp_eq`). It is the instance of the abstract
`CategoryTheory.map_curry_kunnethPairing_comp_eq`. Its inputs are proved here: the monoidality of
`α_{p₂}`, the definition of `δ_K`, the symmetry of the lax tensor maps of nearby cycles, and
`Π = (α_{p₁} ⊗ α_{p₂}) ≫ μ`. The exceptional exchange `β_{p₁}` and its compatibility with the
exceptional Künneth maps (blueprint `lemma-base-change-maps-external-duality--1`) are hypotheses:
`β_{p₁}` needs the compact-support exchange `ν_{p₁}` of blueprint `prose-E-15` (3) for the
non-proper projection, which is only constructed for compactified morphisms of models.

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

variable {ℓ : ℕ} [Fact ℓ.Prime] (k' : Type u) [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (x : RationalPoint X) (D : NearbyCyclesModel.NearbyDualizingData k k' ℓ)

-- the abstract statement is matched against the concrete functors
/-- **Nearby cycles of the universal kernel**, first identity (blueprint
`lemma-nearby-cycles-universal-kernel`): for an exceptional exchange
`β_{p₁} : Sp_{X×X} p₁^! ⟶ p_{1s}^! Sp_X` compatible with the exceptional Künneth maps (`hκ`,
blueprint `lemma-base-change-maps-external-duality--1`) and the map
`𝔥 : Sp_{X×X} RHom(p₂^* K, p₁^! K) ⟶ RHom(p_{2s}^* K', p_{1s}^! K')` adjoint to
`(α_{p₂} ⊗ 1) ≫ μ ≫ Sp(ev) ≫ β_{p₁}`, the Künneth–Verdier maps satisfy `𝔥 ∘ Sp(λ_K) = λ_{K'} ∘ ρ`,
with `K' = Sp_{X,x} K` and `ρ = (1 ⊠ δ_K) ∘ Π⁻¹`. -/
theorem map_kunnethVerdierMap_comp_eq (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (β₁ : boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X) ⋙ specializationProd k' x ⟶
      specialization k' x ⋙ boundedConstructibleUpperShriek ℓ
        (prod.fst : deformationSpecialFibre X x.left.ker k' ⨯
          deformationSpecialFibre X x.left.ker k' ⟶ _))
    (hκ : ((specializationFstExchange k' x).app K ⊗ₘ
        (specializationSndExchange k' x).app (dualizingComplex' ℓ X)) ≫
        Functor.LaxMonoidal.μ (specializationProd k' x) _ _ ≫
        (specializationProd k' x).map (exceptionalKunnethMap ℓ K) ≫ β₁.app K =
      _ ◁ (boundedConstructibleUpperStar _ ℓ _).map
          (D.θ (isTraitModelOfBase_deformationModel k' x)) ≫
        exceptionalKunnethMap ℓ ((specialization k' x).obj K))
    (𝔥 : (specializationProd k' x).obj
        ((ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K)) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ
          (prod.snd : deformationSpecialFibre X x.left.ker k' ⨯
            deformationSpecialFibre X x.left.ker k' ⟶ _)).obj ((specialization k' x).obj K))).obj
        ((boundedConstructibleUpperShriek ℓ (prod.fst : deformationSpecialFibre X x.left.ker k' ⨯
            deformationSpecialFibre X x.left.ker k' ⟶ _)).obj ((specialization k' x).obj K)))
    (h𝔥 : MonoidalClosed.uncurry 𝔥 = (specializationSndExchange k' x).app K ▷ _ ≫
      Functor.LaxMonoidal.μ (specializationProd k' x) _ _ ≫
      (specializationProd k' x).map ((ihom.ev _).app _) ≫ β₁.app K) :
    (specializationProd k' x).map (kunnethVerdierMap ℓ K K) ≫ 𝔥 =
      universalKernelSpecialization k' x D K ≫
        kunnethVerdierMap ℓ ((specialization k' x).obj K) ((specialization k' x).obj K) := by
  have hα₂ := specializationSndExchange_tensor k' x K (verdierDual ℓ K)
  have hδ := whiskerLeft_specializationDualityMap_comp_ev k' x D K
  have hbr := NearbyCyclesModel.boundedConstructibleNearbyCycles_μ_braiding
    (NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
      (deformationProdModel X x.left.ker X x.left.ker k')
      (isTraitModel_deformationProdModel X x.left.ker X x.left.ker k')
      (deformationProdModel_exists_comp_ε X x.left.ker X x.left.ker k'))
  have key := CategoryTheory.map_curry_kunnethPairing_comp_eq (SX := specialization (ℓ := ℓ) k' x)
    (SP := specializationProd (ℓ := ℓ) k' x) (specializationFstExchange k' x)
    (specializationSndExchange k' x) β₁ ((ihom.ev K).app (dualizingComplex' ℓ X))
    (D.θ (isTraitModelOfBase_deformationModel k' x))
    (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)) _ _)
    (Functor.LaxMonoidal.μ (boundedConstructibleUpperStar _ ℓ
      (prod.snd : deformationSpecialFibre X x.left.ker k' ⨯
        deformationSpecialFibre X x.left.ker k' ⟶ _)))
    (fun g ↦ Functor.LaxMonoidal.μ_natural_right _ _ g)
    (exceptionalKunnethMap ℓ K) (exceptionalKunnethMap ℓ ((specialization k' x).obj K))
    (specializationDualityMap k' x D K) (by transport_exact hδ) (by transport_exact hα₂)
    (by transport_exact hκ) hbr (specializationKunnethMap k' x K (verdierDual ℓ K))
    (by
      apply ObjectProperty.hom_ext
      transport_exact specializationKunnethMap_hom k' x K (verdierDual ℓ K))
    𝔥 (by transport_exact h𝔥)
  unfold kunnethVerdierMap kunnethVerdierPairing universalKernelSpecialization
  transport_exact key

end AlgebraicGeometry.ProEtale.CondensedRing
