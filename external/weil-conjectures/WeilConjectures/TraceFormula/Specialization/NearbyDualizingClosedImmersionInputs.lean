/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.BoundedConstructiblePushforwardExchangeComp

/-!

# The closed-immersion law of the dualizing maps: the inputs over a generic base

For a morphism `φ : N ⟶ M` of trait models over a generic base, over proper `i₁ : Y₁ ⟶ X₁` and
`i₂ : Y' ⟶ X'`, this file states the inputs of the diagram chase
`CategoryTheory.closedImmersionLaw_aux` behind the closed-immersion law
`θ_N ∘ Ψ_N(ρ) = ρ' ∘ Ri₂^!(θ_M) ∘ β_φ(ω_{X₁})` of the dualizing maps, each in the exact shape
expected there:

* the exceptional adjunction of `β_φ`
  (`NearbyCyclesModel.Hom.pushforwardExchange_app_comp_lowerStar_map_exceptionalExchange_app`);
* the composition law of the proper exchanges `χ_{a_N} = Ra'_*(χ_φ) ∘ χ_{a_M}(Ri₁_*)`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.pushforwardExchange_app_comp_lowerStarCompOfEq`);
* the naturality square of the proper exchange `χ_{a_M}`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.pushforwardExchange_naturality_symm`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  {X₁ Y₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
  [IsSeparated X₁.hom] [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {N : NearbyCyclesModel Y₁.left Y'.left} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- The naturality square of the proper exchange `χ_a` of a trait model over a generic base. -/
lemma IsTraitModelOfGenericBase.pushforwardExchange_naturality_symm
    (h : M.IsTraitModelOfGenericBase X₁ ι q g)
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀ : g ≫ ε₀ = M.ε ≫ X₁.hom)
    {K L : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : K ⟶ L) :
    (h.pushforwardExchange ℓ ε₀ hε₀).app K ≫
        (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
          ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).map f) =
      (traitPointSpecialization ε₀ ℓ).map
          ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁)).map f) ≫
        (h.pushforwardExchange ℓ ε₀ hε₀).app L :=
  ((h.pushforwardExchange ℓ ε₀ hε₀).naturality f).symm

/-- **The composition law of the proper exchanges along a morphism of trait models** over a
generic base: for `φ : N ⟶ M` over `i₁ : Y₁ ⟶ X₁`, `i₂ : Y' ⟶ X'`, compatible with the structure
morphisms to the trait, `χ_{a_N} = Ra_{X'*}(χ_φ) ∘ χ_{a_M}(Ri₁_*)` through the composition
isomorphisms of the direct images. -/
lemma IsTraitModelOfGenericBase.pushforwardExchange_app_comp_lowerStarCompOfEq
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    (ε₀ : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (hε₀M : g ≫ ε₀ = M.ε ≫ X₁.hom)
    (hε₀N : gN ≫ ε₀ = N.ε ≫ Y₁.hom) (i₁ : Y₁ ⟶ X₁) (i₂ : Y' ⟶ X')
    (φ : N.Hom M i₁.left i₂.left) (hq : qN = φ.total ≫ q) (hg : gN = φ.generic ≫ g)
    (K : Dᵇc(Y₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (hN.pushforwardExchange ℓ ε₀ hε₀N).app K ≫
        (boundedConstructibleLowerStarCompOfEq ℓ i₂ (CondensedRing.toPoint X')
          (comp_toPoint i₂)).inv.app
          ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).obj K) =
      (traitPointSpecialization ε₀ ℓ).map
          ((boundedConstructibleLowerStarCompOfEq ℓ i₁ (CondensedRing.toPoint X₁)
            (comp_toPoint i₁)).inv.app K) ≫
        (hM.pushforwardExchange ℓ ε₀ hε₀M).app ((boundedConstructibleLowerStar ℓ i₁).obj K) ≫
        (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X')).map
          ((φ.boundedConstructiblePushforwardExchange ℓ
            (hN.preservesBoundedConstructible (ℓ := ℓ))
            (hM.preservesBoundedConstructible (ℓ := ℓ))).app K) :=
  Hom.boundedConstructiblePushforwardExchange_comp_app_of_eq ℓ φ (hM.toPoint ε₀ hε₀M)
    (hN.toPoint ε₀ hε₀N) (comp_toPoint i₁) (comp_toPoint i₂) hq.symm hg.symm _ _ _ K

/-- **The exceptional adjunction of `β_φ`**: if `ν : Ri₂_! Ψ_N ⟶ Ψ_M Ri₁_!` inverts the proper
exchange `χ_φ` under `Ri_! ≅ Ri_*`, its exceptional adjoint `β_φ` satisfies
`ε_{i₂} ∘ Ri₂_*(β_φ) ∘ χ_φ(Ri₁^!) = Ψ_M(ε_{i₁})` for the traces `ε_i : Ri_* Ri^! ⟶ 𝟭`. -/
lemma Hom.pushforwardExchange_app_comp_lowerStar_map_exceptionalExchange_app
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    (i₁ : Y₁ ⟶ X₁) [IsProper i₁.left] (i₂ : Y' ⟶ X') [IsProper i₂.left]
    (φ : N.Hom M i₁.left i₂.left)
    (ν : boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ)) ⋙
        boundedConstructibleLowerShriek ℓ i₂ ⟶
      boundedConstructibleLowerShriek ℓ i₁ ⋙
        boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ)))
    (hν : ∀ K, (φ.boundedConstructiblePushforwardExchange ℓ
        (hN.preservesBoundedConstructible (ℓ := ℓ))
        (hM.preservesBoundedConstructible (ℓ := ℓ))).app K ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
        ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).obj K) ≫
      ν.app K =
        (boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app K))
    (L : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (φ.boundedConstructiblePushforwardExchange ℓ (hN.preservesBoundedConstructible (ℓ := ℓ))
        (hM.preservesBoundedConstructible (ℓ := ℓ))).app
        ((boundedConstructibleUpperShriek ℓ i₁).obj L) ≫
      (boundedConstructibleLowerStar ℓ i₂).map ((exceptionalExchange ℓ i₁ i₂ ν).app L) ≫
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
          ((boundedConstructibleUpperShriek ℓ i₂).obj
            ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj
              L)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ i₂).counit.app
          ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj L) =
      (boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).map
        ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app
            ((boundedConstructibleUpperShriek ℓ i₁).obj L) ≫
          (boundedConstructibleUpperShriekAdjunction ℓ i₁).counit.app L) :=
  app_comp_map_mateEquiv_app_comp_inv_app_comp_counit_app
    (boundedConstructibleUpperShriekAdjunction ℓ i₁)
    (boundedConstructibleUpperShriekAdjunction ℓ i₂) ν
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂) _ hν L

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
