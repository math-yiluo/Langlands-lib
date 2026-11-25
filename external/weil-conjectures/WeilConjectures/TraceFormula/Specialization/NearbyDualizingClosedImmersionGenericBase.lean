/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingClosedImmersionInputs

/-!

# The closed-immersion law of the dualizing maps over a generic base

For a morphism `φ : N ⟶ M` of proper trait models with full geometric generic fibres over a
generic base, over proper `i₁ : Y₁ ⟶ X₁` and `i₂ : Y' ⟶ X'`, and a compact-support exchange `ν`
inverting the proper exchange `χ_φ` under `Ri_! ≅ Ri_*`, the dualizing maps satisfy the
closed-immersion law `θ_N ∘ Ψ_N(ρ) = ρ' ∘ Ri₂^!(θ_M) ∘ β_φ(ω_{X₁})` (blueprint
`sec-Base-change-for-nearby-cycles` (4);
`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.closedImmersion_law`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

namespace NearbyDualizingDataOfGenericBase

variable {k' : Type u} [Field k'] {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The closed-immersion law of the dualizing maps over a generic base** (blueprint
`sec-Base-change-for-nearby-cycles` (4)): for a morphism `φ : N ⟶ M` of proper trait models with
full geometric generic fibres over proper `i₁ : Y₁ ⟶ X₁` and `i₂ : Y' ⟶ X'`, and a
compact-support exchange `ν` inverting the proper exchange `χ_φ` under `Ri_! ≅ Ri_*`,
`θ_N ∘ Ψ_N(ρ) = ρ' ∘ Ri₂^!(θ_M) ∘ β_φ(ω_{X₁})` for the exceptional exchange `β_φ` of `ν` and the
composition isomorphisms `ρ : Ri₁^! ω_{X₁} ≅ ω_{Y₁}`, `ρ' : Ri₂^! ω_{X'} ≅ ω_{Y'}`. Both sides
are determined by their traces after the invertible proper exchange `χ_{a_N}`, which are compared
by `CategoryTheory.closedImmersionLaw_aux`. -/
theorem closedImmersion_law (D : NearbyDualizingDataOfGenericBase k' ℓ)
    {F : Type u} [Field F] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
    {X₁ Y₁ : Over (Spec (.of F))} [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom]
    [IsSeparated X₁.hom] [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
    {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
    {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [IsProper (CondensedRing.toPoint X₁).left] [IsProper (CondensedRing.toPoint Y₁).left]
    [IsProper (CondensedRing.toPoint X').left] [IsProper (CondensedRing.toPoint Y').left]
    {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
    {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
    {N : NearbyCyclesModel Y₁.left Y'.left} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
    (hM : M.IsTraitModelOfGenericBase X₁ ι q g) (hN : N.IsTraitModelOfGenericBase Y₁ ι qN gN)
    [IsProper q] [IsProper qN]
    (hMgen : IsPullback M.ε g X₁.hom (traitGenericPointToSpec k' ≫ ι))
    (hNgen : IsPullback N.ε gN Y₁.hom (traitGenericPointToSpec k' ≫ ι))
    (i₁ : Y₁ ⟶ X₁) [IsProper i₁.left] (i₂ : Y' ⟶ X') [IsProper i₂.left]
    (φ : N.Hom M i₁.left i₂.left) (hq : qN = φ.total ≫ q) (hg : gN = φ.generic ≫ g)
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
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app K)) :
    (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).map
        (upperShriekDualizingComplexIso ℓ i₁).hom ≫ D.θ hN =
      (exceptionalExchange ℓ i₁ i₂ ν).app (dualizingComplex ℓ X₁) ≫
        (boundedConstructibleUpperShriek ℓ i₂).map (D.θ hM) ≫
        (upperShriekDualizingComplexIso ℓ i₂).hom := by
  have : IsIso ((hN.pushforwardExchange ℓ _ hNgen.w.symm).app
      ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁))) :=
    hN.isIso_pushforwardExchange_app ℓ _ hNgen.w.symm hNgen _
  refine eq_of_map_comp_trace_eq ℓ Y' ?_
  rw [← cancel_epi ((hN.pushforwardExchange ℓ _ hNgen.w.symm).app
      ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))]
  exact closedImmersionLaw_aux
    (traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ)
    (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint Y'))
    (boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X'))
    ((hN.pushforwardExchange ℓ _ hNgen.w.symm).app
      ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))
    ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).map
      (upperShriekDualizingComplexIso ℓ i₁).hom)
    (D.θ hN) (trace ℓ Y')
    ((exceptionalExchange ℓ i₁ i₂ ν).app (dualizingComplex ℓ X₁))
    ((boundedConstructibleUpperShriek ℓ i₂).map (D.θ hM))
    (upperShriekDualizingComplexIso ℓ i₂).hom
    ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint Y₁)).map
      (upperShriekDualizingComplexIso ℓ i₁).hom)
    ((hN.pushforwardExchange ℓ _ hNgen.w.symm).app (dualizingComplex ℓ Y₁))
    (trace ℓ Y₁)
    (inv (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ))
    ((boundedConstructibleLowerStarCompOfEq ℓ i₁ (CondensedRing.toPoint X₁)
      (comp_toPoint i₁)).inv.app
        ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))
    ((boundedConstructibleLowerStar ℓ (CondensedRing.toPoint X₁)).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app
          ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ i₁).counit.app (dualizingComplex ℓ X₁)))
    (trace ℓ X₁)
    ((boundedConstructibleLowerStarCompOfEq ℓ i₂ (CondensedRing.toPoint X')
      (comp_toPoint i₂)).inv.app
        ((boundedConstructibleUpperShriek ℓ i₂).obj (dualizingComplex ℓ X')))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
          ((boundedConstructibleUpperShriek ℓ i₂).obj (dualizingComplex ℓ X')) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ i₂).counit.app (dualizingComplex ℓ X'))
    (trace ℓ X')
    ((boundedConstructibleLowerStarCompOfEq ℓ i₂ (CondensedRing.toPoint X')
      (comp_toPoint i₂)).inv.app
        ((boundedConstructibleUpperShriek ℓ i₂).obj
          ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj
            (dualizingComplex ℓ X₁))))
    ((boundedConstructibleLowerStar ℓ i₂).map
      ((boundedConstructibleUpperShriek ℓ i₂).map (D.θ hM)))
    ((boundedConstructibleLowerStarCompOfEq ℓ i₂ (CondensedRing.toPoint X')
      (comp_toPoint i₂)).inv.app
        ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).obj
          ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁))))
    ((boundedConstructibleLowerStar ℓ i₂).map
      ((exceptionalExchange ℓ i₁ i₂ ν).app (dualizingComplex ℓ X₁)))
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₂).inv.app
          ((boundedConstructibleUpperShriek ℓ i₂).obj
            ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj
              (dualizingComplex ℓ X₁))) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ i₂).counit.app
          ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj
            (dualizingComplex ℓ X₁)))
    (D.θ hM)
    ((φ.boundedConstructiblePushforwardExchange ℓ
        (hN.preservesBoundedConstructible (ℓ := ℓ))
        (hM.preservesBoundedConstructible (ℓ := ℓ))).app
      ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))
    ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).map
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app
          ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ i₁).counit.app (dualizingComplex ℓ X₁)))
    ((hM.pushforwardExchange ℓ _ hMgen.w.symm).app
      ((boundedConstructibleLowerStar ℓ i₁).obj
        ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁))))
    ((hM.pushforwardExchange ℓ _ hMgen.w.symm).app (dualizingComplex ℓ X₁))
    ((hN.pushforwardExchange ℓ _ hNgen.w.symm).naturality
      (upperShriekDualizingComplexIso ℓ i₁).hom).symm
    (D.pushforwardExchange_comp_map_θ_comp_trace hN hNgen _ hNgen.w.symm)
    (lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace ℓ i₁)
    (lowerStar_map_upperShriekDualizingComplexIso_hom_comp_trace ℓ i₂)
    ((boundedConstructibleLowerStarCompOfEq ℓ i₂ (CondensedRing.toPoint X')
      (comp_toPoint i₂)).inv.naturality ((boundedConstructibleUpperShriek ℓ i₂).map (D.θ hM)))
    ((boundedConstructibleLowerStarCompOfEq ℓ i₂ (CondensedRing.toPoint X')
      (comp_toPoint i₂)).inv.naturality
      -- explicit objects: comparing `inv.app ((F ⋙ G).obj _)` with `inv.app (G.obj (F.obj _))`
      -- makes the kernel unfold the composition isomorphism and time out
      (X := (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).obj
        ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))
      (Y := (boundedConstructibleUpperShriek ℓ i₂).obj
        ((boundedConstructibleNearbyCycles (hM.preservesBoundedConstructible (ℓ := ℓ))).obj
          (dualizingComplex ℓ X₁)))
      ((exceptionalExchange ℓ i₁ i₂ ν).app (dualizingComplex ℓ X₁)))
    (lowerStar_map_upperShriek_map_comp_counit ℓ i₂ (D.θ hM))
    (Hom.pushforwardExchange_app_comp_lowerStar_map_exceptionalExchange_app ℓ hM hN i₁ i₂ φ ν hν
      (dualizingComplex ℓ X₁))
    (IsTraitModelOfGenericBase.pushforwardExchange_app_comp_lowerStarCompOfEq ℓ hM hN _
      hMgen.w.symm hNgen.w.symm i₁ i₂ φ hq hg
      ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))
    (IsTraitModelOfGenericBase.pushforwardExchange_naturality_symm ℓ hM _ hMgen.w.symm
      (K := (boundedConstructibleLowerStar ℓ i₁).obj
        ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)))
      (L := dualizingComplex ℓ X₁)
      ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i₁).inv.app
          ((boundedConstructibleUpperShriek ℓ i₁).obj (dualizingComplex ℓ X₁)) ≫
        (boundedConstructibleUpperShriekAdjunction ℓ i₁).counit.app (dualizingComplex ℓ X₁)))
    (D.pushforwardExchange_comp_map_θ_comp_trace hM hMgen _ hMgen.w.symm)

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
