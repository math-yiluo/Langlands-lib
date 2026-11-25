/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingConstruction
public import WeilConjectures.TraceFormula.Specialization.NearbyOpenExchange

/-!

# The dualizing maps of nearby cycles and open restriction

For an open sub-model `N ⊆ M` of trait models over the base, over open immersions `j`, `j'`, the
dualizing maps satisfy `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`
(`NearbyCyclesModel.IsTraitModelOfBase.map_dualizingMap_comp_dualizingComplexUpperStarIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

namespace IsTraitModelOfBase

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The dualizing maps are compatible with open restriction**: for an open sub-model `N ⊆ M`
over open immersions `j`, `j'`, `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`. -/
theorem map_dualizingMap_comp_dualizingComplexUpperStarIso {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (hM : M.IsTraitModelOfBase k qM gM) (hN : N.IsTraitModelOfBase k q g)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X') [IsOpenImmersion j'.left]
    (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (hM.dualizingMap ℓ) ≫ (dualizingComplexUpperStarIso ℓ j').hom =
      (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible ℓ)
          (hM.preservesBoundedConstructible ℓ)).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible ℓ)).map
          (dualizingComplexUpperStarIso ℓ j).hom ≫ hN.dualizingMap ℓ := by
  obtain ⟨C⟩ := hM.nonempty_compactification
  have := φ.isIso_pullbackExchange_of_isOpenImmersion (Profinite.padicAlgClRingObj ℓ) hφ
  refine map_comp_eq_of_exceptionalExchange
    (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible ℓ)
      (hM.preservesBoundedConstructible ℓ))
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j')
    (exceptionalExchange ℓ j j' (φ.boundedConstructibleLowerShriekExchange ℓ
      (hN.preservesBoundedConstructible ℓ) (hM.preservesBoundedConstructible ℓ)))
    (fun b ↦ by
      cast_proofs φ.exceptionalExchange_boundedConstructibleLowerShriekExchange_app ℓ
        (hN.preservesBoundedConstructible ℓ) (hM.preservesBoundedConstructible ℓ) b)
    (hM.dualizingMap ℓ) (hN.dualizingMap ℓ) (dualizingComplexComp ℓ j)
    (dualizingComplexComp ℓ j') ?_ (dualizingComplexUpperStarIso ℓ j)
    (by cast_proofs dualizingComplexUpperStarIso_hom_eq ℓ j) (dualizingComplexUpperStarIso ℓ j')
    (by cast_proofs dualizingComplexUpperStarIso_hom_eq ℓ j')
  rw [dualizingMap, dualizingMap,
    hN.compactSupportExchange_eq_compactSupportExchange ℓ (C.ofOpen hN j j' φ hφ hq hg),
    hM.compactSupportExchange_eq_compactSupportExchange ℓ C]
  have h := dualizingExchange_eq_comp_dualizingComplex ℓ (traitSpecializationUnit k k' (ℓ := ℓ))
    j j'
    (φ.boundedConstructibleLowerShriekExchange ℓ (hN.preservesBoundedConstructible ℓ)
      (hM.preservesBoundedConstructible ℓ)) (C.compactSupportExchange ℓ)
    ((C.ofOpen hN j j' φ hφ hq hg).compactSupportExchange ℓ) (fun K ↦ by
      cast_proofs Compactification.compactSupportExchange_ofOpen_app ℓ C hN j j' φ hφ hq hg K)
  cast_proofs h

end IsTraitModelOfBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
