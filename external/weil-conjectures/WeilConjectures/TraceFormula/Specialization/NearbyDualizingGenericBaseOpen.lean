/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingGenericBaseConstruction
public import WeilConjectures.TraceFormula.Specialization.NearbyOpenExchange

/-!

# The dualizing maps of nearby cycles over a generic base and open restriction

A compactification `M ⊆ P` of a trait model over a generic base restricts to a compactification
`N ⊆ P` of an open sub-model `N ⊆ M`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.ofOpen`), along which the
compact-support exchange of `N` is the composite of the exchange `ν_j = (α_j⁻¹)♯` and that of `M`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.Compactification.compactSupportExchange_ofOpen_app`,
an instance of `ProEtale.CondensedRing.compactSupportExchangeOfCompactification_comp_app`). By the
composition law of the dualizing maps (`ProEtale.CondensedRing.dualizingExchange_eq_comp`), the
dualizing maps satisfy `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.map_dualizingMap_comp_dualizingComplexUpperStarIso`),
as over a base field
(`NearbyCyclesModel.IsTraitModelOfBase.map_dualizingMap_comp_dualizingComplexUpperStarIso`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfGenericBase

open Scheme

section OfOpen

variable {F : Type u} [Field F] {k' : Type u} [Field k']
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {Y : Over (Spec (.of F))} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {X : Over (Spec (.of F))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {hM : M.IsTraitModelOfGenericBase X ι qM gM}

/-- **A compactification of a model over a generic base restricts to its open sub-models**: for
an open sub-model `N ⊆ M` over open immersions `j`, `j'` and a compactification `M ⊆ P` over
`ιX`, `ιX'`, the compactification `N ⊆ P` over `j ≫ ιX`, `j' ≫ ιX'`. -/
noncomputable def Compactification.ofOpen (C : hM.Compactification)
    (hN : N.IsTraitModelOfGenericBase Y ι q g) (j : Y ⟶ X) [IsOpenImmersion j.left]
    (j' : Y' ⟶ X') [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left)
    [IsOpenImmersion φ.total] (hφ : IsPullback φ.generic N.j M.j φ.total)
    (hq : q = φ.total ≫ qM) (hg : g = φ.generic ≫ gM) : hN.Compactification where
  X := C.X
  X' := C.X'
  model := C.model
  qc := C.qc
  gc := C.gc
  isTraitModelOfGenericBase := C.isTraitModelOfGenericBase
  isPullback_ε := C.isPullback_ε
  exists_isIso_genericFibre := C.exists_isIso_genericFibre
  ιX := j ≫ C.ιX
  ιX' := j' ≫ C.ιX'
  isOpenImmersion_ιX := by
    rw [Over.comp_left]
    infer_instance
  isOpenImmersion_ιX' := by
    rw [Over.comp_left]
    infer_instance
  hom := φ.comp C.hom
  isOpenImmersion_hom_total := by
    rw [NearbyCyclesModel.Hom.comp_total]
    infer_instance
  isPullback_hom_j := hφ.paste_horiz C.isPullback_hom_j
  q_eq := by rw [hq, NearbyCyclesModel.Hom.comp_total, Category.assoc, ← C.q_eq]
  g_eq := by rw [hg, NearbyCyclesModel.Hom.comp_generic, Category.assoc, ← C.g_eq]

end OfOpen

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {Y : Over (Spec (.of F))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {hM : M.IsTraitModelOfGenericBase X ι qM gM}

/-- **The compact-support exchanges along an open sub-model** (blueprint
`prose-E-15`, `lemma-compatibilities-base-change-maps` (3)): for an open sub-model `N ⊆ M`
of trait models over a generic base, over open immersions `j`, `j'`, and a compactification
`M ⊆ P`, the compact-support exchange of the restricted compactification `N ⊆ P` is the composite
of the exchange `ν_j` (adjoint to `α_j⁻¹`) and of the compact-support exchange of `M ⊆ P`,
through the composition isomorphisms `Ra_N! ≅ Rj_! ⋙ Ra_M!` and `Ra'_N! ≅ Rj'_! ⋙ Ra'_M!`.

An instance of `ProEtale.CondensedRing.compactSupportExchangeOfCompactification_comp_app` at the
morphisms of models `φ : N ⟶ M` and `C.hom : M ⟶ P`. -/
theorem Compactification.compactSupportExchange_ofOpen_app (C : hM.Compactification)
    (hN : N.IsTraitModelOfGenericBase Y ι q g) (j : Y ⟶ X) [IsOpenImmersion j.left]
    (j' : Y' ⟶ X') [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left)
    [IsOpenImmersion φ.total] (hφ : IsPullback φ.generic N.j M.j φ.total)
    (hq : q = φ.total ≫ qM) (hg : g = φ.generic ≫ gM)
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((C.ofOpen hN j j' φ hφ hq hg).compactSupportExchange ℓ).app K ≫
        (traitPointSpecialization (traitGenericPointToSpec k' ≫ ι) ℓ).map
          ((lowerShriekCompOfEq ℓ j (CondensedRing.toPoint X) (comp_toPoint j)).hom.app K) =
      (lowerShriekCompOfEq ℓ j' (CondensedRing.toPoint X') (comp_toPoint j')).hom.app
          ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (CondensedRing.toPoint X')).map
          ((φ.boundedConstructibleLowerShriekExchange ℓ (hN.preservesBoundedConstructible (ℓ := ℓ))
            (hM.preservesBoundedConstructible (ℓ := ℓ))).app K) ≫
        (C.compactSupportExchange ℓ).app ((boundedConstructibleLowerShriek ℓ j).obj K) := by
  have : IsOpenImmersion (j ≫ C.ιX).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsOpenImmersion (j' ≫ C.ιX').left := by
    rw [Over.comp_left]
    infer_instance
  have : IsIso ((φ.comp C.hom).pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    inferInstanceAs (IsIso ((C.ofOpen hN j j' φ hφ hq hg).hom.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)))
  cast_proofs compactSupportExchangeOfCompactification_comp_app ℓ φ C.hom
    (hN.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ))
    (preservesBoundedConstructible_traitModelOfPoint _ ℓ)
    (C.isTraitModelOfGenericBase.toPoint _ C.isPullback_ε.w.symm)
    (C.isIsoOn_pushforwardExchange ℓ) K

/-- **The dualizing maps over a generic base are compatible with open restriction**: for an open
sub-model `N ⊆ M` over open immersions `j`, `j'`, `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`. -/
theorem map_dualizingMap_comp_dualizingComplexUpperStarIso
    (hM : M.IsTraitModelOfGenericBase X ι qM gM) (hN : N.IsTraitModelOfGenericBase Y ι q g)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X') [IsOpenImmersion j'.left]
    (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (hM.dualizingMap ℓ) ≫ (dualizingComplexUpperStarIso ℓ j').hom =
      (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible (ℓ := ℓ))
          (hM.preservesBoundedConstructible (ℓ := ℓ))).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible (ℓ := ℓ))).map
          (dualizingComplexUpperStarIso ℓ j).hom ≫ hN.dualizingMap ℓ := by
  obtain ⟨C⟩ := hM.nonempty_compactification
  have := φ.isIso_pullbackExchange_of_isOpenImmersion (Profinite.padicAlgClRingObj ℓ) hφ
  refine map_comp_eq_of_exceptionalExchange
    (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible (ℓ := ℓ))
      (hM.preservesBoundedConstructible (ℓ := ℓ)))
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)
    (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j')
    (exceptionalExchange ℓ j j' (φ.boundedConstructibleLowerShriekExchange ℓ
      (hN.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ))))
    (fun b ↦ by
      cast_proofs φ.exceptionalExchange_boundedConstructibleLowerShriekExchange_app ℓ
        (hN.preservesBoundedConstructible (ℓ := ℓ)) (hM.preservesBoundedConstructible (ℓ := ℓ)) b)
    (hM.dualizingMap ℓ) (hN.dualizingMap ℓ) (dualizingComplexComp ℓ j)
    (dualizingComplexComp ℓ j') ?_ (dualizingComplexUpperStarIso ℓ j)
    (by cast_proofs dualizingComplexUpperStarIso_hom_eq ℓ j) (dualizingComplexUpperStarIso ℓ j')
    (by cast_proofs dualizingComplexUpperStarIso_hom_eq ℓ j')
  rw [dualizingMap, dualizingMap,
    hN.compactSupportExchange_eq_compactSupportExchange ℓ (C.ofOpen hN j j' φ hφ hq hg),
    hM.compactSupportExchange_eq_compactSupportExchange ℓ C]
  have h := dualizingExchange_eq_comp_dualizingComplex ℓ
    (traitPointSpecializationUnit (traitGenericPointToSpec k' ≫ ι) ℓ) j j'
    (φ.boundedConstructibleLowerShriekExchange ℓ (hN.preservesBoundedConstructible (ℓ := ℓ))
      (hM.preservesBoundedConstructible (ℓ := ℓ))) (C.compactSupportExchange ℓ)
    ((C.ofOpen hN j j' φ hφ hq hg).compactSupportExchange ℓ) (fun K ↦ by
      cast_proofs Compactification.compactSupportExchange_ofOpen_app ℓ C hN j j' φ hφ hq hg K)
  cast_proofs h

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfGenericBase
