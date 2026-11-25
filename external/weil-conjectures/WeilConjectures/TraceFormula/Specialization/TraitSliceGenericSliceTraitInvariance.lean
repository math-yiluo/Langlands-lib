/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGenericSliceTraitGalois
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitCompositumClosed
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisDegree
public import WeilConjectures.TraceFormula.Specialization.SliceTraitGaloisLayer
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMapInvariants
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitResidueCoeffs
public import WeilConjectures.Tactic.TransportExact
public import WeilConjectures.Tactic.ExactModProofs
public meta import Lean.LibrarySuggestions.Basic

/-!

# The change of trait `T ⟶ S'` of the Galois-layer models, torsion coefficients

In the situation of
`WeilConjectures.TraceFormula.Specialization.TraitSliceGenericSliceTraitGalois`, let `D` be a
generic slice trait with residue coefficients
(`AlgebraicGeometry.GenericSliceTrait.HasResidueCoeffs`,
which exists by `AlgebraicGeometry.exists_genericSliceTrait_hasResidueCoeffs`) and `k'` separably
closed of characteristic `p > 0`. With coefficients a finite ring `T₀` in which `p` is invertible,
the pullback exchange of the change of trait `τ_N : N₂ ⟶ N₁` of the Galois-layer models of the
slices over `T` and `S'` is invertible at every complex of étale origin on the geometric generic
fibre of `M` (`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGaloisChangeHom_finite`).

This is
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic`
(SGA 4½, [Th. finitude], proof of 3.7, 3.8): the change of Galois layers is invertible by the
invariance of nearby cycles under the change of trait `T ⟶ S'`
(`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGaloisLayerMap`), the extensions
`L'^sep / L'` and `L_T^sep / L_T` are pro-`p` (`AlgebraicGeometry.SliceTrait.exists_finrank_eq_pow`,
`AlgebraicGeometry.isUnit_finrank_traitTensorCompositum`), and `L'` is relatively separably closed
in `L_T` (`AlgebraicGeometry.GenericSliceTrait.compositumSepMap_mem_range_algebraMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

/-- The inclusion of the geometric generic fibre of a model over the trait is affine. -/
lemma IsTraitModelOver.isAffineHom_j (hM : M.IsTraitModelOver q g) : IsAffineHom M.j :=
  MorphismProperty.of_isPullback hM.isPullback_j.flip
    (inferInstanceAs (IsAffineHom (Spec.map _)))

/-- The open immersion of generic fibres of the Galois-layer model `N₁` over `S'` is affine. -/
lemma isAffineHom_genericSliceTraitGaloisModel_j :
    IsAffineHom (genericSliceTraitGaloisModel hM b hb D).j := by
  have := hM.isAffineHom_j
  have h₂ : IsAffineHom (genericSliceTraitGenericHom hM b hb D).cartesianModel.j :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h₁ : IsAffineHom ((genericSliceTraitGenericHom hM b hb D).traitChangeThickening
      D.toSliceTrait.Ω (sliceTraitStructure D.toSliceTrait M b) q g hM.isPullback_j.w
      (sliceTrait_fst_comp D.toSliceTrait M b hb)) :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsAffineHom (Spec.map _)))
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂

/-- The open immersion of generic fibres of the Galois-layer model `N₂` over `T` is affine. -/
lemma isAffineHom_traitSliceGaloisModel_j : IsAffineHom (traitSliceGaloisModel hM b hb).j := by
  have := hM.isAffineHom_j
  have h₂ : IsAffineHom (traitSliceGenericHom hM b hb).cartesianModel.j :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h₁ : IsAffineHom ((traitSliceGenericHom hM b hb).traitChangeThickening
      (traitGenericField (traitSliceField k'))
      (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q g
      hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))) :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsAffineHom (Spec.map _)))
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂
variable [IsSepClosed k'] [Fact (ringChar k').Prime]

/-- **The change of trait `τ_N : N₂ ⟶ N₁` of the Galois-layer models, torsion coefficients**: for a
generic slice trait with residue coefficients and a finite ring `T₀` in which the characteristic
`p` of `k'` is invertible, the pullback exchange of `τ_N` is invertible at every complex on the
geometric generic fibre of `M` which is bounded below of étale origin. -/
theorem isIso_pullbackExchange_traitSliceGaloisChangeHom_finite (hD : D.HasResidueCoeffs)
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] (hpT : IsUnit ((ringChar k' : ℕ) : T₀))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) M.generic)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic T₀).functor.obj C)) :
    IsIso (((traitSliceGaloisChangeHom hM b hb D).pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app C) := by
  have hp : (ringChar k').Prime := Fact.out
  have := isAffineHom_genericSliceTraitGaloisModel_j hM b hb D
  have := isAffineHom_traitSliceGaloisModel_j hM b hb
  have : FaithfulSMul D.toSliceTrait.R D.toSliceTrait.Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  have : Algebra.IsAlgebraic D.toSliceTrait.R D.toSliceTrait.Ω := D.isAlgebraic_a
  have hres (n : ℕ) (hn : (n : ResidueField (PowerSeries k')) = 0) : ringChar k' ∣ n :=
    ringChar.dvd ((PowerSeries.residueFieldEquiv k').injective (by rw [map_natCast, hn, map_zero]))
  have hdeg := D.toSliceTrait.exists_finrank_eq_pow hres
  have hp₁ (L' : FiniteGaloisIntermediateField D.toSliceTrait.compositum
      D.toSliceTrait.compositumSep) :
      IsUnit ((Module.finrank D.toSliceTrait.compositum L' : ℕ) : T₀) := by
    obtain ⟨k, hk⟩ := hdeg L'
    rw [hk, Nat.cast_pow]
    exact hpT.pow k
  have hC₁ := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ (genericSliceTraitGaloisModel hM b hb D).ε hC
  have hC₂ := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ (traitSliceGaloisModel hM b hb).ε
      (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀
        (𝟙 M.generic) hC)
  have hK := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ (sliceTraitGeneric D.toSliceTrait M b hb hM.isPullback_j_algebraMap)
      (ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T₀
        (𝟙 M.generic) hC)
  have hIH := isIso_pullbackExchange_traitSliceGenericSliceTraitHom_finite hM b hb D T₀ hpT _ hK
  have hτ' := isIso_pullbackExchange_traitSliceGaloisLayerMap hM b hb D
    (Profinite.continuousMapRingObj T₀)
    (L((𝟙 M.generic)^*⟦Profinite.continuousMapRingObj T₀⟧).obj C) (by transport_exact hIH)
  have key := Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic
    (l := D.compositumMap) (ω := D.compositumSepMap) (hω := D.compositumSepMap_comp_algebraMap) T₀
    (traitSliceGaloisChangeHom hM b hb D) (traitSliceGaloisChangeHom_generic_comp_residue hM b hb D)
    hp₁ (isUnit_finrank_traitTensorCompositum hp (fun n hn ↦ ringChar.dvd hn) hpT)
    (D.compositumSepMap_mem_range_algebraMap hD) C (by transport_exact hC₁)
    (by transport_exact hC₂) (hiso := by transport_exact hτ')
  transport_exact key
/-- The restricted base change morphism `Li^* (Lt^* Rj_* ⟶ Rj'_* Lg^*)` of a square only depends on
its horizontal maps: it is transported along equalities of these. -/
lemma isIso_map_exchangeRight_of_eq (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {W X₀ Y₀ Z₀ Z' : Scheme.{u}} {i : Z' ⟶ X₀}
    {top top' : W ⟶ Y₀} {l : W ⟶ X₀} {r : Y₀ ⟶ Z₀} {bot bot' : X₀ ⟶ Z₀} (htop : top = top')
    (hbot : bot = bot') (sq : CommSq top l r bot) (sq' : CommSq top' l r bot')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y₀) Ab.{u + 1})
      (condensedRingObj Λ Y₀)))
    (h : IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ r) (derivedUpperStarLowerStarAdjunction Λ l)
      (pullbackSquareComparison Λ sq)).app K))) :
    IsIso ((L((i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ r) (derivedUpperStarLowerStarAdjunction Λ l)
      (pullbackSquareComparison Λ sq')).app K)) := by
  subst htop hbot
  exact_mod_proofs h

/-- The cartesian part `χ : N'' ⟶ M` of the slice over `T`: the nilpotent thickening of generic
fibres of the Galois-layer model `N''` followed by the cartesian model of the slice. -/
noncomputable abbrev traitSliceGaloisModelHom :=
  ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).traitChangeModelHom
    (traitGenericField (traitSliceField k'))
    (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q g
    hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))).comp
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).fromCartesian

/-- **"M1 at `T`", torsion coefficients**: the restricted base change morphism of the square of
generic fibres of `χ : N'' ⟶ M` is invertible at every complex of étale origin, with coefficients
a finite ring in which `p` is invertible. It is the composite of `τ_N : N₂ ⟶ N₁`
(`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGaloisChangeHom_finite`) and the cartesian
part `N₁ ⟶ M` over `S'` (`NearbyCyclesModel.isIso_pullbackExchange_sliceTraitGaloisModelHom`),
which have the same maps of total spaces and of generic fibres. -/
theorem isIso_map_exchangeRight_traitSliceGaloisModelHom_finite (hD : D.HasResidueCoeffs)
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] (hpT : IsUnit ((ringChar k' : ℕ) : T₀))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) M.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) M.generic
      ((finiteCoefficientDerivedEquivalence M.generic T₀).functor.obj K)) :
    IsIso ((L(((baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _)).i)^*⟦Profinite.continuousMapRingObj T₀⟧)).map
      ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀) M.j)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
        (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).j)
      (pullbackSquareComparison (Profinite.continuousMapRingObj T₀)
        (traitSliceGaloisModelHom hM b hb).commSq_j)).app K)) := by
  have heq : (algebraMap (PowerSeries k') (traitGenericField k')).toAlgebra =
      (inferInstance : Algebra (PowerSeries k') (traitGenericField k')) :=
    Algebra.algebra_ext _ _ fun _ ↦ rfl
  have hsub := D.toSliceTrait.subsingleton_primeSpectrum (algebraMap_traitGenericField_injective k')
    (isAlgebraic_traitGenericField k')
  rw [heq] at hsub
  have hψ := isIso_pullbackExchange_sliceTraitGaloisModelHom D.toSliceTrait M b hb
    hM.isPullback_j_algebraMap hM.isPullback_i_constantCoeff (Profinite.continuousMapRingObj T₀) K
  have hK' := ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj
    T₀ (𝟙 M.generic ≫ 𝟙 M.generic) hK
  have hτ := isIso_pullbackExchange_traitSliceGaloisChangeHom_finite hM b hb D hD T₀ hpT _ hK'
  have h₁ := Hom.isIso_pullbackExchange_app_comp (Profinite.continuousMapRingObj T₀)
    (traitSliceGaloisChangeHom hM b hb D)
    (sliceTraitGaloisModelHom D.toSliceTrait M b hb hM.isPullback_j_algebraMap
      hM.isPullback_i_constantCoeff) K (by transport_exact hψ) (by transport_exact hτ)
  have h₂ := Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_app
    (Profinite.continuousMapRingObj T₀) _ K h₁
  have htop : ((traitSliceGaloisChangeHom hM b hb D).comp
      (sliceTraitGaloisModelHom D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff)).generic = (traitSliceGaloisModelHom hM b hb).generic :=
    (traitSliceGaloisGenericMap_fst_assoc hM b hb D _).trans
      (pullback.fst _ _ ≫= traitSliceCartesianGenericMap_fst hM b hb D)
  have hbot : ((traitSliceGaloisChangeHom hM b hb D).comp
      (sliceTraitGaloisModelHom D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff)).total = (traitSliceGaloisModelHom hM b hb).total :=
    (traitSliceGenericSliceTraitTotal b D ≫= Category.id_comp _).trans
      ((traitSliceGenericSliceTraitTotal_fst b D).trans (Category.id_comp _).symm)
  have hsq : CommSq ((traitSliceGaloisChangeHom hM b hb D).comp
      (sliceTraitGaloisModelHom D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff)).generic
      (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).j M.j
      ((traitSliceGaloisChangeHom hM b hb D).comp
      (sliceTraitGaloisModelHom D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff)).total := by
    rw [htop, hbot]
    exact (traitSliceGaloisModelHom hM b hb).commSq_j
  have h₄ : IsIso ((L(((baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _)).i)^*⟦Profinite.continuousMapRingObj T₀⟧)).map
      ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀) M.j)
      (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
        (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).j)
      (pullbackSquareComparison (Profinite.continuousMapRingObj T₀) hsq)).app K)) := by
    refine NatTrans.isIso_map_app_of_iso _ _
      ((leftDerivedUpperStarId (Profinite.continuousMapRingObj T₀) M.generic).app K) ?_
    transport_exact h₂
  have h₅ := isIso_map_exchangeRight_of_eq (Profinite.continuousMapRingObj T₀)
    (i := (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).i)
    htop hbot hsq
    (traitSliceGaloisModelHom hM b hb).commSq_j K (by transport_exact h₄)
  transport_exact h₅
omit [IsSepClosed k'] [Fact (ringChar k').Prime] in
/-- The open immersion of generic fibres of the Galois-layer model `N''` of the slice over `T` is
affine. -/
lemma isAffineHom_baseChangeGaloisModel_j :
    IsAffineHom (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over _)).j := by
  have := hM.isAffineHom_j
  have h₂ : IsAffineHom
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _)).cartesianModel.j :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h₁ : IsAffineHom ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over _)).traitChangeThickening (traitGenericField (traitSliceField k'))
      (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q g
      hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))) :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsAffineHom (Spec.map _)))
  exact MorphismProperty.comp_mem _ _ _ h₁ h₂

/-- **"M1 at `T`"** (SGA 4½, [Th. finitude], 3.4 and 3.7): with `ℚ̄_ℓ`-coefficients, `ℓ` different
from the characteristic `p` of the separably closed field `k'`, the pullback exchange of the
cartesian part `χ : N'' ⟶ M` of the slice of `M` over `T = Spec K⟦t⟧` is invertible at every
complex `C` whose restriction `Lε^* C` to the geometric generic fibre is bounded constructible.

With torsion coefficients this is
`NearbyCyclesModel.isIso_map_exchangeRight_traitSliceGaloisModelHom_finite`, through a generic
slice trait with residue coefficients; it passes to `ℚ̄_ℓ` by the integral-model criterion
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral`) and derived Nakayama
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`), as in
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`. -/
theorem isIso_pullbackExchange_traitSliceGaloisModelHom {ℓ : ℕ} [Fact ℓ.Prime]
    [Fact (ringChar k' ≠ ℓ)]
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj C)) :
    IsIso (((traitSliceGaloisModelHom hM b hb).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app C) := by
  obtain ⟨D, hD⟩ := exists_genericSliceTrait_hasResidueCoeffs k'
  have hp : (ringChar k').Prime := Fact.out
  have hpℓ : ringChar k' ≠ ℓ := Fact.out
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have : QuasiCompact g := MorphismProperty.of_isPullback hM.isPullback_j ‹_›
  have : QuasiSeparated g := MorphismProperty.of_isPullback hM.isPullback_j inferInstance
  have : LocallyOfFiniteType g := MorphismProperty.of_isPullback hM.isPullback_j ‹_›
  have := QuasiCompact.compactSpace_of_compactSpace g
  have := quasiSeparatedSpace_of_quasiSeparated g
  have : IsNoetherian M.generic := isNoetherian_of_locallyOfFiniteType g
  have := hM.isAffineHom_j
  have := isAffineHom_baseChangeGaloisModel_j hM b hb
  have := QuasiCompact.compactSpace_of_compactSpace q
  have := quasiSeparatedSpace_of_quasiSeparated q
  have : QuasiCompact b := by
    subst hb
    exact QuasiCompact.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : QuasiSeparated b := by
    subst hb
    exact QuasiSeparated.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : QuasiCompact (pullback.snd b (traitSlice (traitSliceCoord k'))) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiSeparated (pullback.snd b (traitSlice (traitSliceCoord k'))) :=
    MorphismProperty.pullback_snd _ _ ‹_›
  have := QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd b (traitSlice (traitSliceCoord k')))
  have := quasiSeparatedSpace_of_quasiSeparated (pullback.snd b (traitSlice (traitSliceCoord k')))
  have hc : CompactSpace
      (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).total :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd b (traitSlice (traitSliceCoord k')))
  have hqs : QuasiSeparatedSpace
      (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).total :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd b (traitSlice (traitSliceCoord k')))
  have := QuasiCompact.compactSpace_of_compactSpace
    (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).j
  have := quasiSeparatedSpace_of_quasiSeparated
    (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).j
  have : IsAffineHom
      (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).i :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsAffineHom (Spec.map _)))
  have := QuasiCompact.compactSpace_of_compactSpace
    (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).i
  have := quasiSeparatedSpace_of_quasiSeparated
    (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).i
  have hint (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) M.generic)))
      (hK₀ : boundedConstructible _ K₀) :
      IsIso ((L(((baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _)).i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
        ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) M.j)
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
            (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k'))
              (traitSlice_over _)).j)
          (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1)
            (traitSliceGaloisModelHom hM b hb).commSq_j)).app K₀)) := by
    have : K₀.IsGE hK₀.1.1.choose := hK₀.1.1.choose_spec
    have hpe := plusEtaleOrigin_extendScalars_residueField_of_boundedConstructible E hK₀
    have hu := isUnit_natCast_integersResidueField (ℓ := ℓ) E.1 hp hpℓ
    have hres := isIso_map_exchangeRight_traitSliceGaloisModelHom_finite hM b hb D hD
      (PadicAlgCl.integersResidueField ℓ E.1) hu _ hpe
    have h := isIso_map_baseChangeMap_app_padicIntegers_of_residueField ℓ E
      (traitSliceGaloisModelHom hM b hb).commSq_j
      (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).i K₀
      hK₀.1.1.choose (derivedCompleteIntegers_of_boundedConstructible hK₀)
      (by transport_exact hres)
    transport_exact h
  have key := isIso_map_baseChangeMap_app_padicAlgCl_of_integral ℓ
    (traitSliceGaloisModelHom hM b hb).commSq_j
    (baseChangeGaloisModel hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).i hC
    fun E K₀ hK₀ ↦ by transport_exact hint E K₀ hK₀
  have h := Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app
    (Profinite.padicAlgClRingObj ℓ) (traitSliceGaloisModelHom hM b hb) C (by transport_exact key)
  transport_exact h

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

-- The library-suggestion symbol frequency index traverses the statements of public theorems
-- without sharing at export, which takes minutes on the pullback exchanges of these concrete
-- models; they are excluded from the premise index.
run_cmd Lean.modifyEnv (fun env => List.foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env
  ["isIso_pullbackExchange_traitSliceGaloisChangeHom_finite",
      "isIso_map_exchangeRight_traitSliceGaloisModelHom_finite",
      "isIso_pullbackExchange_traitSliceGaloisModelHom", "isIso_map_exchangeRight_of_eq"])
