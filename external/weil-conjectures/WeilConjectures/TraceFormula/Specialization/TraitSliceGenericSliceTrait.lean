/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeFiniteCoefficient
public import WeilConjectures.Tactic.TransportExact
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.Tactic.ExactModProofs
public meta import Lean.LibrarySuggestions.Basic

/-!

# The slice over `Spec K⟦t⟧` as a change of trait of the slice over a generic slice trait

Let `M` be a model over the trait `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and let
`D` be a generic slice trait of `𝔸¹_S` (`AlgebraicGeometry.GenericSliceTrait`), the strict
localization `S' = Spec R` of `𝔸¹_S` at the generic point of its special fibre, through which the
generic slice `σ : T = Spec K⟦t⟧ ⟶ 𝔸¹_S` factors by `D.ι : R ⟶ K⟦t⟧`. The geometric slice
`M'' = M ×_{𝔸¹_S} T` (`NearbyCyclesModel.baseChange`) is then the base change of the slice
`M' = M ×_{𝔸¹_S} S'` (`NearbyCyclesModel.sliceTraitModel`) along the change of strictly
henselian traits `T ⟶ S'`:
```
𝒳'' = 𝒳 ×_{𝔸¹_S} T ──τ──→ 𝒳' = 𝒳 ×_{𝔸¹_S} S'
        │                        │
        T ──────── D.ι ────────→ S'
```
is cartesian (`NearbyCyclesModel.isPullback_genericSliceTraitChangeTotal'`). The morphism of
models `τ : M'' ⟶ M'` of the geometric generic fibres
(`NearbyCyclesModel.traitSliceGenericSliceTraitHom`) therefore has invertible pullback exchange
with finite coefficients at complexes of étale origin, by the invariance of nearby cycles under
change of trait (SGA 4½, [Th. finitude], Prop. 3.7,
`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`):
`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGenericSliceTraitHom_finite`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

namespace GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- The characteristic of `k'` divides every natural number vanishing in the residue field of a
generic slice trait. -/
lemma ringChar_dvd_of_natCast_eq_zero (n : ℕ) (hn : (n : ResidueField D.R) = 0) :
    ringChar k' ∣ n := by
  rw [← map_natCast (IsLocalRing.residue D.R), IsLocalRing.residue_eq_zero_iff, ← D.ker_b,
    RingHom.mem_ker, map_natCast] at hn
  rw [← D.ringChar_κ]
  exact ringChar.dvd hn

end GenericSliceTrait

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Abstract

/-- Invertibility of `H` applied to a natural transformation is transported along isomorphisms of
objects. -/
lemma _root_.CategoryTheory.NatTrans.isIso_map_app_of_iso {C D E : Type*} [Category C]
    [Category D] [Category E] {F G : C ⥤ D} (η : F ⟶ G) (H : D ⥤ E) {o o' : C} (e : o ≅ o')
    (h : IsIso (H.map (η.app o))) : IsIso (H.map (η.app o')) :=
  (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight η H) e).1 h

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]
  {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂}
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ : Type u} [Field κ] [IsSepClosed κ] {b₂ : R₂ →+* κ}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Invariance of nearby cycles under change of strictly henselian trait, finite coefficients
`T`, on the models of the geometric generic fibres**: in the situation of
`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`, the pullback
exchange of `φ.toGeneric` is invertible at every complex `K` on the geometric generic fibre of `N`
which is bounded below of étale origin. -/
theorem Hom.isIso_pullbackExchange_toGeneric_app_of_isPullback_trait_finite [IsLocalHom ι]
    (hι : Function.Injective ι) (hun : maximalIdeal R₂ = (maximalIdeal R₁).map ι)
    (p : ℕ) [Fact p.Prime] (hp : ∀ n : ℕ, (n : ResidueField R₁) = 0 → p ∣ n)
    (hpT : IsUnit (p : T)) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂) (hc : c.comp a₁ = a₂.comp ι)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [hq₁ : LocallyOfFiniteType q₁]
    [hq₁' : QuasiCompact q₁] [hq₁'' : IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) N.generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) N.generic
      ((finiteCoefficientDerivedEquivalence N.generic T).functor.obj K)) :
    IsIso ((φ.toGeneric.pullbackExchange (Profinite.continuousMapRingObj T)).app K) := by
  refine (Scheme.Hom.exists_locallyEmbedsInAffineSpace q₁).elim fun m hm ↦ ?_
  have hw : (M.i ≫ φ.total) ≫ q₁ = p₂ ≫ Spec.map (CommRingCat.ofHom (b₂.comp ι)) := by
    rw [Category.assoc, hφ.w, reassoc_of% hMi.w, CommRingCat.ofHom_comp, Spec.map_comp]
  have h := (traitChangeInvariance T m).isIso ι hι hun p hp hpT a₁ a₂ c ha₁
    ha₂ halg₁ halg₂ hc b₂ hb₂ (φ.toGenericWithSpecial (pullback.fst _ _)
      (pullback.lift (M.i ≫ φ.total) p₂ hw) (pullback.lift_fst _ _ _)) q₁ inferInstance
    inferInstance inferInstance hm g₁ hNj (pullback.snd _ _) (IsPullback.of_hasPullback _ _) q₂
    g₂ hMj p₂ hMi hφ hgen (pullback.lift_snd _ _ _) K hK
  have h' := Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_toGenericWithSpecial
    (Profinite.continuousMapRingObj T) φ (pullback.fst _ _) (pullback.lift (M.i ≫ φ.total) p₂ hw)
    (pullback.lift_fst _ _ _) K (by exact_mod_proofs h)
  have h₃ := Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app
    (Profinite.continuousMapRingObj T) φ.toGeneric K (by
      refine NatTrans.isIso_map_app_of_iso _ _
        ((leftDerivedUpperStarId (Profinite.continuousMapRingObj T) N.generic).app K).symm ?_
      transport_exact h')
  exact_mod_proofs h₃

end Abstract

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

/-- The morphism of total spaces `𝒳 ×_{𝔸¹_S} T ⟶ 𝒳 ×_{𝔸¹_S} S'` of the slices, induced by the
factorisation `T ⟶ S' ⟶ 𝔸¹_S` of the generic slice. -/
noncomputable def traitSliceGenericSliceTraitTotal :
    pullback b (traitSlice (traitSliceCoord k')) ⟶ sliceTraitTotal D.toSliceTrait M b :=
  pullback.map b (traitSlice (traitSliceCoord k')) b D.toAffineLine (𝟙 _)
    (Spec.map (CommRingCat.ofHom D.ι)) (𝟙 _) (by simp) (by
      rw [Category.comp_id]
      exact D.spec_ι_comp.symm)

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitTotal_fst :
    traitSliceGenericSliceTraitTotal b D ≫ pullback.fst b D.toAffineLine = pullback.fst _ _ := by
  simp [traitSliceGenericSliceTraitTotal]

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitTotal_snd :
    traitSliceGenericSliceTraitTotal b D ≫ pullback.snd b D.toAffineLine =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ι) := by
  simp [traitSliceGenericSliceTraitTotal]

/-- **The slice over `T` is the base change of the slice over `S'`**: the square of total
spaces over the change of traits `Spec K⟦t⟧ ⟶ S'` is cartesian. -/
lemma isPullback_traitSliceGenericSliceTraitTotal :
    IsPullback (traitSliceGenericSliceTraitTotal b D)
      (pullback.snd b (traitSlice (traitSliceCoord k')))
      (sliceTraitStructure D.toSliceTrait M b) (Spec.map (CommRingCat.ofHom D.ι)) := by
  have h : IsPullback (pullback.fst b (traitSlice (traitSliceCoord k')))
      (pullback.snd b (traitSlice (traitSliceCoord k'))) b
      (Spec.map (CommRingCat.ofHom D.ι) ≫ D.toAffineLine) := by
    rw [D.spec_ι_comp]
    exact IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (traitSliceGenericSliceTraitTotal_snd b D)
    (IsPullback.of_hasPullback b D.toAffineLine)
  rw [traitSliceGenericSliceTraitTotal_fst]
  exact h

/-- The map `𝒳'' ×_T Spec Ω_K ⟶ 𝒳' ×_{S'} Spec Ω'` of geometric generic fibres of the slices,
induced by `D.ωK : Ω' ⟶ Ω_K`. -/
noncomputable def traitSliceGenericSliceTraitGeneric :
    (baseChange hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).generic ⟶
      (sliceTraitModel D.toSliceTrait M b).generic :=
  pullback.map _ _ _ _ (traitSliceGenericSliceTraitTotal b D)
    (Spec.map (CommRingCat.ofHom D.ωK)) (Spec.map (CommRingCat.ofHom D.ι))
    (traitSliceGenericSliceTraitTotal_snd b D).symm (by
      simp only [GenericSliceTrait.toSliceTrait_a, traitGenericPoint, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, D.ωK_comp_a])

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitGeneric_fst :
    traitSliceGenericSliceTraitGeneric hM b hb D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ traitSliceGenericSliceTraitTotal b D :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitGeneric_snd :
    traitSliceGenericSliceTraitGeneric hM b hb D ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωK) :=
  pullback.lift_snd _ _ _

/-- The map `𝒳'' ×_T Spec K ⟶ 𝒳' ×_{S'} Spec κ'` of special fibres of the slices, induced by
`D.κK : κ' ⟶ K`. -/
noncomputable def traitSliceGenericSliceTraitSpecial :
    (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left ⟶
      pullback (sliceTraitStructure D.toSliceTrait M b) (Spec.map (CommRingCat.ofHom D.b)) :=
  pullback.map _ _ _ _ (traitSliceGenericSliceTraitTotal b D)
    (Spec.map (CommRingCat.ofHom D.κK)) (Spec.map (CommRingCat.ofHom D.ι))
    (traitSliceGenericSliceTraitTotal_snd b D).symm (by
      simp only [traitClosedPoint, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, D.κK_comp_b])

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitSpecial_fst :
    traitSliceGenericSliceTraitSpecial b D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ traitSliceGenericSliceTraitTotal b D :=
  pullback.lift_fst _ _ _

/-- **The change of trait `τ : M'' ⟶ M'` from the slice over `T` to the slice over `S'`**, on the
geometric models: `traitSliceGenericSliceTraitTotal` on total spaces and
`traitSliceGenericSliceTraitGeneric` on geometric generic fibres. -/
@[simps]
noncomputable def traitSliceGenericSliceTraitHom :
    (baseChange hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).geometric.Hom
      (sliceTraitModel D.toSliceTrait M b) (traitSliceGenericSliceTraitTotal b D)
      (traitSliceGenericSliceTraitSpecial b D) where
  total := traitSliceGenericSliceTraitTotal b D
  generic := traitSliceGenericSliceTraitGeneric hM b hb D
  comm_j := traitSliceGenericSliceTraitGeneric_fst hM b hb D
  comm_i := traitSliceGenericSliceTraitSpecial_fst b D
  comm_ε := traitSliceGenericSliceTraitGeneric_fst hM b hb D

variable [Fact (ringChar k').Prime]

/-- **Invariance of the nearby cycles of the slice under the change of trait `T ⟶ S'`**, finite
coefficients (SGA 4½, [Th. finitude], Prop. 3.7): the pullback exchange of the change of trait
`τ : M'' ⟶ M'` on the models of the geometric generic fibres is invertible at every complex `K`
on the geometric generic fibre of `M'` which is bounded below of étale origin, for a finite ring
`T₀` in which the characteristic `p` of `k'` is invertible. -/
theorem isIso_pullbackExchange_traitSliceGenericSliceTraitHom_finite
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] (hpT : IsUnit ((ringChar k' : ℕ) : T₀))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (sliceTraitModel D.toSliceTrait M b).generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀)
        (sliceTraitModel D.toSliceTrait M b).generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀))
      (sliceTraitModel D.toSliceTrait M b).generic
      ((finiteCoefficientDerivedEquivalence _ T₀).functor.obj K)) :
    IsIso (((traitSliceGenericSliceTraitHom hM b hb D).toGeneric.pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app K) := by
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have : LocallyOfFiniteType b := by
    subst hb
    exact locallyOfFiniteType_of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : QuasiCompact b := by
    subst hb
    exact QuasiCompact.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : IsSeparated b := by
    subst hb
    exact IsSeparated.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have h₁ : LocallyOfFiniteType (sliceTraitStructure D.toSliceTrait M b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b D.toAffineLine) inferInstance
  have h₂ : QuasiCompact (sliceTraitStructure D.toSliceTrait M b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b D.toAffineLine) inferInstance
  have h₃ : IsSeparated (sliceTraitStructure D.toSliceTrait M b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b D.toAffineLine) inferInstance
  have h := Hom.isIso_pullbackExchange_toGeneric_app_of_isPullback_trait_finite T₀
    (R₁ := D.R) (R₂ := PowerSeries (traitSliceField k')) (ι := D.ι)
    (Ω₁ := D.Ω) (Ω₂ := traitGenericField (traitSliceField k')) (a₁ := D.a)
    (a₂ := algebraMap (PowerSeries (traitSliceField k')) (traitGenericField (traitSliceField k')))
    (c := D.ωK) (κ := traitSliceField k') (b₂ := PowerSeries.constantCoeff)
    (M := (baseChange hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).geometric)
    (N := sliceTraitModel D.toSliceTrait M b) (f := traitSliceGenericSliceTraitTotal b D)
    (f' := traitSliceGenericSliceTraitSpecial b D) (hq₁ := by exact_mod_proofs h₁)
    (hq₁' := by exact_mod_proofs h₂) (hq₁'' := by exact_mod_proofs h₃)
    D.injective_ι D.maximalIdeal_eq_map_ι (ringChar k')
    D.ringChar_dvd_of_natCast_eq_zero hpT D.injective_a (algebraMap_traitGenericField_injective _)
    D.isAlgebraic_a (isAlgebraic_traitGenericField _) D.ωK_comp_a
    PowerSeries.ker_coeff_eq_max_ideal (traitSliceGenericSliceTraitHom hM b hb D)
    (sliceTraitStructure D.toSliceTrait M b) (pullback.snd _ _)
    (isPullback_sliceTraitModel_j D.toSliceTrait M b)
    (pullback.snd b (traitSlice (traitSliceCoord k'))) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (isPullback_traitSliceGenericSliceTraitTotal b D)
    (traitSliceGenericSliceTraitGeneric_snd hM b hb D) K (by exact_mod_proofs hK)
  exact_mod_proofs h

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

-- The library-suggestion symbol frequency index traverses the statements of public theorems
-- without sharing at export, which takes minutes on the pullback exchanges of these concrete
-- models; they are excluded from the premise index.
run_cmd Lean.modifyEnv (fun env => List.foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env
  ["isIso_pullbackExchange_toGeneric_app_of_isPullback_trait_finite",
      "isIso_pullbackExchange_traitSliceGenericSliceTraitHom_finite"])
