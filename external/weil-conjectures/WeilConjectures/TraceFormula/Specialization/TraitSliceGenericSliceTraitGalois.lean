/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public meta import Lean.LibrarySuggestions.Basic
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitCompositumMap
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisSquare
public import WeilConjectures.Tactic.TransportExact

/-!

# The change of trait `T ⟶ S'` between the Galois-layer models of the slices

Let `M` be a model of finite type over the trait `S = Spec k'⟦t⟧` with coordinate
`b : 𝒳 ⟶ 𝔸¹_S`, `D` a generic slice trait `S' = Spec R` of `𝔸¹_S`
(`AlgebraicGeometry.GenericSliceTrait`) and `T = Spec K⟦t⟧` the generic slice, which factors
through `S'`. On the models of the geometric generic fibres:

* the slice `σ_{S'} : M' ⟶ M` over `S'` gives the model `N₁` with generic fibre the Galois layer
  base `Z₂(S')` of `L' = Ω(R)` (`NearbyCyclesModel.genericSliceTraitGaloisModel`, an instance of
  `NearbyCyclesModel.sliceTraitGaloisModel`);
* the slice `σ_T : M'' ⟶ M` over `T` (`NearbyCyclesModel.traitSliceGenericHom`) gives the model
  `N₂` with generic fibre the base `Z₂(T)` of `L_T = Ω(K⟦t⟧)`
  (`NearbyCyclesModel.traitSliceGaloisModel`), its Galois layer `N₂_{L_T^sep}` and the morphism
  `ρ_T : M'' ⟶ N₂_{L_T^sep}` with invertible pullback exchange
  (`NearbyCyclesModel.isIso_pullbackExchange_traitSliceToGaloisLayer`).

This file constructs the change of trait `τ_N : N₂ ⟶ N₁` over `Spec l : Spec L_T ⟶ Spec L'`
(`NearbyCyclesModel.traitSliceGaloisChangeHom`) and shows, through the square
```
M''  ──τ──→  M'
 │ρ_T         │ρ_{S'}
N₂_{L_T^sep} ─τ'→ N₁_{L'^sep}
```
(`τ = NearbyCyclesModel.traitSliceGenericSliceTraitHom`), that the pullback exchange of the change
of Galois layers `τ'` (`NearbyCyclesModel.traitSliceGaloisLayerMap`) is invertible with finite
coefficients in which `p` is invertible, at complexes of étale origin
(`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGaloisLayerMap`), by the invariance of nearby
cycles under the change of trait `τ` (SGA 4½, [Th. finitude], Prop. 3.7). This mirrors
`WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGalois` (section `Pair`), with
the slice trait `T`, which is not weakly étale over `𝔸¹_S`, on one side.

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

/-- The geometric generic fibre of a model over the trait, with the geometric generic point
written as the spectrum of the structure map. -/
lemma IsTraitModelOver.isPullback_j_algebraMap (hM : M.IsTraitModelOver q g) :
    IsPullback M.j g q
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') (traitGenericField k')))) :=
  hM.isPullback_j

/-- The special fibre of a model over the trait, with the closed point written as the spectrum of
the constant coefficient. -/
lemma IsTraitModelOver.isPullback_i_constantCoeff (hM : M.IsTraitModelOver q g) :
    IsPullback M.i X'.hom q (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k')))) :=
  hM.isPullback_i

/-- The change of generic fibres of `φ.toCartesian` followed by the projection to the generic fibre
of the target is the change of generic fibres of `φ`. -/
@[reassoc]
lemma Hom.toCartesian_generic_fst {Y Y' Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
    {N : NearbyCyclesModel Y Y'} {f : Z ⟶ Y} {f' : Z' ⟶ Y'} (φ : P.Hom N f f') :
    φ.toCartesian.generic ≫ pullback.fst N.j φ.total = φ.generic :=
  pullback.lift_fst _ _ _

/-- The change of generic fibres of `φ.toCartesian` followed by the projection to the total space
of the source is the inclusion of the generic fibre of the source. -/
@[reassoc]
lemma Hom.toCartesian_generic_snd {Y Y' Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}
    {N : NearbyCyclesModel Y Y'} {f : Z ⟶ Y} {f' : Z' ⟶ Y'} (φ : P.Hom N f f') :
    φ.toCartesian.generic ≫ pullback.snd N.j φ.total = P.j :=
  pullback.lift_snd _ _ _

/-! ### The slice over the generic slice trait `S'` -/

/-- The model `N₁` of the geometric generic fibre of `M` with the total space and special fibre of
the slice `M'` over `S'` and generic fibre
`Z₂(S') = (M' ×_{S'} Spec(Ω ⊗ R)) ×_{Spec(Ω ⊗ R)} Spec L'`
(`NearbyCyclesModel.sliceTraitGaloisModel`). -/
noncomputable abbrev genericSliceTraitGaloisModel :=
  sliceTraitGaloisModel D.toSliceTrait M b hb hM.isPullback_j_algebraMap
    hM.isPullback_i_constantCoeff

/-! ### The slice over `T = Spec K⟦t⟧` -/

/-- The slice `σ_T : M'' ⟶ M` over `T = Spec K⟦t⟧` on the models of the geometric generic
fibres. -/
noncomputable abbrev traitSliceGenericHom :=
  (baseChangeHom hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).toGeneric

/-- The model `N₂` of the geometric generic fibre of `M` with the total space and special fibre of
the slice `M''` over `T` and generic fibre `Z₂(T)` (`NearbyCyclesModel.Hom.traitChangeModel`). -/
noncomputable abbrev traitSliceGaloisModel : NearbyCyclesModel M.generic
    (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left :=
  (traitSliceGenericHom hM b hb).traitChangeModel (traitGenericField (traitSliceField k'))
    (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q g
    hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))

/-- The structure map `Z₂(T) ⟶ Spec L_T` of the generic fibre of `N₂`. -/
noncomputable abbrev traitSliceGaloisResidue :
    (traitSliceGaloisModel hM b hb).generic ⟶
      Spec (.of (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
        (traitGenericField (traitSliceField k')))) :=
  (traitSliceGenericHom hM b hb).traitChangeResidue (traitGenericField (traitSliceField k'))
    (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q g
    hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))

/-- The Galois layer `N₂_{L_T^sep}` of `N₂` along `Z₂(T) ⟶ Spec L_T`. -/
noncomputable abbrev traitSliceGaloisLayer : NearbyCyclesModel M.generic
    (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left :=
  (traitSliceGaloisModel hM b hb).galoisLayer (traitSliceGaloisResidue hM b hb)
    (traitTensorCompositumSep (PowerSeries (traitSliceField k')) (traitGenericField k')
      (traitGenericField (traitSliceField k')))

/-- The morphism of models `ρ_T : M'' ⟶ N₂_{L_T^sep}`: the identity of total spaces and the purely
inseparable part `r₁` on generic fibres. -/
noncomputable abbrev traitSliceToGaloisLayer :=
  (traitSliceGenericHom hM b hb).toTraitChangeGaloisLayer (traitGenericField (traitSliceField k'))
    (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
    (baseChangeGenericStructure hM b hb _ (traitSlice_over _)) q g hM.isPullback_j.w
    (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))
    (isPullback_baseChange_j hM b hb _ (traitSlice_over _)).w
    (baseChangeHom_generic_comp hM b hb _ (traitSlice_over _))
/-- **The pullback exchange of `ρ_T : M'' ⟶ N₂_{L_T^sep}` is invertible** (all coefficients):
`ρ_T` is the identity of total spaces and a universal homeomorphism on generic fibres. -/
theorem isIso_pullbackExchange_traitSliceToGaloisLayer
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ M.generic))) :
    IsIso (((traitSliceToGaloisLayer hM b hb).pullbackExchange Λ).app C) := by
  have : IsUniversalHomeomorphism (traitSliceToGaloisLayer hM b hb).generic :=
    (traitSliceGenericHom hM b hb).isUniversalHomeomorphism_traitChangeInsepMap
      (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))
      (isPullback_baseChange_j hM b hb _ (traitSlice_over _)) hM.isPullback_j
      (baseChangeHom_generic_comp hM b hb _ (traitSlice_over _))
  have h := Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ
    (traitSliceGaloisLayer hM b hb) (traitSliceToGaloisLayer hM b hb).generic (ε' := 𝟙 _)
    (baseChange hM b hb _ (traitSlice_over (traitSliceCoord k'))).toGeneric
    (by
      have hj : (baseChange hM b hb _ (traitSlice_over (traitSliceCoord k'))).j =
          (traitSliceToGaloisLayer hM b hb).generic ≫ (traitSliceGaloisLayer hM b hb).j := by
        exact (Category.comp_id _).symm.trans (traitSliceToGaloisLayer hM b hb).comm_j.symm
      exact congrArg (fun j ↦ (⟨(baseChange hM b hb _ (traitSlice_over _)).total,
        (baseChange hM b hb _ (traitSlice_over _)).generic, j,
        (baseChange hM b hb _ (traitSlice_over _)).i, 𝟙 _⟩ : NearbyCyclesModel _ _)) hj)
    (traitSliceToGaloisLayer hM b hb) HEq.rfl HEq.rfl C
  transport_exact h

/-! ### The change of trait `τ_N : N₂ ⟶ N₁` -/

/-- The slice `σ_{S'} : M' ⟶ M` over the generic slice trait on the models of the geometric generic
fibres. -/
noncomputable abbrev genericSliceTraitGenericHom :=
  sliceTraitGenericHom D.toSliceTrait M b hb hM.isPullback_j_algebraMap
    hM.isPullback_i_constantCoeff

/-- The map `𝒳_η̄ ×_𝒳 𝒳'' ⟶ 𝒳_η̄ ×_𝒳 𝒳'` of the generic fibres of the cartesian models of the
slices over `T` and `S'`. -/
noncomputable def traitSliceCartesianGenericMap :
    (traitSliceGenericHom hM b hb).cartesianModel.generic ⟶
      (genericSliceTraitGenericHom hM b hb D).cartesianModel.generic :=
  pullback.map _ _ _ _ (𝟙 _) (traitSliceGenericSliceTraitTotal b D) (𝟙 _) (by simp)
    (by
      rw [Category.comp_id]
      exact (traitSliceGenericSliceTraitTotal_fst b D).symm)

@[reassoc (attr := simp)]
lemma traitSliceCartesianGenericMap_fst :
    traitSliceCartesianGenericMap hM b hb D ≫
        pullback.fst M.toGeneric.j (genericSliceTraitGenericHom hM b hb D).total =
      pullback.fst M.toGeneric.j (traitSliceGenericHom hM b hb).total :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma traitSliceCartesianGenericMap_snd :
    traitSliceCartesianGenericMap hM b hb D ≫
        pullback.snd M.toGeneric.j (genericSliceTraitGenericHom hM b hb D).total =
      pullback.snd M.toGeneric.j (traitSliceGenericHom hM b hb).total ≫
        traitSliceGenericSliceTraitTotal b D :=
  pullback.lift_snd _ _ _

/-- The map of the generic fibres of the cartesian models lies over the map
`Spec(Ω ⊗_{k'⟦t⟧} K⟦t⟧) ⟶ Spec(Ω ⊗_{k'⟦t⟧} R)`. -/
@[reassoc]
lemma traitSliceCartesianModelTensor_comp_tensorSpecMap :
    (traitSliceGenericHom hM b hb).cartesianModelTensor
        (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q
        g hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _)) ≫
        D.tensorSpecMap =
      traitSliceCartesianGenericMap hM b hb D ≫
        (genericSliceTraitGenericHom hM b hb D).cartesianModelTensor
          (sliceTraitStructure D.toSliceTrait M b) q g hM.isPullback_j.w
          (sliceTrait_fst_comp D.toSliceTrait M b hb) := by
  have h₁ : (genericSliceTraitGenericHom hM b hb D).cartesianModelTensor
      (sliceTraitStructure D.toSliceTrait M b) q g hM.isPullback_j.w
      (sliceTrait_fst_comp D.toSliceTrait M b hb) ≫
        traitTensorFst (PowerSeries k') D.toSliceTrait.R (traitGenericField k') =
      pullback.fst _ _ ≫ g :=
    Hom.cartesianModelTensor_fst _ _
  have h₂ : (genericSliceTraitGenericHom hM b hb D).cartesianModelTensor
      (sliceTraitStructure D.toSliceTrait M b) q g hM.isPullback_j.w
      (sliceTrait_fst_comp D.toSliceTrait M b hb) ≫
        traitTensorSnd (PowerSeries k') D.toSliceTrait.R (traitGenericField k') =
      pullback.snd _ _ ≫ sliceTraitStructure D.toSliceTrait M b :=
    Hom.cartesianModelTensor_snd _ _
  have h₃ : (traitSliceGenericHom hM b hb).cartesianModelTensor
      (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q
      g hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _)) ≫
        traitTensorFst (PowerSeries k') (PowerSeries (traitSliceField k'))
          (traitGenericField k') =
      pullback.fst _ _ ≫ g :=
    Hom.cartesianModelTensor_fst _ _
  have h₄ : (traitSliceGenericHom hM b hb).cartesianModelTensor
      (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)) q
      g hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _)) ≫
        traitTensorSnd (PowerSeries k') (PowerSeries (traitSliceField k'))
          (traitGenericField k') =
      pullback.snd _ _ ≫
        baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _) :=
    Hom.cartesianModelTensor_snd _ _
  have h₅ : D.tensorSpecMap ≫
      traitTensorFst (PowerSeries k') D.toSliceTrait.R (traitGenericField k') =
      traitTensorFst (PowerSeries k') (PowerSeries (traitSliceField k')) (traitGenericField k') :=
    D.tensorSpecMap_fst
  have h₆ : D.tensorSpecMap ≫
      traitTensorSnd (PowerSeries k') D.toSliceTrait.R (traitGenericField k') =
      traitTensorSnd (PowerSeries k') (PowerSeries (traitSliceField k')) (traitGenericField k') ≫
        Spec.map (CommRingCat.ofHom D.sliceι) :=
    D.tensorSpecMap_snd
  apply (isPullback_traitTensor (PowerSeries k') D.toSliceTrait.R (traitGenericField k')).hom_ext
  · exact (Category.assoc _ _ _).trans ((_ ≫= h₅).trans (h₃.trans
      ((traitSliceCartesianGenericMap_fst_assoc hM b hb D g).symm.trans
        ((traitSliceCartesianGenericMap hM b hb D ≫= h₁).symm.trans (Category.assoc _ _ _).symm))))
  · exact (Category.assoc _ _ _).trans ((_ ≫= h₆).trans ((Category.assoc _ _ _).symm.trans
      ((h₄ =≫ _).trans ((Category.assoc _ _ _).trans ((_ ≫= (traitSliceGenericSliceTraitTotal_snd
        b D).symm).trans ((Category.assoc _ _ _).symm.trans
          ((traitSliceCartesianGenericMap_snd hM b hb D =≫ _).symm.trans
            ((Category.assoc _ _ _).trans
            ((traitSliceCartesianGenericMap hM b hb D ≫= h₂).symm.trans
              (Category.assoc _ _ _).symm)))))))))
/-- The map `Z₂(T) ⟶ Z₂(S')` of the generic fibres of the models `N₂`, `N₁`. -/
noncomputable def traitSliceGaloisGenericMap :
    (traitSliceGaloisModel hM b hb).generic ⟶ (genericSliceTraitGaloisModel hM b hb D).generic :=
  pullback.map _ _ _ _ (traitSliceCartesianGenericMap hM b hb D)
    (Spec.map (CommRingCat.ofHom D.compositumMap)) D.tensorSpecMap
    (traitSliceCartesianModelTensor_comp_tensorSpecMap hM b hb D)
    D.compositumPoint_comp_tensorSpecMap

@[reassoc (attr := simp)]
lemma traitSliceGaloisGenericMap_fst :
    traitSliceGaloisGenericMap hM b hb D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ traitSliceCartesianGenericMap hM b hb D :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma traitSliceGaloisGenericMap_snd :
    traitSliceGaloisGenericMap hM b hb D ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.compositumMap) :=
  pullback.lift_snd _ _ _

/-- **The change of trait `τ_N : N₂ ⟶ N₁` of the Galois-layer models of the slices over `T` and
`S'`**, over the identity of the geometric generic fibre of `M` and the map of special fibres of
the slices: the change of trait of the slices on total spaces and `traitSliceGaloisGenericMap` on
generic fibres. -/
@[simps]
noncomputable def traitSliceGaloisChangeHom :
    (traitSliceGaloisModel hM b hb).Hom (genericSliceTraitGaloisModel hM b hb D) (𝟙 M.generic)
      (traitSliceGenericSliceTraitSpecial b D) where
  total := traitSliceGenericSliceTraitTotal b D
  generic := traitSliceGaloisGenericMap hM b hb D
  comm_j := (traitSliceGaloisGenericMap_fst_assoc hM b hb D _).trans
    ((pullback.fst _ _ ≫= traitSliceCartesianGenericMap_snd hM b hb D).trans
      (Category.assoc _ _ _).symm)
  comm_i := traitSliceGenericSliceTraitSpecial_fst b D
  comm_ε := (traitSliceGaloisGenericMap_fst_assoc hM b hb D _).trans
    ((pullback.fst _ _ ≫= ((Category.assoc _ _ _).symm.trans
      (traitSliceCartesianGenericMap_fst hM b hb D =≫ 𝟙 _))).trans (Category.comp_id _).symm)

/-- `τ_N` lies over `Spec l : Spec L_T ⟶ Spec L'`. -/
lemma traitSliceGaloisChangeHom_generic_comp_residue :
    (traitSliceGaloisChangeHom hM b hb D).generic ≫
        sliceTraitGaloisResidue D.toSliceTrait M b hb hM.isPullback_j_algebraMap
          hM.isPullback_i_constantCoeff =
      traitSliceGaloisResidue hM b hb ≫ Spec.map (CommRingCat.ofHom D.compositumMap) :=
  traitSliceGaloisGenericMap_snd hM b hb D

/-- **The change of Galois layers** `τ' : N₂_{L_T^sep} ⟶ N₁_{L'^sep}` induced by `τ_N` and the map
`ω : L'^sep ⟶ L_T^sep` of separable closures (`NearbyCyclesModel.galoisLayerMap`). -/
noncomputable abbrev traitSliceGaloisLayerMap :
    (traitSliceGaloisLayer hM b hb).Hom
      (sliceTraitGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff) (𝟙 M.generic) (traitSliceGenericSliceTraitSpecial b D) :=
  galoisLayerMap D.toSliceTrait.compositumSep
    (traitTensorCompositumSep (PowerSeries (traitSliceField k')) (traitGenericField k')
      (traitGenericField (traitSliceField k'))) D.compositumSepMap
    D.compositumSepMap_comp_algebraMap (traitSliceGaloisChangeHom hM b hb D)
    (traitSliceGaloisChangeHom_generic_comp_residue hM b hb D)

/-- The slices over `T` and `S'` commute with `τ` on geometric generic fibres. -/
@[reassoc]
lemma traitSliceGenericSliceTraitGeneric_comp_sliceTraitGeneric :
    traitSliceGenericSliceTraitGeneric hM b hb D ≫
        sliceTraitGeneric D.toSliceTrait M b hb hM.isPullback_j_algebraMap =
      baseChangeGenericMap hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _) := by
  have hω : Spec.map (CommRingCat.ofHom D.ωK) ≫ Spec.map (CommRingCat.ofHom D.ωS) =
      traitGenericPointMap k' (traitSliceField k') := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ωK_comp_ωS]
    rfl
  apply hM.isPullback_j.hom_ext
  · exact (Category.assoc _ _ _).trans ((_ ≫= IsPullback.lift_fst _ _ _ _).trans
      ((Category.assoc _ _ _).symm.trans
        ((traitSliceGenericSliceTraitGeneric_fst hM b hb D =≫ _).trans
        ((Category.assoc _ _ _).trans
          ((pullback.fst _ _ ≫= traitSliceGenericSliceTraitTotal_fst b D).trans
          (baseChangeGenericMap_j hM b hb _ _).symm)))))
  · exact (Category.assoc _ _ _).trans ((_ ≫= IsPullback.lift_snd _ _ _ _).trans
      ((Category.assoc _ _ _).symm.trans
        ((traitSliceGenericSliceTraitGeneric_snd hM b hb D =≫ _).trans
        ((Category.assoc _ _ _).trans ((pullback.snd _ _ ≫= hω).trans
          (baseChangeGenericMap_g hM b hb _ _).symm)))))
/-- The first components of the purely inseparable part `r₁` of `ρ_T`: `r₁ ≫ q ≫ r₂` is the change
of generic fibres of the cartesian model of `σ_T`. -/
@[reassoc]
lemma traitSliceToGaloisLayer_generic_fst_fst :
    (traitSliceToGaloisLayer hM b hb).generic ≫
        pullback.fst (traitSliceGaloisResidue hM b hb)
          (Spec.map (CommRingCat.ofHom (algebraMap
            (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
              (traitGenericField (traitSliceField k')))
            (traitTensorCompositumSep (PowerSeries (traitSliceField k')) (traitGenericField k')
              (traitGenericField (traitSliceField k')))))) ≫
        pullback.fst ((traitSliceGenericHom hM b hb).cartesianModelTensor
          (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
          q g hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _)))
          (traitTensorCompositumPoint (PowerSeries k') (PowerSeries (traitSliceField k'))
            (traitGenericField k') (traitGenericField (traitSliceField k'))) =
      (traitSliceGenericHom hM b hb).toCartesian.generic :=
  (traitSliceGenericHom hM b hb).traitChangeInsepMap_comp_traitChangeGaloisMap_comp
    hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _))
    (isPullback_baseChange_j hM b hb _ (traitSlice_over _)).w
    (baseChangeHom_generic_comp hM b hb _ (traitSlice_over _))

/-- The component of `r₁` in `Spec L_T`. -/
@[reassoc]
lemma traitSliceToGaloisLayer_generic_fst_snd :
    (traitSliceToGaloisLayer hM b hb).generic ≫
        pullback.fst (traitSliceGaloisResidue hM b hb)
          (Spec.map (CommRingCat.ofHom (algebraMap
            (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
              (traitGenericField (traitSliceField k')))
            (traitTensorCompositumSep (PowerSeries (traitSliceField k')) (traitGenericField k')
              (traitGenericField (traitSliceField k')))))) ≫
        pullback.snd ((traitSliceGenericHom hM b hb).cartesianModelTensor
          (baseChangeTotalStructure hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
          q g hM.isPullback_j.w (baseChangeHom_total_comp hM b hb _ (traitSlice_over _)))
          (traitTensorCompositumPoint (PowerSeries k') (PowerSeries (traitSliceField k'))
            (traitGenericField k') (traitGenericField (traitSliceField k'))) =
      pullback.snd _ _ ≫ traitTensorSepPoint (PowerSeries (traitSliceField k'))
        (traitGenericField k') (traitGenericField (traitSliceField k')) ≫
        traitTensorCompositumGalois (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

/-- The component of `r₁` in `Spec L_T^sep`. -/
@[reassoc]
lemma traitSliceToGaloisLayer_generic_snd :
    (traitSliceToGaloisLayer hM b hb).generic ≫
        pullback.snd (traitSliceGaloisResidue hM b hb)
          (Spec.map (CommRingCat.ofHom (algebraMap
            (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
              (traitGenericField (traitSliceField k')))
            (traitTensorCompositumSep (PowerSeries (traitSliceField k')) (traitGenericField k')
              (traitGenericField (traitSliceField k')))))) =
      pullback.snd _ _ ≫ traitTensorSepPoint (PowerSeries (traitSliceField k'))
        (traitGenericField k') (traitGenericField (traitSliceField k')) :=
  pullback.lift_snd _ _ _

/-- The square of generic fibres of the second square: `τ ≫ ρ_{S'} = ρ_T ≫ τ'`. -/
lemma traitSliceGenericSliceTraitGeneric_comp_toGaloisLayer_generic :
    traitSliceGenericSliceTraitGeneric hM b hb D ≫
        (sliceTraitToGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
          hM.isPullback_i_constantCoeff).generic =
      (traitSliceToGaloisLayer hM b hb).generic ≫
        (traitSliceGaloisLayerMap hM b hb D).generic := by
  have c₁ : traitSliceGenericSliceTraitGeneric hM b hb D ≫
      (sliceTraitToGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff).generic ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
          pullback.fst _ _ =
      baseChangeGenericMap hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _) := by
    refine (_ ≫= sliceTraitToGaloisLayer_generic_fst_fst_assoc ..).trans ?_
    refine (_ ≫= Hom.toCartesian_generic_fst _).trans ?_
    exact traitSliceGenericSliceTraitGeneric_comp_sliceTraitGeneric hM b hb D
  have c₁' : (traitSliceToGaloisLayer hM b hb).generic ≫
      (traitSliceGaloisLayerMap hM b hb D).generic ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
          pullback.fst _ _ =
      baseChangeGenericMap hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _) := by
    refine (_ ≫= galoisLayerGenericMap_fst_assoc (hω := D.compositumSepMap_comp_algebraMap)
      (hτ := traitSliceGaloisChangeHom_generic_comp_residue hM b hb D) ..).trans ?_
    refine (_ ≫= _ ≫= traitSliceGaloisGenericMap_fst_assoc hM b hb D _).trans ?_
    refine (_ ≫= _ ≫= _ ≫= traitSliceCartesianGenericMap_fst hM b hb D).trans ?_
    refine (traitSliceToGaloisLayer_generic_fst_fst_assoc hM b hb _).trans ?_
    exact Hom.toCartesian_generic_fst _
  have c₂ : traitSliceGenericSliceTraitGeneric hM b hb D ≫
      (sliceTraitToGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff).generic ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
          pullback.snd _ _ =
      (baseChange hM b hb _ (traitSlice_over (traitSliceCoord k'))).j ≫
        traitSliceGenericSliceTraitTotal b D := by
    refine (_ ≫= sliceTraitToGaloisLayer_generic_fst_fst_assoc ..).trans ?_
    refine (_ ≫= Hom.toCartesian_generic_snd _).trans ?_
    exact (traitSliceGenericSliceTraitHom hM b hb D).comm_j
  have c₂' : (traitSliceToGaloisLayer hM b hb).generic ≫
      (traitSliceGaloisLayerMap hM b hb D).generic ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
          pullback.snd _ _ =
      (baseChange hM b hb _ (traitSlice_over (traitSliceCoord k'))).j ≫
        traitSliceGenericSliceTraitTotal b D := by
    refine (_ ≫= galoisLayerGenericMap_fst_assoc (hω := D.compositumSepMap_comp_algebraMap)
      (hτ := traitSliceGaloisChangeHom_generic_comp_residue hM b hb D) ..).trans ?_
    refine (_ ≫= _ ≫= traitSliceGaloisGenericMap_fst_assoc hM b hb D _).trans ?_
    refine (_ ≫= _ ≫= _ ≫= traitSliceCartesianGenericMap_snd hM b hb D).trans ?_
    refine (traitSliceToGaloisLayer_generic_fst_fst_assoc hM b hb
      (pullback.snd _ _ ≫ traitSliceGenericSliceTraitTotal b D)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (Hom.toCartesian_generic_snd _ =≫ _)
  have c₃ : traitSliceGenericSliceTraitGeneric hM b hb D ≫
      (sliceTraitToGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff).generic ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      baseChangeGenericStructure hM b hb _ (traitSlice_over (traitSliceCoord k')) ≫
        traitTensorSepPoint (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        traitTensorCompositumGalois (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        Spec.map (CommRingCat.ofHom D.compositumMap) := by
    refine (_ ≫= sliceTraitToGaloisLayer_generic_fst_snd ..).trans ?_
    refine (traitSliceGenericSliceTraitGeneric_snd_assoc hM b hb D _).trans ?_
    refine (_ ≫= D.sepPoint_comp_assoc _).trans ?_
    exact _ ≫= _ ≫= by transport_exact D.compositumGalois_comp
  have c₃' : (traitSliceToGaloisLayer hM b hb).generic ≫
      (traitSliceGaloisLayerMap hM b hb D).generic ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      baseChangeGenericStructure hM b hb _ (traitSlice_over (traitSliceCoord k')) ≫
        traitTensorSepPoint (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        traitTensorCompositumGalois (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        Spec.map (CommRingCat.ofHom D.compositumMap) := by
    refine (_ ≫= galoisLayerGenericMap_fst_assoc (hω := D.compositumSepMap_comp_algebraMap)
      (hτ := traitSliceGaloisChangeHom_generic_comp_residue hM b hb D) ..).trans ?_
    refine (_ ≫= _ ≫= traitSliceGaloisGenericMap_snd hM b hb D).trans ?_
    transport_exact traitSliceToGaloisLayer_generic_fst_snd_assoc hM b hb
      (Spec.map (CommRingCat.ofHom D.compositumMap))
  have c₄ : traitSliceGenericSliceTraitGeneric hM b hb D ≫
      (sliceTraitToGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
        hM.isPullback_i_constantCoeff).generic ≫ pullback.snd _ _ =
      baseChangeGenericStructure hM b hb _ (traitSlice_over (traitSliceCoord k')) ≫
        traitTensorSepPoint (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        Spec.map (CommRingCat.ofHom D.compositumSepMap) := by
    refine (_ ≫= sliceTraitToGaloisLayer_generic_snd ..).trans ?_
    refine (traitSliceGenericSliceTraitGeneric_snd_assoc hM b hb D _).trans ?_
    exact _ ≫= by transport_exact D.sepPoint_comp
  have c₄' : (traitSliceToGaloisLayer hM b hb).generic ≫
      (traitSliceGaloisLayerMap hM b hb D).generic ≫ pullback.snd _ _ =
      baseChangeGenericStructure hM b hb _ (traitSlice_over (traitSliceCoord k')) ≫
        traitTensorSepPoint (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        Spec.map (CommRingCat.ofHom D.compositumSepMap) := by
    refine (_ ≫= galoisLayerGenericMap_snd (hω := D.compositumSepMap_comp_algebraMap)
      (hτ := traitSliceGaloisChangeHom_generic_comp_residue hM b hb D) ..).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      ((traitSliceToGaloisLayer_generic_snd hM b hb =≫ _).trans (Category.assoc _ _ _))
  refine pullback.hom_ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_) ?_
  · exact (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (Category.assoc _ _ _)).trans
      (c₁.trans (c₁'.symm.trans
        (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (Category.assoc _ _ _)).symm))
  · exact (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (Category.assoc _ _ _)).trans
      (c₂.trans (c₂'.symm.trans
        (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (Category.assoc _ _ _)).symm))
  · exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
      (c₃.trans (c₃'.symm.trans ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm))
  · exact (Category.assoc _ _ _).trans (c₄.trans (c₄'.symm.trans (Category.assoc _ _ _).symm))
/-- **The change of Galois layers from the change of trait `T ⟶ S'` of the slices** (SGA 4½,
[Th. finitude], proof of 3.7): the square `ρ_{S'} ∘ τ = τ' ∘ ρ_T` of morphisms of models, whose
vertical sides `ρ` have invertible pullback exchanges, shows that the exchange of the change of
Galois layers `τ'` is invertible at `C` once the change of trait `τ` of the slices is invertible at
the restriction of `C`. -/
theorem isIso_pullbackExchange_traitSliceGaloisLayerMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.generic) Ab.{u + 1})
      (condensedRingObj Λ M.generic)))
    (hIH : IsIso (((traitSliceGenericSliceTraitHom hM b hb D).toGeneric.pullbackExchange Λ).app
      (L((sliceTraitGeneric D.toSliceTrait M b hb hM.isPullback_j_algebraMap)^*⟦Λ⟧).obj C))) :
    IsIso (((traitSliceGaloisLayerMap hM b hb D).pullbackExchange Λ).app C) := by
  have h₁ := isIso_pullbackExchange_sliceTraitToGaloisLayer D.toSliceTrait M b hb
    hM.isPullback_j_algebraMap hM.isPullback_i_constantCoeff Λ C
  have h₂ := isIso_pullbackExchange_traitSliceToGaloisLayer hM b hb Λ
    (L((𝟙 M.generic)^*⟦Λ⟧).obj C)
  have key := Hom.isIso_map_pullbackExchange_app_of_square_of_isIso Λ
    (traitSliceGenericSliceTraitHom hM b hb D).toGeneric
    (sliceTraitToGaloisLayer D.toSliceTrait M b hb hM.isPullback_j_algebraMap
      hM.isPullback_i_constantCoeff)
    (traitSliceToGaloisLayer hM b hb) (traitSliceGaloisLayerMap hM b hb D)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (traitSliceGenericSliceTraitGeneric_comp_toGaloisLayer_generic hM b hb D)
    ((traitSliceGenericSliceTraitGeneric_comp_sliceTraitGeneric hM b hb D).trans
      (Category.comp_id _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm) C
    (by transport_exact h₁) (by transport_exact h₂) (by transport_exact hIH)
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId Λ
    (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left)
    (((traitSliceGaloisLayerMap hM b hb D).pullbackExchange Λ).app C)).mp (by transport_exact key)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

-- The library-suggestion symbol frequency index traverses the statements of public theorems
-- without sharing at export, which takes minutes on the pullback exchanges of these concrete
-- models; they are excluded from the premise index.
run_cmd Lean.modifyEnv (fun env => List.foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env
  ["isIso_pullbackExchange_traitSliceToGaloisLayer",
      "isIso_pullbackExchange_traitSliceGaloisLayerMap"])
