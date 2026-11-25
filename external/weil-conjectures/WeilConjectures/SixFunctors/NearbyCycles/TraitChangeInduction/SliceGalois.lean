/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceChange
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.TraceFormula.Specialization.TraitChangeGaloisLayer
public import WeilConjectures.SixFunctors.NearbyCycles.UniversalHomeomorphismExchange

/-!

# The change of trait between the Galois layers of two slices

Let `H : S₂(x) ⟶ S₁(x)` be a morphism of slice traits over a change of trait `ι : R₁ ⟶ R₂`,
`φ : M ⟶ N` a morphism of models over `Spec ι` and `cN`, `cM` compatible coordinates, with slices
`σ_N : N' ⟶ N`, `σ_M : M' ⟶ M` over the slice traits
(`NearbyCyclesModel.sliceTraitHom`) and change of trait of the slices `φ' : M' ⟶ N'`
(`NearbyCyclesModel.sliceTraitChangeHom`). The change of geometric generic fibres of `σ_N` is,
up to universal homeomorphisms, the Galois layer of `L₁^sep / L₁` over the model `N₁`
(`NearbyCyclesModel.Hom.traitChangeModel`), and likewise for `σ_M` with `L₂^sep / L₂`. This file
constructs the change of trait `τ : N₂ ⟶ N₁` of these models over `Spec l : Spec L₂ ⟶ Spec L₁`
(`NearbyCyclesModel.sliceGaloisChangeHom`) and checks the two commutative squares
```
M'  ──φ'──→  N'                N₂ ──τ──→ N₁
 │ρ_M         │ρ_N              │ψ_M       │ψ_N
N₂_{L₂^sep} ─τ'→ N₁_{L₁^sep}    M  ──φ──→  N
```
of morphisms of models, with `τ'` the change of Galois layers (`NearbyCyclesModel.galoisLayerMap`),
`ρ` the universal homeomorphisms onto the Galois layers and `ψ` the composites of the nilpotent
thickenings and the weakly étale cartesian parts. These are the squares through which Deligne's
induction (SGA 4½, [Th. finitude], proof of 3.7) reduces the change of trait on the generic slice
to the change of trait of the slices.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme SliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ

section Single

variable {R : Type u} [CommRing R] [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra R Ω]
  {κ : Type u} [Field κ] {b : R →+* κ} (D : SliceTrait (algebraMap R Ω) b)
  {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R))) {q : N.total ⟶ Spec (.of R)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R) = q)
  {g : N.generic ⟶ Spec (.of Ω)}
  (hNj : IsPullback N.j g q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
  {p : Y' ⟶ Spec (.of κ)} (hNi : IsPullback N.i p q (Spec.map (CommRingCat.ofHom b)))

/-- The slice `σ : N' ⟶ N` on the models of the geometric generic fibres. -/
noncomputable abbrev sliceTraitGenericHom :
    (sliceTraitModel D N cN).toGeneric.Hom N.toGeneric (sliceTraitGeneric D N cN hcN hNj)
      (sliceTraitSpecial D N cN hcN hNi) :=
  (sliceTraitHom D N cN hcN hNj hNi).toGeneric

/-- The model `N₁` with the total space and special fibre of the slice `N'` and generic fibre
`Z₂ = (N' ×_{S(x)} T) ×_T Spec L` (`NearbyCyclesModel.Hom.traitChangeModel`), `L = Ω(S(x))`. -/
noncomputable abbrev sliceTraitGaloisModel : NearbyCyclesModel N.generic
    (pullback (sliceTraitStructure D N cN) (Spec.map (CommRingCat.ofHom D.b))) :=
  (sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeModel D.Ω (sliceTraitStructure D N cN) q g
    hNj.w    (sliceTrait_fst_comp D N cN hcN)

/-- The structure map `Z₂ ⟶ Spec L` of the generic fibre of `N₁`. -/
noncomputable abbrev sliceTraitGaloisResidue :
    (sliceTraitGaloisModel D N cN hcN hNj hNi).generic ⟶ Spec (.of D.compositum) :=
  (sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeResidue D.Ω (sliceTraitStructure D N cN) q g
    hNj.w (sliceTrait_fst_comp D N cN hcN)

/-- The Galois layer `N₁_{L^sep}` of the model `N₁` along `Z₂ ⟶ Spec L` and `L^sep / L`. -/
noncomputable abbrev sliceTraitGaloisLayer : NearbyCyclesModel N.generic
    (pullback (sliceTraitStructure D N cN) (Spec.map (CommRingCat.ofHom D.b))) :=
  (sliceTraitGaloisModel D N cN hcN hNj hNi).galoisLayer
    (sliceTraitGaloisResidue D N cN hcN hNj hNi) D.compositumSep

/-- The morphism of models `N' ⟶ N₁_{L^sep}` from the slice to the Galois layer: the identity of
total spaces and the purely inseparable part `r₁` on generic fibres. -/
noncomputable abbrev sliceTraitToGaloisLayer :
    (sliceTraitModel D N cN).toGeneric.Hom (sliceTraitGaloisLayer D N cN hcN hNj hNi)
      (sliceTraitGeneric D N cN hcN hNj) (𝟙 _) :=
  (sliceTraitGenericHom D N cN hcN hNj hNi).toTraitChangeGaloisLayer D.Ω
    (sliceTraitStructure D N cN) (pullback.snd _ _) q g hNj.w (sliceTrait_fst_comp D N cN hcN)
    (isPullback_sliceTraitModel_j D N cN).w (hNj.lift_snd _ _ _)

/-- The pullback exchange of `N' ⟶ N₁_{L^sep}` is invertible: it is the identity of total spaces
and the universal homeomorphism `r₁ : Spec Ω' ⟶ Spec L^sep`, base changed, on generic fibres. -/
theorem isIso_pullbackExchange_sliceTraitToGaloisLayer
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic))) :
    IsIso (((sliceTraitToGaloisLayer D N cN hcN hNj hNi).pullbackExchange Λ).app C) := by
  have : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  have : Algebra.IsAlgebraic D.R D.Ω := D.isAlgebraic_a
  have : IsUniversalHomeomorphism (sliceTraitToGaloisLayer D N cN hcN hNj hNi).generic :=
    (sliceTraitGenericHom D N cN hcN hNj hNi).isUniversalHomeomorphism_traitChangeInsepMap
      (sliceTrait_fst_comp D N cN hcN) (isPullback_sliceTraitModel_j D N cN) hNj
      (hNj.lift_snd _ _ _)
  exact Hom.isIso_pullbackExchange_app_of_isUniversalHomeomorphism_of_eq Λ
    (sliceTraitGaloisLayer D N cN hcN hNj hNi) (sliceTraitToGaloisLayer D N cN hcN hNj hNi).generic
    (sliceTraitModel D N cN).toGeneric
    (by
      have hj : (sliceTraitModel D N cN).j = (sliceTraitToGaloisLayer D N cN hcN hNj hNi).generic ≫
          (sliceTraitGaloisLayer D N cN hcN hNj hNi).j := by
        simpa using (sliceTraitToGaloisLayer D N cN hcN hNj hNi).comm_j.symm
      exact congrArg (fun j ↦ (⟨(sliceTraitModel D N cN).total, (sliceTraitModel D N cN).generic,
        j, (sliceTraitModel D N cN).i, 𝟙 _⟩ : NearbyCyclesModel _ _)) hj)
    (sliceTraitToGaloisLayer D N cN hcN hNj hNi) HEq.rfl HEq.rfl C

/-- The first components of the purely inseparable part `r₁`: `r₁ ≫ q ≫ r₂` is the change of
generic fibres of the cartesian model. -/
@[reassoc]
lemma sliceTraitToGaloisLayer_generic_fst_fst :
    (sliceTraitToGaloisLayer D N cN hcN hNj hNi).generic ≫
        pullback.fst (sliceTraitGaloisResidue D N cN hcN hNj hNi)
          (Spec.map (CommRingCat.ofHom (algebraMap D.compositum D.compositumSep))) ≫
        pullback.fst ((sliceTraitGenericHom D N cN hcN hNj hNi).cartesianModelTensor
          (sliceTraitStructure D N cN) q g hNj.w (sliceTrait_fst_comp D N cN hcN))
          (traitTensorCompositumPoint R D.R Ω D.Ω) =
      (sliceTraitGenericHom D N cN hcN hNj hNi).toCartesian.generic :=
  (sliceTraitGenericHom D N cN hcN hNj hNi).traitChangeInsepMap_comp_traitChangeGaloisMap_comp
    hNj.w (sliceTrait_fst_comp D N cN hcN) (isPullback_sliceTraitModel_j D N cN).w
    (hNj.lift_snd _ _ _)

/-- The component of `r₁` in `Spec L`. -/
@[reassoc]
lemma sliceTraitToGaloisLayer_generic_fst_snd :
    (sliceTraitToGaloisLayer D N cN hcN hNj hNi).generic ≫
        pullback.fst (sliceTraitGaloisResidue D N cN hcN hNj hNi)
          (Spec.map (CommRingCat.ofHom (algebraMap D.compositum D.compositumSep))) ≫
        pullback.snd ((sliceTraitGenericHom D N cN hcN hNj hNi).cartesianModelTensor
          (sliceTraitStructure D N cN) q g hNj.w (sliceTrait_fst_comp D N cN hcN))
          (traitTensorCompositumPoint R D.R Ω D.Ω) =
      pullback.snd _ _ ≫ traitTensorSepPoint D.R Ω D.Ω ≫ traitTensorCompositumGalois D.R Ω D.Ω :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

/-- The component of `r₁` in `Spec L^sep`. -/
@[reassoc]
lemma sliceTraitToGaloisLayer_generic_snd :
    (sliceTraitToGaloisLayer D N cN hcN hNj hNi).generic ≫
        pullback.snd (sliceTraitGaloisResidue D N cN hcN hNj hNi)
          (Spec.map (CommRingCat.ofHom (algebraMap D.compositum D.compositumSep))) =
      pullback.snd _ _ ≫ traitTensorSepPoint D.R Ω D.Ω :=
  pullback.lift_snd _ _ _

end Single

section Pair

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂) (hc : c.comp (algebraMap R₁ Ω₁) = (algebraMap R₂ Ω₂).comp ι)
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')
  (cN : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁))) {q₁ : N.total ⟶ Spec (.of R₁)}
  (hcN : cN ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
  {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁))))
  {p₁ : Y' ⟶ Spec (.of κ₁)} (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
  (cM : M.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂))) {q₂ : M.total ⟶ Spec (.of R₂)}
  (hcM' : cM ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₂)) ↘ Spec (.of R₂) = q₂)
  {g₂ : M.generic ⟶ Spec (.of Ω₂)}
  (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom (algebraMap R₂ Ω₂))))
  {p₂ : X' ⟶ Spec (.of κ₂)} (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
  (hcM : cM ≫ AffineSpace.map _ (Spec.map (CommRingCat.ofHom ι)) = φ.total ≫ cN)
  (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))

/-- The map of the generic fibres of the cartesian models of the slices,
`𝒳_{M,η̄} ×_{𝒳_M} M' ⟶ 𝒳_{N,η̄} ×_{𝒳_N} N'`. -/
noncomputable def sliceTraitCartesianGenericMap :
    (sliceTraitGenericHom D₂ M cM hcM' hMj hMi).cartesianModel.generic ⟶
      (sliceTraitGenericHom D₁ N cN hcN hNj hNi).cartesianModel.generic :=
  pullback.map _ _ _ _ φ.generic (sliceTraitChangeTotal H φ cN cM hcM) φ.total φ.comm_j.symm
    (sliceTraitChangeTotal_fst H φ cN cM hcM).symm

@[reassoc (attr := simp)]
lemma sliceTraitCartesianGenericMap_fst :
    sliceTraitCartesianGenericMap H φ cN hcN hNj hNi cM hcM' hMj hMi hcM ≫
        pullback.fst N.j (sliceTraitHom D₁ N cN hcN hNj hNi).total =
      pullback.fst M.j (sliceTraitHom D₂ M cM hcM' hMj hMi).total ≫ φ.generic :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceTraitCartesianGenericMap_snd :
    sliceTraitCartesianGenericMap H φ cN hcN hNj hNi cM hcM' hMj hMi hcM ≫
        pullback.snd N.j (sliceTraitHom D₁ N cN hcN hNj hNi).total =
      pullback.snd M.j (sliceTraitHom D₂ M cM hcM' hMj hMi).total ≫
        sliceTraitChangeTotal H φ cN cM hcM :=
  pullback.lift_snd _ _ _

include hgen in
/-- The map of the generic fibres of the cartesian models of the slices lies over the map
`Spec(Ω₂ ⊗_{R₂} S₂(x)) ⟶ Spec(Ω₁ ⊗_{R₁} S₁(x))`. -/
@[reassoc]
lemma cartesianModelTensor_comp_tensorSpecMap :
    (sliceTraitGenericHom D₂ M cM hcM' hMj hMi).cartesianModelTensor
        (sliceTraitStructure D₂ M cM) q₂ g₂ hMj.w (sliceTrait_fst_comp D₂ M cM hcM') ≫
        H.tensorSpecMap hc =
      sliceTraitCartesianGenericMap H φ cN hcN hNj hNi cM hcM' hMj hMi hcM ≫
        (sliceTraitGenericHom D₁ N cN hcN hNj hNi).cartesianModelTensor
          (sliceTraitStructure D₁ N cN) q₁ g₁ hNj.w (sliceTrait_fst_comp D₁ N cN hcN) := by
  apply (isPullback_traitTensor R₁ D₁.R Ω₁).hom_ext
  · simp only [Category.assoc, SliceTrait.Hom.tensorSpecMap_fst, Hom.cartesianModelTensor_fst,
      Hom.cartesianModelTensor_fst_assoc, sliceTraitCartesianGenericMap_fst_assoc, hgen]
  · simp only [Category.assoc, SliceTrait.Hom.tensorSpecMap_snd, Hom.cartesianModelTensor_snd,
      Hom.cartesianModelTensor_snd_assoc, sliceTraitCartesianGenericMap_snd_assoc,
      sliceTraitChangeTotal_snd]

include hgen in
/-- The map `Z₂(M) ⟶ Z₂(N)` of the generic fibres of the models `N₂`, `N₁`. -/
noncomputable def sliceTraitGaloisGenericMap :
    (sliceTraitGaloisModel D₂ M cM hcM' hMj hMi).generic ⟶
      (sliceTraitGaloisModel D₁ N cN hcN hNj hNi).generic :=
  pullback.map _ _ _ _ (sliceTraitCartesianGenericMap H φ cN hcN hNj hNi cM hcM' hMj hMi hcM)
    (Spec.map (CommRingCat.ofHom H.compositumMap)) (H.tensorSpecMap hc)
    (cartesianModelTensor_comp_tensorSpecMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)
    (H.compositumPoint_comp_tensorSpecMap hc)

include hgen in
@[reassoc (attr := simp)]
lemma sliceTraitGaloisGenericMap_fst :
    sliceTraitGaloisGenericMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen ≫
        pullback.fst _ _ =
      pullback.fst _ _ ≫ sliceTraitCartesianGenericMap H φ cN hcN hNj hNi cM hcM' hMj hMi hcM :=
  pullback.lift_fst _ _ _

include hgen in
@[reassoc (attr := simp)]
lemma sliceTraitGaloisGenericMap_snd :
    sliceTraitGaloisGenericMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen ≫
        pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom H.compositumMap) :=
  pullback.lift_snd _ _ _

include hgen in
/-- **The change of trait `τ : N₂ ⟶ N₁` of the models of the Galois layers of the slices**, over
`φ.generic` and the map of special fibres of the slices: the change of trait of the slices on
total spaces and `sliceTraitGaloisGenericMap` on generic fibres. -/
@[simps]
noncomputable def sliceTraitGaloisChangeHom :
    (sliceTraitGaloisModel D₂ M cM hcM' hMj hMi).Hom (sliceTraitGaloisModel D₁ N cN hcN hNj hNi)
      φ.generic (sliceTraitChangeSpecial H φ cN cM hcM) where
  total := sliceTraitChangeTotal H φ cN cM hcM
  generic := sliceTraitGaloisGenericMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen
  comm_j := by
    simp only [Hom.traitChangeModel_j, Hom.traitChangeThickening, Category.assoc,
      sliceTraitGaloisGenericMap_fst_assoc]
    erw [sliceTraitCartesianGenericMap_snd]
    rfl
  comm_i := (sliceTraitChangeHom H φ cN cM hcM).comm_i
  comm_ε := by
    simp only [Hom.traitChangeModel_ε, Hom.traitChangeThickening, Category.assoc,
      sliceTraitGaloisGenericMap_fst_assoc]
    erw [sliceTraitCartesianGenericMap_fst_assoc]
    rfl

include hgen in
/-- `τ` lies over `Spec l : Spec L₂ ⟶ Spec L₁`. -/
lemma sliceTraitGaloisChangeHom_generic_comp_residue :
    (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen).generic ≫
        sliceTraitGaloisResidue D₁ N cN hcN hNj hNi =
      sliceTraitGaloisResidue D₂ M cM hcM' hMj hMi ≫
        Spec.map (CommRingCat.ofHom H.compositumMap) :=
  sliceTraitGaloisGenericMap_snd H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen

include hgen in
/-- **The change of Galois layers** `τ' : N₂_{L₂^sep} ⟶ N₁_{L₁^sep}` induced by `τ` and the map
`ω : L₁^sep ⟶ L₂^sep` of separable closures (`NearbyCyclesModel.galoisLayerMap`). -/
noncomputable abbrev sliceTraitGaloisLayerMap :
    (sliceTraitGaloisLayer D₂ M cM hcM' hMj hMi).Hom (sliceTraitGaloisLayer D₁ N cN hcN hNj hNi)
      φ.generic (sliceTraitChangeSpecial H φ cN cM hcM) :=
  galoisLayerMap D₁.compositumSep D₂.compositumSep H.compositumSepMap
    H.compositumSepMap_comp_algebraMap
    (sliceTraitGaloisChangeHom H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)
    (sliceTraitGaloisChangeHom_generic_comp_residue H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen)

include hgen in
/-- The slices commute with the change of trait on geometric generic fibres:
`φ'.generic ≫ σ_N.generic = σ_M.generic ≫ φ.generic`. -/
@[reassoc]
lemma sliceTraitChangeGeneric_comp_sliceTraitGeneric :
    sliceTraitChangeGeneric H φ cN cM hcM ≫ sliceTraitGeneric D₁ N cN hcN hNj =
      sliceTraitGeneric D₂ M cM hcM' hMj ≫ φ.generic := by
  apply hNj.hom_ext
  · simp only [Category.assoc, sliceTraitGeneric, IsPullback.lift_fst, φ.comm_j,
      IsPullback.lift_fst_assoc]
    simp [sliceTraitChangeGeneric]
  · simp only [Category.assoc, sliceTraitGeneric, IsPullback.lift_snd, hgen,
      IsPullback.lift_snd_assoc]
    rw [sliceTraitChangeGeneric_snd_assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, H.ΩMap_comp_ωS]

include hgen in
/-- The square of generic fibres of the second square: `φ'.generic ≫ r₁(N) = r₁(M) ≫ τ'.generic`. -/
lemma sliceTraitChangeGeneric_comp_toGaloisLayer_generic :
    sliceTraitChangeGeneric H φ cN cM hcM ≫
        (sliceTraitToGaloisLayer D₁ N cN hcN hNj hNi).generic =
      (sliceTraitToGaloisLayer D₂ M cM hcM' hMj hMi).generic ≫
        (sliceTraitGaloisLayerMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen).generic := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, sliceTraitToGaloisLayer_generic_fst_fst_assoc,
          galoisLayerMap_generic, galoisLayerGenericMap_fst_assoc,
          sliceTraitGaloisChangeHom_generic, sliceTraitGaloisGenericMap_fst_assoc,
          sliceTraitCartesianGenericMap_fst,
          sliceTraitToGaloisLayer_generic_fst_fst_assoc, Hom.toCartesian_generic,
          pullback.lift_fst_assoc, pullback.lift_fst]
        exact sliceTraitChangeGeneric_comp_sliceTraitGeneric H φ cN hcN hNj cM hcM' hMj hcM hgen
      · simp only [Category.assoc, sliceTraitToGaloisLayer_generic_fst_fst_assoc,
          galoisLayerMap_generic, galoisLayerGenericMap_fst_assoc,
          sliceTraitGaloisChangeHom_generic, sliceTraitGaloisGenericMap_fst_assoc,
          sliceTraitCartesianGenericMap_snd,
          sliceTraitToGaloisLayer_generic_fst_fst_assoc, Hom.toCartesian_generic,
          pullback.lift_snd_assoc, pullback.lift_snd]
        exact (sliceTraitChangeHom H φ cN cM hcM).comm_j
    · simp only [Category.assoc, sliceTraitToGaloisLayer_generic_fst_snd_assoc,
        galoisLayerMap_generic, galoisLayerGenericMap_fst_assoc, sliceTraitGaloisChangeHom_generic,
        sliceTraitGaloisGenericMap_snd, sliceTraitToGaloisLayer_generic_fst_snd]
      rw [sliceTraitChangeGeneric_snd_assoc, H.sepPoint_comp_assoc, H.compositumGalois_comp]
  · simp only [Category.assoc, sliceTraitToGaloisLayer_generic_snd_assoc, galoisLayerMap_generic,
      galoisLayerGenericMap_snd, sliceTraitToGaloisLayer_generic_snd]
    rw [sliceTraitChangeGeneric_snd_assoc, H.sepPoint_comp]

include hgen in
/-- **The change of Galois layers from the change of trait of the slices** (SGA 4½,
[Th. finitude], proof of 3.7): the square `ρ_N ∘ φ' = τ' ∘ ρ_M` of morphisms of models, whose
vertical sides `ρ` (identity on total spaces, universal homeomorphisms on generic fibres) have
invertible pullback exchanges, shows that the exchange of the change of Galois layers `τ'` is
invertible at `C` once the change of trait `φ'` of the slices is invertible at the restriction
of `C`. -/
theorem isIso_pullbackExchange_sliceTraitGaloisLayerMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj Λ N.generic)))
    (hIH : IsIso (((sliceTraitChangeHom H φ cN cM hcM).toGeneric.pullbackExchange Λ).app
      (L((sliceTraitGeneric D₁ N cN hcN hNj)^*⟦Λ⟧).obj C))) :
    IsIso (((sliceTraitGaloisLayerMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM
      hgen).pullbackExchange Λ).app C) := by
  have key := Hom.isIso_map_pullbackExchange_app_of_square_of_isIso Λ
    (sliceTraitChangeHom H φ cN cM hcM).toGeneric (sliceTraitToGaloisLayer D₁ N cN hcN hNj hNi)
    (sliceTraitToGaloisLayer D₂ M cM hcM' hMj hMi)
    (sliceTraitGaloisLayerMap H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM hgen) (by simp)
    (sliceTraitChangeGeneric_comp_toGaloisLayer_generic H hc φ cN hcN hNj hNi cM hcM' hMj hMi hcM
      hgen)
    (sliceTraitChangeGeneric_comp_sliceTraitGeneric H φ cN hcN hNj cM hcM' hMj hcM hgen)
    (by simp) C (isIso_pullbackExchange_sliceTraitToGaloisLayer D₁ N cN hcN hNj hNi Λ C)
    (isIso_pullbackExchange_sliceTraitToGaloisLayer D₂ M cM hcM' hMj hMi Λ _) hIH
  exact (NatIso.isIso_map_iff (leftDerivedUpperStarId Λ _) _).mp key

end Pair

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
