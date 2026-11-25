/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionGalois
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethFormula
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGaloisLayer

/-!

# Functoriality of the slices over a generic slice trait

Let `φ₁ : P ⟶ M` be a morphism of models of finite type over `S = Spec k'⟦t⟧`, `b` a coordinate of
`M`, so that `φ₁ ≫ b` is a coordinate of `P`, and `D` a generic slice trait `S'` of `𝔸¹_S`. This
file constructs the morphisms induced by `φ₁` between the constructions of
`WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsionGalois`:

* the morphism `P_{S'} ⟶ M_{S'}` of the slices over `S'`
  (`NearbyCyclesModel.coordinateSliceTraitMap`), compatible with the slices
  `σ : M_{S'} ⟶ M` (`NearbyCyclesModel.coordinateSliceTraitMapGeneric_comp`,
  `NearbyCyclesModel.coordinateSliceTraitMapSpecial_comp`);
* the morphism `P₁ ⟶ M₁` of the models of the Galois layers
  (`NearbyCyclesModel.coordinateSliceGaloisMap`), lying over the identity of `Spec L`
  (`NearbyCyclesModel.coordinateSliceGaloisMap_generic_comp_residue`), with the change of Galois
  layers `P₁^{L^sep} ⟶ M₁^{L^sep}` compatible with the morphisms `ρ` from the slices
  (`NearbyCyclesModel.coordinateSliceTraitMapGeneric_comp_toGaloisLayer_generic`).

These are the first projections of the product configurations through which the generic-slicing
step of Gabber's Künneth formula descends along the Galois layer (blueprint
`proposition-external-kunneth-formula-nearby-cycles`, projection formula (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped TensorProduct CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme GenericSliceTrait

attribute [local instance] GenericSliceTrait.algebraR GenericSliceTrait.algebraΩ
  GenericSliceTrait.algebraBaseΩ GenericSliceTrait.algebraRΩ

variable {k' : Type u} [Field k'] {X Z : Scheme.{u}} {X' Z' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} (φ₁ : P.Hom M f₁ f₁') {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (hP : P.IsTraitModelOver (φ₁.total ≫ q) (φ₁.generic ≫ g))
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

/-! ### The morphism of the slices over the generic slice trait -/

/-- The morphism `𝒵 ×_{𝔸¹_S} S' ⟶ 𝒳 ×_{𝔸¹_S} S'` of the total spaces of the slices. -/
noncomputable abbrev coordinateSliceTraitMapTotal :
    pullback (φ₁.total ≫ b) D.toAffineLine ⟶ pullback b D.toAffineLine :=
  pullback.map _ _ _ _ φ₁.total (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The morphism of the generic fibres of the slices. -/
noncomputable abbrev coordinateSliceTraitMapGeneric :
    pullback (pullback.snd (φ₁.total ≫ b) D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)) ⟶
      pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)) :=
  pullback.map _ _ _ _ (coordinateSliceTraitMapTotal φ₁ b D) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The morphism of the special fibres of the slices. -/
noncomputable abbrev coordinateSliceTraitMapSpecial :
    pullback (pullback.snd (φ₁.total ≫ b) D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b)) ⟶
      pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b)) :=
  pullback.map _ _ _ _ (coordinateSliceTraitMapTotal φ₁ b D) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- **The morphism of the slices over the generic slice trait** `P_{S'} ⟶ M_{S'}` induced by
`φ₁`, on the models of the geometric generic fibres. -/
@[simps]
noncomputable def coordinateSliceTraitMap :
    (coordinateSliceTraitModel (φ₁.total ≫ b) D).Hom (coordinateSliceTraitModel b D)
      (coordinateSliceTraitMapGeneric φ₁ b D) (coordinateSliceTraitMapSpecial φ₁ b D) where
  total := coordinateSliceTraitMapTotal φ₁ b D
  generic := coordinateSliceTraitMapGeneric φ₁ b D
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

/-- The morphism of the slices commutes with the slices on generic fibres. -/
lemma coordinateSliceTraitMapGeneric_comp :
    coordinateSliceTraitMapGeneric φ₁ b D ≫ coordinateSliceTraitGeneric hM b hb D =
      coordinateSliceTraitGeneric hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb) D ≫
        φ₁.generic := by
  refine hM.isPullback_j.hom_ext ?_ ?_
  · simp [coordinateSliceTraitGeneric, φ₁.comm_j]
  · simp only [coordinateSliceTraitGeneric, Category.assoc, IsPullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]

include hM hP in
/-- The special fibre map of `φ₁` lies over `Spec k'`. -/
lemma special_comp_hom_eq : f₁' ≫ X'.hom = Z'.hom := by
  rw [← cancel_mono (traitClosedPoint k'), Category.assoc, ← hM.isPullback_i.w,
    reassoc_of% φ₁.comm_i, hP.isPullback_i.w]

/-- The morphism of the slices commutes with the slices on special fibres. -/
lemma coordinateSliceTraitMapSpecial_comp :
    coordinateSliceTraitMapSpecial φ₁ b D ≫ coordinateSliceTraitSpecial hM b hb D =
      coordinateSliceTraitSpecial hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb) D ≫
        f₁' := by
  refine hM.isPullback_i.hom_ext ?_ ?_
  · simp [coordinateSliceTraitSpecial, φ₁.comm_i]
  · simp only [coordinateSliceTraitSpecial, Category.assoc, IsPullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id, special_comp_hom_eq φ₁ hM hP]

/-! ### The morphism of the models of the Galois layers -/

/-- The morphism of the generic fibres `𝒵_η̄ ×_𝒵 P_{S'} ⟶ 𝒳_η̄ ×_𝒳 M_{S'}` of the cartesian
models of the slices. -/
noncomputable def coordinateSliceCartesianGenericMap :
    (coordinateSliceTraitHom hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb)
      D).cartesianModel.generic ⟶
      (coordinateSliceTraitHom hM b hb D).cartesianModel.generic :=
  pullback.map _ _ _ _ φ₁.generic (coordinateSliceTraitMapTotal φ₁ b D) φ₁.total φ₁.comm_j.symm
    (by simp)

@[reassoc (attr := simp)]
lemma coordinateSliceCartesianGenericMap_fst :
    coordinateSliceCartesianGenericMap φ₁ hM hP b hb D ≫
        pullback.fst M.j (coordinateSliceTraitHom hM b hb D).total =
      pullback.fst P.j (coordinateSliceTraitHom hP (φ₁.total ≫ b)
        (comp_coordinate_fst (φ₁ := φ₁) hb) D).total ≫ φ₁.generic :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma coordinateSliceCartesianGenericMap_snd :
    coordinateSliceCartesianGenericMap φ₁ hM hP b hb D ≫
        pullback.snd M.j (coordinateSliceTraitHom hM b hb D).total =
      pullback.snd P.j (coordinateSliceTraitHom hP (φ₁.total ≫ b)
        (comp_coordinate_fst (φ₁ := φ₁) hb) D).total ≫ coordinateSliceTraitMapTotal φ₁ b D :=
  pullback.lift_snd _ _ _

/-- The map of the generic fibres of the cartesian models of the slices lies over
`T = Spec(Ω ⊗_{k'⟦t⟧} R)`. -/
lemma cartesianModelTensor_coordinateSliceCartesianGenericMap :
    (coordinateSliceTraitHom hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb)
        D).cartesianModelTensor
        (pullback.snd (φ₁.total ≫ b) D.toAffineLine) (φ₁.total ≫ q) (φ₁.generic ≫ g)
        hP.isPullback_j.w (coordinateSliceTraitHom_total_comp hP (φ₁.total ≫ b)
          (comp_coordinate_fst (φ₁ := φ₁) hb) D) =
      coordinateSliceCartesianGenericMap φ₁ hM hP b hb D ≫
        (coordinateSliceTraitHom hM b hb D).cartesianModelTensor (pullback.snd b D.toAffineLine) q g
          hM.isPullback_j.w (coordinateSliceTraitHom_total_comp hM b hb D) := by
  apply (isPullback_traitTensor (PowerSeries k') D.R (traitGenericField k')).hom_ext
  · simp
  · simp

/-- The map `Z₂(P) ⟶ Z₂(M)` of the generic fibres of the models `P₁`, `M₁`. -/
noncomputable def coordinateSliceGaloisGenericMap :
    (coordinateSliceGaloisModel hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb) D).generic ⟶
      (coordinateSliceGaloisModel hM b hb D).generic :=
  pullback.map _ _ _ _ (coordinateSliceCartesianGenericMap φ₁ hM hP b hb D) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, cartesianModelTensor_coordinateSliceCartesianGenericMap]) (by simp)

@[reassoc (attr := simp)]
lemma coordinateSliceGaloisGenericMap_fst :
    coordinateSliceGaloisGenericMap φ₁ hM hP b hb D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ coordinateSliceCartesianGenericMap φ₁ hM hP b hb D :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma coordinateSliceGaloisGenericMap_snd :
    coordinateSliceGaloisGenericMap φ₁ hM hP b hb D ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [coordinateSliceGaloisGenericMap]

/-- **The morphism `P₁ ⟶ M₁` of the models of the Galois layers** induced by `φ₁`, over
`φ₁.generic` and the map of the special fibres of the slices. -/
@[simps]
noncomputable def coordinateSliceGaloisMap :
    (coordinateSliceGaloisModel hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb) D).Hom
      (coordinateSliceGaloisModel hM b hb D) φ₁.generic
      (coordinateSliceTraitMapSpecial φ₁ b D) where
  total := coordinateSliceTraitMapTotal φ₁ b D
  generic := coordinateSliceGaloisGenericMap φ₁ hM hP b hb D
  comm_j := by
    simp only [Hom.traitChangeModel_j, Hom.traitChangeThickening, Category.assoc,
      coordinateSliceGaloisGenericMap_fst_assoc, Hom.cartesianModel_j]
    exact congrArg (pullback.fst _ _ ≫ ·) (coordinateSliceCartesianGenericMap_snd φ₁ hM hP b hb D)
  comm_i := pullback.lift_fst _ _ _
  comm_ε := by
    simp only [Hom.traitChangeModel_ε, Hom.traitChangeThickening, Category.assoc,
      coordinateSliceGaloisGenericMap_fst_assoc, Hom.cartesianModel_ε,
      Category.comp_id]
    exact congrArg (pullback.fst _ _ ≫ ·) (coordinateSliceCartesianGenericMap_fst φ₁ hM hP b hb D)

/-- The morphism `P₁ ⟶ M₁` lies over the identity of `Spec L`. -/
lemma coordinateSliceGaloisMap_generic_comp_residue :
    (coordinateSliceGaloisMap φ₁ hM hP b hb D).generic ≫ coordinateSliceGaloisResidue hM b hb D =
      coordinateSliceGaloisResidue hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb) D ≫
        Spec.map (CommRingCat.ofHom
          (RingHom.id (traitTensorCompositum D.R (traitGenericField k') D.Ω))) := by
  simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, coordinateSliceGaloisMap_generic]
  exact coordinateSliceGaloisGenericMap_snd φ₁ hM hP b hb D

/-- The change of Galois layers `P₁^{L^sep} ⟶ M₁^{L^sep}` induced by `P₁ ⟶ M₁`. -/
noncomputable abbrev coordinateSliceGaloisLayerMap :=
  galoisLayerFst (coordinateSliceGaloisMap φ₁ hM hP b hb D)
    (coordinateSliceGaloisMap_generic_comp_residue φ₁ hM hP b hb D)
    (traitTensorCompositumSep D.R (traitGenericField k') D.Ω)

/-- **The morphisms `ρ` from the slices to the Galois layers commute with the morphisms induced by
`φ₁`**, on generic fibres. -/
lemma coordinateSliceTraitMapGeneric_comp_toGaloisLayer_generic :
    coordinateSliceTraitMapGeneric φ₁ b D ≫ (coordinateSliceToGaloisLayer hM b hb D).generic =
      (coordinateSliceToGaloisLayer hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb)
        D).generic ≫ (coordinateSliceGaloisLayerMap φ₁ hM hP b hb D).generic := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, coordinateSliceToGaloisLayer_generic_fst_fst_assoc,
          galoisLayerMap_generic, galoisLayerGenericMap_fst_assoc,
          coordinateSliceGaloisMap_generic, coordinateSliceGaloisGenericMap_fst_assoc,
          coordinateSliceCartesianGenericMap_fst, Hom.toCartesian_generic,
          pullback.lift_fst_assoc, pullback.lift_fst]
        exact coordinateSliceTraitMapGeneric_comp φ₁ hM hP b hb D
      · simp only [Category.assoc, coordinateSliceToGaloisLayer_generic_fst_fst_assoc,
          galoisLayerMap_generic, galoisLayerGenericMap_fst_assoc,
          coordinateSliceGaloisMap_generic, coordinateSliceGaloisGenericMap_fst_assoc,
          coordinateSliceCartesianGenericMap_snd, Hom.toCartesian_generic,
          pullback.lift_snd_assoc, pullback.lift_snd]
        exact (coordinateSliceTraitMap φ₁ b D).comm_j
    · simp only [Category.assoc,
        galoisLayerMap_generic, galoisLayerGenericMap_fst_assoc, coordinateSliceGaloisMap_generic,
        coordinateSliceGaloisGenericMap_snd, coordinateSliceToGaloisLayer_generic_fst_snd]
      simp [coordinateSliceTraitMapGeneric]
  · simp only [Category.assoc, coordinateSliceToGaloisLayer_generic_snd_assoc,
      galoisLayerMap_generic, galoisLayerGenericMap_snd, coordinateSliceToGaloisLayer_generic_snd]
    simp [coordinateSliceTraitMapGeneric]

/-- The morphisms `ψ : M₁ ⟶ M` commute with the morphisms induced by `φ₁`, on generic fibres. -/
lemma coordinateSliceGaloisMap_generic_comp_galoisModelHom_generic :
    (coordinateSliceGaloisMap φ₁ hM hP b hb D).generic ≫
        (coordinateSliceGaloisModelHom hM b hb D).generic =
      (coordinateSliceGaloisModelHom hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb)
        D).generic ≫ φ₁.generic := by
  simp only [Hom.comp_generic, Hom.traitChangeModelHom_generic, Hom.traitChangeThickening,
    Hom.fromCartesian_generic, coordinateSliceGaloisMap_generic, Category.assoc,
    coordinateSliceGaloisGenericMap_fst_assoc]
  exact congrArg (pullback.fst _ _ ≫ ·) (coordinateSliceCartesianGenericMap_fst φ₁ hM hP b hb D)

/-- The morphisms `ψ : M₁ ⟶ M` commute with the morphisms induced by `φ₁`, on total spaces. -/
lemma coordinateSliceGaloisMap_total_comp_galoisModelHom_total :
    (coordinateSliceGaloisMap φ₁ hM hP b hb D).total ≫
        (coordinateSliceGaloisModelHom hM b hb D).total =
      (coordinateSliceGaloisModelHom hP (φ₁.total ≫ b) (comp_coordinate_fst (φ₁ := φ₁) hb)
        D).total ≫ φ₁.total := by
  simp

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
