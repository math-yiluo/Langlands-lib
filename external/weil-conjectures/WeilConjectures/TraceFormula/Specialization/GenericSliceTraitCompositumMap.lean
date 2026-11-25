/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUnramified
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.SliceGaloisFields

/-!

# The compositum fields of the change of trait to a generic slice trait

Let `D` be a generic slice trait of `𝔸¹_S`, `S = Spec k'⟦t⟧`
(`AlgebraicGeometry.GenericSliceTrait`),
`S' = Spec R` its trait and `T = Spec K⟦t⟧` (`K = k'(x)^alg`), with the local injection
`ι : R ⟶ K⟦t⟧` and the embedding `ω_K : Ω' ⟶ Ω_K` of geometric generic points. Over the common
base `S`, with geometric generic point `Ω`, the composita are `L' = Ω(R) ⊆ Ω'`
(`AlgebraicGeometry.SliceTrait.compositum` of `D.toSliceTrait`) and `L_T = Ω(K⟦t⟧) ⊆ Ω_K`
(`AlgebraicGeometry.traitTensorCompositum (PowerSeries K) Ω Ω_K`). The map `ω_K` restricts to
`L' ⟶ L_T` (`AlgebraicGeometry.GenericSliceTrait.compositumMap`) and to the separable closures
`L'^sep ⟶ L_T^sep` (`AlgebraicGeometry.GenericSliceTrait.compositumSepMap`), compatibly with the
maps `Spec L ⟶ Spec(Ω ⊗_{k'⟦t⟧} -)` (`AlgebraicGeometry.GenericSliceTrait.tensorSpecMap`).

This mirrors `AlgebraicGeometry.SliceTrait.Hom.compositumMap` for morphisms of slice traits.
The maps `ι` and `ω_K` are restated with the types of `D.toSliceTrait`
(`AlgebraicGeometry.GenericSliceTrait.sliceι`, `AlgebraicGeometry.GenericSliceTrait.sliceωK`,
definitionally `D.ι` and `D.ωK`), so that rewriting does not need to unfold `D.toSliceTrait`.

The algebra structure `Ω ⟶ Ω_K` is recorded as the local instance
`AlgebraicGeometry.traitGenericFieldAlgebra`; the structures `k'⟦t⟧ ⟶ K⟦t⟧`
(`PowerSeries.algebraPowerSeries`), `K⟦t⟧ ⟶ Ω_K` and `k'⟦t⟧ ⟶ Ω_K` are the global instances.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing IntermediateField

open scoped TensorProduct

namespace AlgebraicGeometry

section TraitGenericFieldAlgebra

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The algebra structure `Ω ⟶ Ω_K` given by the embedding of the geometric generic points of the
traits (`AlgebraicGeometry.traitGenericFieldMap`). -/
noncomputable abbrev traitGenericFieldAlgebra :
    Algebra (traitGenericField k') (traitGenericField K) :=
  (traitGenericFieldMap k' K).toAlgebra

attribute [local instance] traitGenericFieldAlgebra

/-- The embedding `Ω ⟶ Ω_K` lies over the coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧`. -/
instance isScalarTower_traitGenericField :
    IsScalarTower (PowerSeries k') (traitGenericField k') (traitGenericField K) :=
  IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun (traitGenericFieldMap_comp_algebraMap k' K) x).symm

/-- `k'⟦t⟧ ⟶ K⟦t⟧ ⟶ Ω_K` is the structure map `k'⟦t⟧ ⟶ Ω_K`. -/
instance isScalarTower_powerSeries_traitGenericField :
    IsScalarTower (PowerSeries k') (PowerSeries K) (traitGenericField K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

end TraitGenericFieldAlgebra

namespace GenericSliceTrait

attribute [local instance] SliceTrait.algebraR SliceTrait.algebraΩ SliceTrait.algebraBaseΩ
  SliceTrait.algebraRΩ traitGenericFieldAlgebra

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')


/-- The local injection `ι : R ⟶ K⟦t⟧`, typed by the ring of the slice trait `D.toSliceTrait`. -/
noncomputable def sliceι : D.toSliceTrait.R →+* PowerSeries (traitSliceField k') :=
  D.ι

/-- The embedding `ω_K : Ω' ⟶ Ω_K`, typed by the field of the slice trait `D.toSliceTrait`. -/
noncomputable def sliceωK : D.toSliceTrait.Ω →+* traitGenericField (traitSliceField k') :=
  D.ωK

/-- `ι` restricts to the coefficientwise map on `k'⟦t⟧`
(`AlgebraicGeometry.GenericSliceTrait.ι_comp_φ`). -/
lemma sliceι_comp_φ :
    D.sliceι.comp D.toSliceTrait.φ = PowerSeries.map (algebraMap k' (traitSliceField k')) :=
  D.ι_comp_φ

/-- `ω_K` restricts to the fixed embedding `Ω ⟶ Ω_K` on `Ω`. -/
lemma sliceωK_comp_ωS :
    D.sliceωK.comp D.toSliceTrait.ωS = traitGenericFieldMap k' (traitSliceField k') :=
  D.ωK_comp_ωS

/-- `ω_K` lies over `ι : R ⟶ K⟦t⟧`. -/
lemma sliceωK_comp_a :
    D.sliceωK.comp D.toSliceTrait.a =
      (algebraMap _ (traitGenericField (traitSliceField k'))).comp D.sliceι :=
  D.ωK_comp_a

/-- `ω_K` maps the compositum `L' = Ω(R)` into `L_T = Ω(K⟦t⟧)`. -/
lemma sliceωK_mem_compositum (x : D.toSliceTrait.Ω) (hx : x ∈ D.toSliceTrait.compositum) :
    D.sliceωK x ∈ traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
      (traitGenericField (traitSliceField k')) := by
  have hle : D.toSliceTrait.compositum.toSubfield ≤
      (traitTensorCompositum (PowerSeries (traitSliceField k')) (traitGenericField k')
        (traitGenericField (traitSliceField k'))).toSubfield.comap D.sliceωK := by
    rw [SliceTrait.compositum, traitTensorCompositum, adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro _ (⟨ω, rfl⟩ | ⟨r, rfl⟩)
    · rw [SetLike.mem_coe, Subfield.mem_comap, RingHom.algebraMap_toAlgebra,
        ← RingHom.comp_apply, D.sliceωK_comp_ωS]
      exact IntermediateField.algebraMap_mem _ ω
    · rw [SetLike.mem_coe, Subfield.mem_comap, RingHom.algebraMap_toAlgebra,
        ← RingHom.comp_apply, D.sliceωK_comp_a, RingHom.comp_apply]
      exact subset_adjoin _ _ ⟨D.sliceι r, rfl⟩
  exact hle hx

/-- The map `l : L' ⟶ L_T` of composita induced by `ω_K`. -/
noncomputable def compositumMap :
    D.toSliceTrait.compositum →+* traitTensorCompositum (PowerSeries (traitSliceField k'))
      (traitGenericField k') (traitGenericField (traitSliceField k')) :=
  (D.sliceωK.comp D.toSliceTrait.compositum.val.toRingHom).codRestrict _ fun x ↦
    D.sliceωK_mem_compositum x x.2

/-- `l` is the restriction of `ω_K`. -/
@[simp]
lemma coe_compositumMap (x : D.toSliceTrait.compositum) :
    (D.compositumMap x : traitGenericField (traitSliceField k')) = D.sliceωK x :=
  rfl

/-- `ω_K` maps the separable closure `L'^sep` into `L_T^sep`. -/
lemma sliceωK_mem_compositumSep (x : D.toSliceTrait.Ω) (hx : x ∈ D.toSliceTrait.compositumSep) :
    D.sliceωK x ∈ traitTensorCompositumSep (PowerSeries (traitSliceField k'))
      (traitGenericField k') (traitGenericField (traitSliceField k')) := by
  rw [mem_separableClosure_iff] at hx ⊢
  have hroot : Polynomial.aeval (D.sliceωK x)
      ((minpoly D.toSliceTrait.compositum x).map D.compositumMap) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have h0 := minpoly.aeval D.toSliceTrait.compositum x
    rw [Polynomial.aeval_def] at h0
    rw [show (algebraMap _ (traitGenericField (traitSliceField k'))).comp D.compositumMap =
        D.sliceωK.comp (algebraMap D.toSliceTrait.compositum D.toSliceTrait.Ω) from
          RingHom.ext fun _ ↦ rfl,
      ← Polynomial.hom_eval₂, h0, map_zero]
  exact (Polynomial.Separable.map hx).of_dvd (minpoly.dvd _ _ hroot)

/-- The map `ω : L'^sep ⟶ L_T^sep` of separable closures induced by `ω_K`. -/
noncomputable def compositumSepMap :
    D.toSliceTrait.compositumSep →+* traitTensorCompositumSep (PowerSeries (traitSliceField k'))
      (traitGenericField k') (traitGenericField (traitSliceField k')) :=
  (D.sliceωK.comp D.toSliceTrait.compositumSep.val.toRingHom).codRestrict _ fun x ↦
    D.sliceωK_mem_compositumSep x x.2

/-- `ω` is the restriction of `ω_K`. -/
@[simp]
lemma coe_compositumSepMap (x : D.toSliceTrait.compositumSep) :
    (D.compositumSepMap x : traitGenericField (traitSliceField k')) = D.sliceωK x :=
  rfl

/-- `ω` extends `l`. -/
lemma compositumSepMap_comp_algebraMap :
    D.compositumSepMap.comp
        (algebraMap D.toSliceTrait.compositum D.toSliceTrait.compositumSep) =
      (algebraMap _ (traitTensorCompositumSep (PowerSeries (traitSliceField k'))
        (traitGenericField k') (traitGenericField (traitSliceField k')))).comp
        D.compositumMap :=
  RingHom.ext fun _ ↦ Subtype.ext rfl

/-- The morphism `Spec(Ω ⊗_{k'⟦t⟧} K⟦t⟧) ⟶ Spec(Ω ⊗_{k'⟦t⟧} R)` induced by `ι : R ⟶ K⟦t⟧`. -/
noncomputable def tensorSpecMap :
    Spec (traitTensor (PowerSeries k') (PowerSeries (traitSliceField k'))
        (traitGenericField k')) ⟶
      Spec (traitTensor (PowerSeries k') D.toSliceTrait.R (traitGenericField k')) :=
  (isPullback_traitTensor (PowerSeries k') D.toSliceTrait.R (traitGenericField k')).lift
    (traitTensorFst (PowerSeries k') (PowerSeries (traitSliceField k')) (traitGenericField k'))
    (traitTensorSnd (PowerSeries k') (PowerSeries (traitSliceField k')) (traitGenericField k') ≫
      Spec.map (CommRingCat.ofHom D.sliceι)) (by
      have h : Spec.map (CommRingCat.ofHom D.sliceι) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k') D.toSliceTrait.R)) =
            Spec.map (CommRingCat.ofHom
              (algebraMap (PowerSeries k') (PowerSeries (traitSliceField k')))) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) D.sliceι_comp_φ
      rw [Category.assoc, h, (isPullback_traitTensor (PowerSeries k')
        (PowerSeries (traitSliceField k')) (traitGenericField k')).w])

/-- The map `Spec(Ω ⊗ K⟦t⟧) ⟶ Spec(Ω ⊗ R)` lies over `Spec Ω`. -/
@[reassoc (attr := simp)]
lemma tensorSpecMap_fst :
    D.tensorSpecMap ≫ traitTensorFst (PowerSeries k') D.toSliceTrait.R (traitGenericField k') =
      traitTensorFst (PowerSeries k') (PowerSeries (traitSliceField k'))
        (traitGenericField k') :=
  IsPullback.lift_fst _ _ _ _

/-- The map `Spec(Ω ⊗ K⟦t⟧) ⟶ Spec(Ω ⊗ R)` lies over `Spec ι : Spec K⟦t⟧ ⟶ Spec R`. -/
@[reassoc (attr := simp)]
lemma tensorSpecMap_snd :
    D.tensorSpecMap ≫ traitTensorSnd (PowerSeries k') D.toSliceTrait.R (traitGenericField k') =
      traitTensorSnd (PowerSeries k') (PowerSeries (traitSliceField k')) (traitGenericField k') ≫
        Spec.map (CommRingCat.ofHom D.sliceι) :=
  IsPullback.lift_snd _ _ _ _

/-- The square of `Spec L ⟶ Spec(Ω ⊗_{k'⟦t⟧} -)` and the maps induced by `D`. -/
@[reassoc]
lemma compositumPoint_comp_tensorSpecMap :
    traitTensorCompositumPoint (PowerSeries k') (PowerSeries (traitSliceField k'))
        (traitGenericField k') (traitGenericField (traitSliceField k')) ≫ D.tensorSpecMap =
      Spec.map (CommRingCat.ofHom D.compositumMap) ≫
        traitTensorCompositumPoint (PowerSeries k') D.toSliceTrait.R (traitGenericField k')
          D.toSliceTrait.Ω := by
  apply (isPullback_traitTensor (PowerSeries k') D.toSliceTrait.R (traitGenericField k')).hom_ext
  · rw [Category.assoc, tensorSpecMap_fst, traitTensorCompositumPoint, traitTensorFst,
      traitTensorFst, Category.assoc, traitTensorCompositumPoint, ← Spec.map_comp,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext ω
    simp only [RingHom.comp_apply, coe_compositumMap, traitTensorToCompositum,
      RingHom.codRestrict_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, traitTensorLift_tmul, map_one, mul_one]
    exact (RingHom.congr_fun D.sliceωK_comp_ωS ω).symm
  · rw [Category.assoc, tensorSpecMap_snd, traitTensorCompositumPoint, traitTensorSnd,
      traitTensorSnd, Category.assoc, traitTensorCompositumPoint, ← Spec.map_comp,
      ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply, coe_compositumMap, traitTensorToCompositum,
      RingHom.codRestrict_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, traitTensorLift_tmul, map_one, one_mul]
    exact (RingHom.congr_fun D.sliceωK_comp_a r).symm

/-- The square of `Spec L^sep ⟶ Spec L` and the maps induced by `D`. -/
@[reassoc]
lemma compositumGalois_comp :
    Spec.map (CommRingCat.ofHom D.compositumSepMap) ≫
        traitTensorCompositumGalois D.toSliceTrait.R (traitGenericField k') D.toSliceTrait.Ω =
      traitTensorCompositumGalois (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        Spec.map (CommRingCat.ofHom D.compositumMap) := by
  rw [traitTensorCompositumGalois, traitTensorCompositumGalois, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, compositumSepMap_comp_algebraMap]

/-- The square of `Spec Ω_K ⟶ Spec L_T^sep`, `Spec Ω' ⟶ Spec L'^sep` and the maps induced by
`D`. -/
@[reassoc]
lemma sepPoint_comp :
    Spec.map (CommRingCat.ofHom D.sliceωK) ≫
        traitTensorSepPoint D.toSliceTrait.R (traitGenericField k') D.toSliceTrait.Ω =
      traitTensorSepPoint (PowerSeries (traitSliceField k')) (traitGenericField k')
          (traitGenericField (traitSliceField k')) ≫
        Spec.map (CommRingCat.ofHom D.compositumSepMap) := by
  rw [traitTensorSepPoint, traitTensorSepPoint, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

end GenericSliceTrait

end AlgebraicGeometry
