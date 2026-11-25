/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitMap
public import WeilConjectures.TraceFormula.Specialization.TraitTensorCompositum

/-!

# The compositum fields of a morphism of slice traits

Let `H : S₂(x) ⟶ S₁(x)` be a morphism of slice traits over a change of trait `ι : R₁ ⟶ R₂`
(`AlgebraicGeometry.SliceTrait.Hom`), with geometric generic points `Ω'ᵢ` of `Sᵢ(x)` over the
geometric generic points `Ωᵢ` of `Sᵢ`. The map `H.ΩMap : Ω'₁ ⟶ Ω'₂` restricts to the composita
`Lᵢ = Ωᵢ(Sᵢ(x)) ⊆ Ω'ᵢ` (`AlgebraicGeometry.SliceTrait.Hom.compositumMap`) and to their separable
closures `Lᵢ^sep` (`AlgebraicGeometry.SliceTrait.Hom.compositumSepMap`), compatibly with the maps
`Spec Lᵢ ⟶ Spec(Ωᵢ ⊗_{Rᵢ} Sᵢ(x))` (`AlgebraicGeometry.SliceTrait.Hom.compositumPoint_comp`).

The algebra structures of a slice trait are recorded as local instances
(`AlgebraicGeometry.SliceTrait.algebraR` etc.); the geometric generic point of the base is given
by an algebra structure `Algebra R₁ Ω₁`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing IntermediateField

open scoped TensorProduct

namespace AlgebraicGeometry.SliceTrait

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] [Algebra R₁ Ω₁]
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait (algebraMap R₁ Ω₁) b₁)

/-- The algebra structure `R₁ ⟶ R` of a slice trait. -/
abbrev algebraR : Algebra R₁ D.R := D.φ.toAlgebra

/-- The algebra structure `R ⟶ Ω'` of a slice trait. -/
abbrev algebraΩ : Algebra D.R D.Ω := D.a.toAlgebra

/-- The algebra structure `Ω₁ ⟶ Ω'` of a slice trait. -/
abbrev algebraBaseΩ : Algebra Ω₁ D.Ω := D.ωS.toAlgebra

/-- The algebra structure `R₁ ⟶ Ω'` of a slice trait. -/
abbrev algebraRΩ : Algebra R₁ D.Ω := (D.a.comp D.φ).toAlgebra

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

instance isScalarTower_R : IsScalarTower R₁ D.R D.Ω :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance isScalarTower_Ω : IsScalarTower R₁ Ω₁ D.Ω :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (RingHom.congr_fun D.ωS_comp x).symm

/-- The compositum `L = Ω₁(R) ⊆ Ω'` of a slice trait. -/
noncomputable abbrev compositum : IntermediateField Ω₁ D.Ω :=
  traitTensorCompositum D.R Ω₁ D.Ω

/-- The separable closure `L^sep ⊆ Ω'` of the compositum of a slice trait. -/
noncomputable abbrev compositumSep : IntermediateField D.compositum D.Ω :=
  traitTensorCompositumSep D.R Ω₁ D.Ω

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂)

/-- `H.ΩMap` maps the compositum `L₁ = Ω₁(S₁(x))` into `L₂ = Ω₂(S₂(x))`. -/
lemma ΩMap_mem_compositum (x : D₁.Ω) (hx : x ∈ D₁.compositum) : H.ΩMap x ∈ D₂.compositum := by
  have hle : D₁.compositum.toSubfield ≤ D₂.compositum.toSubfield.comap H.ΩMap := by
    rw [compositum, traitTensorCompositum, adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro _ (⟨ω, rfl⟩ | ⟨r, rfl⟩)
    · change H.ΩMap (D₁.ωS ω) ∈ D₂.compositum
      rw [← RingHom.comp_apply, H.ΩMap_comp_ωS, RingHom.comp_apply]
      exact IntermediateField.algebraMap_mem _ (c ω)
    · change H.ΩMap (D₁.a r) ∈ D₂.compositum
      rw [← RingHom.comp_apply, H.ΩMap_comp_a, RingHom.comp_apply]
      exact subset_adjoin _ _ ⟨H.ψ r, rfl⟩
  exact hle hx

/-- The map `l : L₁ ⟶ L₂` of composita induced by `H.ΩMap`. -/
noncomputable def compositumMap : D₁.compositum →+* D₂.compositum :=
  (H.ΩMap.comp D₁.compositum.val.toRingHom).codRestrict _ fun x ↦ H.ΩMap_mem_compositum x x.2

@[simp]
lemma coe_compositumMap (x : D₁.compositum) : (H.compositumMap x : D₂.Ω) = H.ΩMap x :=
  rfl

/-- `H.ΩMap` maps the separable closure `L₁^sep` into `L₂^sep`. -/
lemma ΩMap_mem_compositumSep (x : D₁.Ω) (hx : x ∈ D₁.compositumSep) :
    H.ΩMap x ∈ D₂.compositumSep := by
  rw [compositumSep, traitTensorCompositumSep, mem_separableClosure_iff] at hx ⊢
  have hroot : Polynomial.aeval (H.ΩMap x)
      ((minpoly D₁.compositum x).map H.compositumMap) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have h0 := minpoly.aeval D₁.compositum x
    rw [Polynomial.aeval_def] at h0
    rw [show (algebraMap D₂.compositum D₂.Ω).comp H.compositumMap =
        H.ΩMap.comp (algebraMap D₁.compositum D₁.Ω) from RingHom.ext fun _ ↦ rfl,
      ← Polynomial.hom_eval₂, h0, map_zero]
  exact (Polynomial.Separable.map hx).of_dvd (minpoly.dvd _ _ hroot)

/-- The map `ω : L₁^sep ⟶ L₂^sep` of separable closures induced by `H.ΩMap`. -/
noncomputable def compositumSepMap : D₁.compositumSep →+* D₂.compositumSep :=
  (H.ΩMap.comp D₁.compositumSep.val.toRingHom).codRestrict _ fun x ↦
    H.ΩMap_mem_compositumSep x x.2

@[simp]
lemma coe_compositumSepMap (x : D₁.compositumSep) :
    (H.compositumSepMap x : D₂.Ω) = H.ΩMap x :=
  rfl

/-- `ω` extends `l`. -/
lemma compositumSepMap_comp_algebraMap :
    H.compositumSepMap.comp (algebraMap D₁.compositum D₁.compositumSep) =
      (algebraMap D₂.compositum D₂.compositumSep).comp H.compositumMap :=
  RingHom.ext fun _ ↦ Subtype.ext rfl

end AlgebraicGeometry.SliceTrait.Hom

namespace AlgebraicGeometry.SliceTrait.Hom

attribute [local instance] algebraR algebraΩ algebraBaseΩ algebraRΩ

open Scheme

variable {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂] [IsLocalRing R₂]
  {ι : R₁ →+* R₂} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra R₁ Ω₁] [Algebra R₂ Ω₂]
  {c : Ω₁ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {D₁ : SliceTrait (algebraMap R₁ Ω₁) b₁} {D₂ : SliceTrait (algebraMap R₂ Ω₂) b₂}
  (H : SliceTrait.Hom ι c D₁ D₂) (hc : c.comp (algebraMap R₁ Ω₁) = (algebraMap R₂ Ω₂).comp ι)

/-- The morphism `Spec(Ω₂ ⊗_{R₂} S₂(x)) ⟶ Spec(Ω₁ ⊗_{R₁} S₁(x))` induced by `c` and `ψ`. -/
noncomputable def tensorSpecMap :
    Spec (traitTensor R₂ D₂.R Ω₂) ⟶ Spec (traitTensor R₁ D₁.R Ω₁) :=
  (isPullback_traitTensor R₁ D₁.R Ω₁).lift
    (traitTensorFst R₂ D₂.R Ω₂ ≫ Spec.map (CommRingCat.ofHom c))
    (traitTensorSnd R₂ D₂.R Ω₂ ≫ Spec.map (CommRingCat.ofHom H.ψ)) (by
      have h₁ : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)) =
          Spec.map (CommRingCat.ofHom (algebraMap R₂ Ω₂)) ≫
            Spec.map (CommRingCat.ofHom ι) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          hc]
      have h₂ : Spec.map (CommRingCat.ofHom H.ψ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R₁ D₁.R)) =
            Spec.map (CommRingCat.ofHom (algebraMap R₂ D₂.R)) ≫
              Spec.map (CommRingCat.ofHom ι) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) H.ψ_comp_φ
      rw [Category.assoc, Category.assoc, h₁, h₂, (isPullback_traitTensor R₂ D₂.R Ω₂).w_assoc])

@[reassoc (attr := simp)]
lemma tensorSpecMap_fst :
    H.tensorSpecMap hc ≫ traitTensorFst R₁ D₁.R Ω₁ =
      traitTensorFst R₂ D₂.R Ω₂ ≫ Spec.map (CommRingCat.ofHom c) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma tensorSpecMap_snd :
    H.tensorSpecMap hc ≫ traitTensorSnd R₁ D₁.R Ω₁ =
      traitTensorSnd R₂ D₂.R Ω₂ ≫ Spec.map (CommRingCat.ofHom H.ψ) :=
  IsPullback.lift_snd _ _ _ _

/-- The square of `Spec Lᵢ ⟶ Spec(Ωᵢ ⊗_{Rᵢ} Sᵢ(x))` and the maps induced by `H`. -/
@[reassoc]
lemma compositumPoint_comp_tensorSpecMap :
    traitTensorCompositumPoint R₂ D₂.R Ω₂ D₂.Ω ≫ H.tensorSpecMap hc =
      Spec.map (CommRingCat.ofHom H.compositumMap) ≫
        traitTensorCompositumPoint R₁ D₁.R Ω₁ D₁.Ω := by
  apply (isPullback_traitTensor R₁ D₁.R Ω₁).hom_ext
  · rw [Category.assoc, tensorSpecMap_fst, traitTensorCompositumPoint, traitTensorFst,
      traitTensorFst, Category.assoc, traitTensorCompositumPoint, ← Spec.map_comp,
      ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext ω
    simp only [RingHom.comp_apply, coe_compositumMap, traitTensorToCompositum,
      RingHom.codRestrict_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, traitTensorLift_tmul, map_one, mul_one]
    exact (RingHom.congr_fun H.ΩMap_comp_ωS ω).symm
  · rw [Category.assoc, tensorSpecMap_snd, traitTensorCompositumPoint, traitTensorSnd,
      traitTensorSnd, Category.assoc, traitTensorCompositumPoint, ← Spec.map_comp,
      ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp only [RingHom.comp_apply, coe_compositumMap, traitTensorToCompositum,
      RingHom.codRestrict_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, traitTensorLift_tmul, map_one, one_mul]
    exact (RingHom.congr_fun H.ΩMap_comp_a r).symm

/-- The square of `Spec L^sepᵢ ⟶ Spec Lᵢ` and the maps induced by `H`. -/
@[reassoc]
lemma compositumGalois_comp :
    Spec.map (CommRingCat.ofHom H.compositumSepMap) ≫
        traitTensorCompositumGalois D₁.R Ω₁ D₁.Ω =
      traitTensorCompositumGalois D₂.R Ω₂ D₂.Ω ≫ Spec.map (CommRingCat.ofHom H.compositumMap) := by
  rw [traitTensorCompositumGalois, traitTensorCompositumGalois, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, compositumSepMap_comp_algebraMap]

/-- The square of `Spec Ω'ᵢ ⟶ Spec L^sepᵢ` and the maps induced by `H`. -/
@[reassoc]
lemma sepPoint_comp :
    Spec.map (CommRingCat.ofHom H.ΩMap) ≫ traitTensorSepPoint D₁.R Ω₁ D₁.Ω =
      traitTensorSepPoint D₂.R Ω₂ D₂.Ω ≫ Spec.map (CommRingCat.ofHom H.compositumSepMap) := by
  rw [traitTensorSepPoint, traitTensorSepPoint, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

end AlgebraicGeometry.SliceTrait.Hom
