/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisCompositum

/-!

# The compositum of the geometric generic points of two traits

Let `R₁ ⟶ R` be a ring map, `Ω₁` a field over `R₁` and `Ω` an algebraically closed field over
`R` and `Ω₁`, compatibly over `R₁` (typically: `R₁ ⟶ R` a map of traits and `Ω₁`, `Ω` their
geometric generic points). Put `T = Ω₁ ⊗_{R₁} R`.

* `Spec T` is the fibre product `Spec Ω₁ ×_{Spec R₁} Spec R`
  (`AlgebraicGeometry.isPullback_traitTensor`).
* The product map `T ⟶ Ω` (`AlgebraicGeometry.traitTensorLift`) takes values in the compositum
  `L = Ω₁(R) ⊆ Ω` (`AlgebraicGeometry.traitTensorCompositum`); when `Spec T` has at most one point,
  `T ⟶ L` is surjective (`AlgebraicGeometry.surjective_traitTensorToCompositum`), so `L` is the
  residue field of the point of `Spec T`.
* Consequently `ρ : Spec Ω ⟶ Spec T` factors as `Spec Ω ⟶ Spec L^sep ⟶ Spec L ⟶ Spec T`
  (`AlgebraicGeometry.traitTensorSepPoint_comp_traitTensorCompositumGalois_comp`) with
  `L^sep` the separable closure of `L` in `Ω`: the first factor is a universal homeomorphism
  (`Ω / L^sep` is purely inseparable), the middle one is the spectrum of the Galois extension
  `L^sep / L` and the last one is a closed immersion and a universal homeomorphism when `Spec T` is
  a point (`AlgebraicGeometry.isUniversalHomeomorphism_traitTensorCompositumPoint`).

This generalises `AlgebraicGeometry.traitGenericSpecMap_factor` (the case `R₁ = k'⟦t⟧`,
`R = K⟦t⟧`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IntermediateField

open scoped TensorProduct

namespace AlgebraicGeometry

variable (R₁ R Ω₁ Ω : Type u) [CommRing R₁] [CommRing R] [Algebra R₁ R] [Field Ω₁]
  [Algebra R₁ Ω₁] [Field Ω] [Algebra R Ω] [Algebra Ω₁ Ω] [Algebra R₁ Ω]
  [IsScalarTower R₁ R Ω] [IsScalarTower R₁ Ω₁ Ω]

/-- The product map `Ω₁ ⊗_{R₁} R ⟶ Ω`, `ω ⊗ r ↦ ω·r`. -/
noncomputable def traitTensorLift : Ω₁ ⊗[R₁] R →ₐ[R₁] Ω :=
  Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R₁ Ω₁ Ω)
    (IsScalarTower.toAlgHom R₁ R Ω)

variable {R₁ R Ω₁ Ω} in
/-- The product map on pure tensors. -/
lemma traitTensorLift_tmul (ω : Ω₁) (r : R) :
    traitTensorLift R₁ R Ω₁ Ω (ω ⊗ₜ r) = algebraMap Ω₁ Ω ω * algebraMap R Ω r :=
  rfl

/-- The compositum `L = Ω₁(R)` of `Ω₁` and the image of `R` in `Ω`. -/
noncomputable def traitTensorCompositum : IntermediateField Ω₁ Ω :=
  adjoin Ω₁ (Set.range (algebraMap R Ω))

/-- The product map `Ω₁ ⊗_{R₁} R ⟶ Ω` takes values in the compositum `Ω₁(R)`. -/
lemma traitTensorLift_mem_traitTensorCompositum (x : Ω₁ ⊗[R₁] R) :
    traitTensorLift R₁ R Ω₁ Ω x ∈ traitTensorCompositum R Ω₁ Ω := by
  induction x using TensorProduct.inductionOn with
  | tmul ω r =>
    rw [traitTensorLift_tmul]
    exact mul_mem (IntermediateField.algebraMap_mem _ ω) (subset_adjoin _ _ ⟨r, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- The map `Ω₁ ⊗_{R₁} R ⟶ L = Ω₁(R)`, the corestriction of the product map. -/
noncomputable def traitTensorToCompositum : Ω₁ ⊗[R₁] R →+* traitTensorCompositum R Ω₁ Ω :=
  (traitTensorLift R₁ R Ω₁ Ω).toRingHom.codRestrict _
    (traitTensorLift_mem_traitTensorCompositum R₁ R Ω₁ Ω)

/-- **The product map onto the compositum is surjective when `Spec(Ω₁ ⊗_{R₁} R)` has at most one
point**: its kernel is then the unique prime ideal, which is maximal, so its image is a subfield
of `Ω` containing `Ω₁` and the image of `R`. -/
theorem surjective_traitTensorToCompositum [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))] :
    Function.Surjective (traitTensorToCompositum R₁ R Ω₁ Ω) := by
  let f := (traitTensorLift R₁ R Ω₁ Ω).toRingHom
  have hunit (y : Ω₁ ⊗[R₁] R) (hy : f y ≠ 0) : IsUnit y := by
    by_contra hy'
    obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal (Ideal.span {y})
      (Ideal.span_singleton_ne_top hy')
    have hMk : M = RingHom.ker f := congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (⟨M, hM.isPrime⟩ : PrimeSpectrum _) ⟨_, RingHom.ker_isPrime f⟩)
    exact hy (RingHom.mem_ker.mp (hMk ▸ hyM (Ideal.mem_span_singleton_self y)))
  let T : Subalgebra Ω₁ Ω :=
    { f.range with
      algebraMap_mem' := fun a ↦
        ⟨a ⊗ₜ 1, (traitTensorLift_tmul a 1).trans (by rw [map_one, mul_one])⟩ }
  let I : IntermediateField Ω₁ Ω := T.toIntermediateField fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hx
    by_cases hy : f y = 0
    · rw [hy, inv_zero]
      exact zero_mem T
    · exact ⟨↑(hunit y hy).unit⁻¹, by
        rw [← mul_eq_one_iff_eq_inv₀ hy, ← map_mul, IsUnit.val_inv_mul, map_one]⟩
  have hle : traitTensorCompositum R Ω₁ Ω ≤ I := by
    refine adjoin_le_iff.mpr ?_
    rintro _ ⟨r, rfl⟩
    exact ⟨1 ⊗ₜ r, (traitTensorLift_tmul 1 r).trans (by rw [map_one, one_mul])⟩
  rintro ⟨z, hz⟩
  obtain ⟨y, hy⟩ := hle hz
  exact ⟨y, Subtype.ext hy⟩

/-- The separable closure `L^sep` of the compositum `L = Ω₁(R)` in `Ω`. -/
noncomputable abbrev traitTensorCompositumSep :
    IntermediateField (traitTensorCompositum R Ω₁ Ω) Ω :=
  separableClosure (traitTensorCompositum R Ω₁ Ω) Ω

/-- If `Ω` is algebraic over `R` (with `R ⟶ Ω` injective), it is algebraic over the compositum
`L = Ω₁(R)`, which contains the image of `R`. -/
instance [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] :
    Algebra.IsAlgebraic (traitTensorCompositum R Ω₁ Ω) Ω :=
  Algebra.IsAlgebraic.ringHom_of_comp_eq
    ((algebraMap R Ω).codRestrict (traitTensorCompositum R Ω₁ Ω)
      fun r ↦ subset_adjoin _ _ ⟨r, rfl⟩) (RingHom.id Ω)
    (fun _ _ h ↦ FaithfulSMul.algebraMap_injective R Ω (congrArg Subtype.val h))
    Function.surjective_id rfl

/-- `L^sep / L` is Galois. -/
instance [IsAlgClosed Ω] [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] :
    IsGalois (traitTensorCompositum R Ω₁ Ω) (traitTensorCompositumSep R Ω₁ Ω) :=
  have : IsAlgClosure (traitTensorCompositum R Ω₁ Ω) Ω := ⟨inferInstance, inferInstance⟩
  inferInstance

/-- The ring `Ω₁ ⊗_{R₁} R`. -/
noncomputable abbrev traitTensor : CommRingCat.{u} :=
  .of (Ω₁ ⊗[R₁] R)

/-- The map `Spec(Ω₁ ⊗_{R₁} R) ⟶ Spec Ω₁` of the first factor. -/
noncomputable def traitTensorFst : Spec (traitTensor R₁ R Ω₁) ⟶ Spec (.of Ω₁) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The map `Spec(Ω₁ ⊗_{R₁} R) ⟶ Spec R` of the second factor. -/
noncomputable def traitTensorSnd : Spec (traitTensor R₁ R Ω₁) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- **`Spec(Ω₁ ⊗_{R₁} R)` is the fibre product `Spec Ω₁ ×_{Spec R₁} Spec R`.** -/
theorem isPullback_traitTensor :
    IsPullback (traitTensorFst R₁ R Ω₁) (traitTensorSnd R₁ R Ω₁)
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ Ω₁)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ R))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R₁ Ω₁ R)

/-- The morphism `ρ : Spec Ω ⟶ Spec(Ω₁ ⊗_{R₁} R)` of the product map. -/
noncomputable def traitTensorPoint : Spec (.of Ω) ⟶ Spec (traitTensor R₁ R Ω₁) :=
  Spec.map (CommRingCat.ofHom (traitTensorLift R₁ R Ω₁ Ω).toRingHom)

/-- `ρ` lies over `Spec Ω ⟶ Spec Ω₁`. -/
@[reassoc (attr := simp)]
lemma traitTensorPoint_fst :
    traitTensorPoint R₁ R Ω₁ Ω ≫ traitTensorFst R₁ R Ω₁ =
      Spec.map (CommRingCat.ofHom (algebraMap Ω₁ Ω)) := by
  rw [traitTensorPoint, traitTensorFst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext ω
  exact (traitTensorLift_tmul ω 1).trans (by rw [map_one, mul_one])

/-- `ρ` lies over `Spec Ω ⟶ Spec R`. -/
@[reassoc (attr := simp)]
lemma traitTensorPoint_snd :
    traitTensorPoint R₁ R Ω₁ Ω ≫ traitTensorSnd R₁ R Ω₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
  rw [traitTensorPoint, traitTensorSnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact (traitTensorLift_tmul 1 r).trans (by rw [map_one, one_mul])

/-- The morphism `Spec Ω ⟶ Spec L^sep`. -/
noncomputable def traitTensorSepPoint :
    Spec (.of Ω) ⟶ Spec (.of (traitTensorCompositumSep R Ω₁ Ω)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

/-- The morphism `Spec L^sep ⟶ Spec L` of the Galois extension `L^sep / L`. -/
noncomputable def traitTensorCompositumGalois :
    Spec (.of (traitTensorCompositumSep R Ω₁ Ω)) ⟶ Spec (.of (traitTensorCompositum R Ω₁ Ω)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (traitTensorCompositum R Ω₁ Ω)
    (traitTensorCompositumSep R Ω₁ Ω)))

/-- The morphism `Spec L ⟶ Spec(Ω₁ ⊗_{R₁} R)` of the corestricted product map. -/
noncomputable def traitTensorCompositumPoint :
    Spec (.of (traitTensorCompositum R Ω₁ Ω)) ⟶ Spec (traitTensor R₁ R Ω₁) :=
  Spec.map (CommRingCat.ofHom (traitTensorToCompositum R₁ R Ω₁ Ω))

/-- **The factorisation of `ρ`**: `Spec Ω ⟶ Spec L^sep ⟶ Spec L ⟶ Spec(Ω₁ ⊗_{R₁} R)`. -/
@[reassoc]
theorem traitTensorSepPoint_comp_traitTensorCompositumGalois_comp :
    traitTensorSepPoint R Ω₁ Ω ≫ traitTensorCompositumGalois R Ω₁ Ω ≫
      traitTensorCompositumPoint R₁ R Ω₁ Ω = traitTensorPoint R₁ R Ω₁ Ω := by
  rw [traitTensorSepPoint, traitTensorCompositumGalois, traitTensorCompositumPoint,
    traitTensorPoint, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  rfl

/-- `Spec Ω ⟶ Spec L^sep` is a universal homeomorphism: `Ω / L^sep` is purely inseparable. -/
instance [FaithfulSMul R Ω] [Algebra.IsAlgebraic R Ω] :
    IsUniversalHomeomorphism (traitTensorSepPoint R Ω₁ Ω) := by
  rw [traitTensorSepPoint]
  infer_instance

/-- `Spec L ⟶ Spec(Ω₁ ⊗_{R₁} R)` is a closed immersion when `Spec(Ω₁ ⊗_{R₁} R)` has at most one
point. -/
instance [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))] :
    IsClosedImmersion (traitTensorCompositumPoint R₁ R Ω₁ Ω) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_traitTensorToCompositum R₁ R Ω₁ Ω)

/-- **`Spec L ⟶ Spec(Ω₁ ⊗_{R₁} R)` is a universal homeomorphism** when `Spec(Ω₁ ⊗_{R₁} R)` has at
most one point: it is a surjective closed immersion. -/
instance isUniversalHomeomorphism_traitTensorCompositumPoint
    [Subsingleton (PrimeSpectrum (Ω₁ ⊗[R₁] R))] :
    IsUniversalHomeomorphism (traitTensorCompositumPoint R₁ R Ω₁ Ω) := by
  have : Subsingleton (Spec (traitTensor R₁ R Ω₁)) := ‹Subsingleton (PrimeSpectrum _)›
  have : Surjective (traitTensorCompositumPoint R₁ R Ω₁ Ω) :=
    ⟨fun x ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  infer_instance

end AlgebraicGeometry
