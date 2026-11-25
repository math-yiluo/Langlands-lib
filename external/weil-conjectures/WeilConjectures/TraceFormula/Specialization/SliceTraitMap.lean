/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitGaloisLayer
public import WeilConjectures.TraceFormula.Specialization.SliceTraitExists
public import WeilConjectures.TraceFormula.Specialization.SliceTraitFunctoriality

/-!

# Maps of slice traits along a change of trait

Let `S₂ = Spec R₂ ⟶ S₁ = Spec R₁` be a map of strictly henselian traits, given by an injective
local homomorphism `ι : R₁ →+* R₂`, with compatible geometric generic points `a₁ : R₁ ⟶ Ω₁`,
`a₂ : R₂ ⟶ Ω₂` (`c : Ω₁ ⟶ Ω₂`). To compare the slices of a model over the two traits
(SGA 4½, [Th. finitude], 3.7), Deligne uses the morphism `S₂(x) ⟶ S₁(x)` between the strict
localizations of `𝔸¹_{S₂}` and `𝔸¹_{S₁}` at the geometric points over the generic points of their
special fibres. This file constructs it, together with a compatible map of geometric generic
points.

## Main results

- `AlgebraicGeometry.SliceTrait.exists_comp_a_eq`: **extension of geometric generic points**. For
  a slice trait `D` over `S₁` (with `Ω₁` algebraic over `R₁`), any pair of maps `α : R ⟶ Ω₂`,
  `β : Ω₁ ⟶ Ω₂` into an algebraically closed field, compatible over `R₁`, extends to
  `γ : Ω' ⟶ Ω₂`. Indeed `Spec(Ω₁ ⊗_{R₁} R)` is a single point
  (`AlgebraicGeometry.SliceTrait.subsingleton_primeSpectrum`), so the product maps
  `Ω₁ ⊗_{R₁} R ⟶ Ω'` and `Ω₁ ⊗_{R₁} R ⟶ Ω₂` have the same kernel; hence the second factors through
  the compositum `L = Ω₁(R) ⊆ Ω'`, and `L ⟶ Ω₂` extends to the algebraic extension `Ω' / L`.
- `AlgebraicGeometry.SliceTrait.Hom`: a morphism `S'₂ ⟶ S'₁` of slice traits over `S₂ ⟶ S₁`,
  given by a local injective ring map `ψ : R'₁ ⟶ R'₂` over `𝔸¹_{S₂} ⟶ 𝔸¹_{S₁}`, with compatible
  maps of closed and geometric generic points.
- `AlgebraicGeometry.sliceTraitOfStrictLocalizationHom`: the morphism `S₂(x) ⟶ S₁(x)` of
  strict-localization slice traits, given by `AlgebraicGeometry.sliceTraitMap`, with
  `AlgebraicGeometry.exists_sliceTraitOfStrictLocalization_map` providing the map of geometric
  generic points.

-/

@[expose] public section

universe u v

open CategoryTheory IsLocalRing

open scoped TensorProduct

namespace AlgebraicGeometry.SliceTrait

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)

/-- **Extension of geometric generic points of a slice trait**: let `D` be a slice trait over
`S₁ = Spec R₁` with `a₁ : R₁ ⟶ Ω₁` injective and `Ω₁` algebraic over `R₁`. For an algebraically
closed field `Ω₂` and ring maps `α : R ⟶ Ω₂`, `β : Ω₁ ⟶ Ω₂` agreeing on `R₁`, there is
`γ : Ω' ⟶ Ω₂` restricting to `α` on `R` and to `β` on `Ω₁`. Since `Spec(Ω₁ ⊗_{R₁} R)` is a point,
the product map `Ω₁ ⊗_{R₁} R ⟶ Ω₂` has the same kernel as the one to `Ω'`, so it factors through
the compositum `L = Ω₁(R) ⊆ Ω'`, over which `Ω'` is algebraic. -/
theorem exists_comp_a_eq (ha₁ : Function.Injective a₁)
    (halg : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
    {Ω₂ : Type v} [Field Ω₂] [IsAlgClosed Ω₂] (α : D.R →+* Ω₂) (β : Ω₁ →+* Ω₂)
    (h : α.comp D.φ = β.comp a₁) :
    ∃ γ : D.Ω →+* Ω₂, γ.comp D.a = α ∧ γ.comp D.ωS = β := by
  let := D.φ.toAlgebra
  let := a₁.toAlgebra
  let := D.a.toAlgebra
  let := D.ωS.toAlgebra
  let : Algebra R₁ D.Ω := (D.a.comp D.φ).toAlgebra
  have : IsScalarTower R₁ D.R D.Ω := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₁ Ω₁ D.Ω := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun D.ωS_comp x).symm
  have : FaithfulSMul D.R D.Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 D.injective_a
  have : Algebra.IsAlgebraic D.R D.Ω := D.isAlgebraic_a
  have := D.subsingleton_primeSpectrum ha₁ halg
  let : Algebra D.R Ω₂ := α.toAlgebra
  let : Algebra Ω₁ Ω₂ := β.toAlgebra
  let : Algebra R₁ Ω₂ := (α.comp D.φ).toAlgebra
  have : IsScalarTower R₁ D.R Ω₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₁ Ω₁ Ω₂ := IsScalarTower.of_algebraMap_eq fun x ↦
    RingHom.congr_fun h x
  let g : Ω₁ ⊗[R₁] D.R →+* Ω₂ := (Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom R₁ Ω₁ Ω₂) (IsScalarTower.toAlgHom R₁ D.R Ω₂)).toRingHom
  let e := traitTensorToCompositum R₁ D.R Ω₁ D.Ω
  have hker : RingHom.ker e = RingHom.ker g := congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨_, RingHom.ker_isPrime e⟩ : PrimeSpectrum _) ⟨_, RingHom.ker_isPrime g⟩)
  let δ := e.liftOfSurjective (surjective_traitTensorToCompositum R₁ D.R Ω₁ D.Ω) ⟨g, hker.le⟩
  have hδ : δ.comp e = g := e.liftOfSurjective_comp _ _
  let : Algebra (traitTensorCompositum D.R Ω₁ D.Ω) Ω₂ := δ.toAlgebra
  let γ : D.Ω →+* Ω₂ := (IsAlgClosed.lift (R := traitTensorCompositum D.R Ω₁ D.Ω) (S := D.Ω)
    (M := Ω₂)).toRingHom
  have hγ (t : Ω₁ ⊗[R₁] D.R) : γ (traitTensorLift R₁ D.R Ω₁ D.Ω t) = g t := by
    rw [← RingHom.congr_fun hδ t]
    exact (IsAlgClosed.lift (R := traitTensorCompositum D.R Ω₁ D.Ω) (S := D.Ω)
      (M := Ω₂)).commutes (e t)
  refine ⟨γ, RingHom.ext fun r ↦ ?_, RingHom.ext fun ω ↦ ?_⟩
  · have := hγ (1 ⊗ₜ r)
    rw [traitTensorLift_tmul, map_one, one_mul] at this
    exact this.trans ((Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
      (by rw [map_one, one_mul]; rfl))
  · have := hγ (ω ⊗ₜ 1)
    rw [traitTensorLift_tmul, map_one, mul_one] at this
    exact this.trans ((Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
      (by rw [map_one, mul_one]; rfl))

end AlgebraicGeometry.SliceTrait

namespace AlgebraicGeometry

open Scheme

/-- A **morphism of slice traits** `S'₂ ⟶ S'₁` over a change of trait `S₂ = Spec R₂ ⟶ S₁ = Spec R₁`
given by `ι : R₁ ⟶ R₂`, with `c : Ω₁ ⟶ Ω₂` on geometric generic points: a local injective ring map
`ψ : R'₁ ⟶ R'₂` such that `S'₂ ⟶ S'₁` lies over `𝔸¹_{S₂} ⟶ 𝔸¹_{S₁}` and over `S₂ ⟶ S₁`, with
compatible maps `κ'₁ ⟶ κ'₂` of closed points and `Ω'₁ ⟶ Ω'₂` of geometric generic points (the
latter also compatible with `c`). The strict localizations give one
(`AlgebraicGeometry.sliceTraitOfStrictLocalizationHom`): the map `S₂(x) ⟶ S₁(x)` of SGA 4½,
[Th. finitude], 3.7, used to compare slices over the two traits. -/
structure SliceTrait.Hom {R₁ R₂ : Type u} [CommRing R₁] [IsLocalRing R₁] [CommRing R₂]
    [IsLocalRing R₂] (ι : R₁ →+* R₂) {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] (c : Ω₁ →+* Ω₂)
    {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {κ₁ κ₂ : Type u} [Field κ₁] [Field κ₂] {b₁ : R₁ →+* κ₁}
    {b₂ : R₂ →+* κ₂} (D₁ : SliceTrait a₁ b₁) (D₂ : SliceTrait a₂ b₂) where
  /-- the ring map `R'₁ ⟶ R'₂`. -/
  ψ : D₁.R →+* D₂.R
  /-- `S'₂ ⟶ S'₁` lies over `𝔸¹_{S₂} ⟶ 𝔸¹_{S₁}`. -/
  spec_ψ : Spec.map (CommRingCat.ofHom ψ) ≫ D₁.toAffineLine = D₂.toAffineLine ≫ affineLineMap ι
  /-- `S'₂ ⟶ S'₁` lies over `S₂ ⟶ S₁`. -/
  ψ_comp_φ : ψ.comp D₁.φ = D₂.φ.comp ι
  [isLocalHom_ψ : IsLocalHom ψ]
  /-- `ψ` is injective. -/
  injective_ψ : Function.Injective ψ
  /-- the map `κ'₁ ⟶ κ'₂` of closed points. -/
  κMap : D₁.κ →+* D₂.κ
  /-- `ψ` is compatible with the closed points. -/
  b_comp_ψ : D₂.b.comp ψ = κMap.comp D₁.b
  /-- the map `Ω'₁ ⟶ Ω'₂` of geometric generic points. -/
  ΩMap : D₁.Ω →+* D₂.Ω
  /-- `ψ` is compatible with the geometric generic points of `S'₁` and `S'₂`. -/
  ΩMap_comp_a : ΩMap.comp D₁.a = D₂.a.comp ψ
  /-- the map of geometric generic points is compatible with `c : Ω₁ ⟶ Ω₂`. -/
  ΩMap_comp_ωS : ΩMap.comp D₁.ωS = D₂.ωS.comp c

attribute [instance] SliceTrait.Hom.isLocalHom_ψ

variable {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] (ι : R₁ →+* R₂) [IsLocalHom ι] (hι : Function.Injective ι)
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] (c : Ω₁ →+* Ω₂)
  {a₁ : R₁ →+* Ω₁} (ha₁ : Function.Injective a₁)
  (halg₁ : letI := a₁.toAlgebra; Algebra.IsAlgebraic R₁ Ω₁)
  {a₂ : R₂ →+* Ω₂} (ha₂ : Function.Injective a₂)
  (halg₂ : letI := a₂.toAlgebra; Algebra.IsAlgebraic R₂ Ω₂)
  (hc : c.comp a₁ = a₂.comp ι)
  {κ₂ : Type u} [Field κ₂] {b₂ : R₂ →+* κ₂} (hb₂ : RingHom.ker b₂ = maximalIdeal R₂)

/-- `sliceTraitMap ι b₂ : S₂(x) ⟶ S₁(x)` lies over `𝔸¹_{S₂} ⟶ 𝔸¹_{S₁}`. -/
lemma spec_sliceTraitMap_comp_toAffineLine :
    Spec.map (CommRingCat.ofHom (sliceTraitMap ι b₂)) ≫
        (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).toAffineLine =
      (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).toAffineLine ≫
        affineLineMap ι :=
  spec_sliceTraitMap_comp_strictLocalizationToBase ι b₂

/-- `sliceTraitMap ι b₂ : S₂(x) ⟶ S₁(x)` lies over `S₂ ⟶ S₁`. -/
lemma sliceTraitMap_comp_φ :
    (sliceTraitMap ι b₂).comp
        (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).φ =
      (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).φ.comp ι :=
  sliceTraitMap_comp_sliceTraitStructureMap ι b₂

/-- `sliceTraitMap ι b₂` is compatible with the closed points of `S₁(x)` and `S₂(x)`, both with
field `traitSliceField κ₂`. -/
lemma b_comp_sliceTraitMap :
    (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).b.comp
        (sliceTraitMap ι b₂) =
      (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).b :=
  strictHenselizationEval_comp_sliceTraitMap ι b₂

include hc in
/-- **The map of geometric generic points of the strict-localization slice traits**: an embedding
`Ω'₁ ⟶ Ω'₂` extending `sliceTraitMap ι b₂ : R'₁ ⟶ R'₂` and compatible with `c : Ω₁ ⟶ Ω₂`
(`AlgebraicGeometry.SliceTrait.exists_comp_a_eq`). -/
theorem exists_sliceTraitOfStrictLocalization_map :
    ∃ γ : (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).Ω →+*
        (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).Ω,
      γ.comp (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).a =
        (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).a.comp
          (sliceTraitMap ι b₂) ∧
      γ.comp (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
          (ker_comp_eq_maximalIdeal ι b₂ hb₂)).ωS =
        (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂).ωS.comp c := by
  set D₁ := sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
    (ker_comp_eq_maximalIdeal ι b₂ hb₂)
  set D₂ := sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂
  refine D₁.exists_comp_a_eq ha₁ halg₁ (D₂.a.comp (sliceTraitMap ι b₂)) (D₂.ωS.comp c) ?_
  rw [RingHom.comp_assoc, sliceTraitMap_comp_φ ι ha₁ halg₁ ha₂ halg₂ hb₂, RingHom.comp_assoc,
    hc, ← RingHom.comp_assoc, ← RingHom.comp_assoc, D₂.ωS_comp]

/-- **The morphism `S₂(x) ⟶ S₁(x)` of strict-localization slice traits** along the change of trait
`S₂ ⟶ S₁` (SGA 4½, [Th. finitude], 3.7): the strict localization `S₂(x)` of `𝔸¹_{S₂}` at the
geometric point over the generic point of its special fibre maps to that of `𝔸¹_{S₁}` (at the image
geometric point) by `sliceTraitMap ι b₂`, which is local and injective, with the identity of
`traitSliceField κ₂` on closed points and a compatible map of geometric generic points. -/
noncomputable def sliceTraitOfStrictLocalizationHom :
    SliceTrait.Hom ι c
      (sliceTraitOfStrictLocalization (a₁ := a₁) (b₁ := b₂.comp ι) ha₁ halg₁
        (ker_comp_eq_maximalIdeal ι b₂ hb₂))
      (sliceTraitOfStrictLocalization (a₁ := a₂) (b₁ := b₂) ha₂ halg₂ hb₂) where
  ψ := sliceTraitMap ι b₂
  spec_ψ := spec_sliceTraitMap_comp_toAffineLine ι ha₁ halg₁ ha₂ halg₂ hb₂
  ψ_comp_φ := sliceTraitMap_comp_φ ι ha₁ halg₁ ha₂ halg₂ hb₂
  isLocalHom_ψ := isLocalHom_sliceTraitMap ι b₂
  injective_ψ := injective_sliceTraitMap ι b₂ hι hb₂
  κMap := RingHom.id _
  b_comp_ψ := b_comp_sliceTraitMap ι ha₁ halg₁ ha₂ halg₂ hb₂
  ΩMap := (exists_sliceTraitOfStrictLocalization_map ι c ha₁ halg₁ ha₂ halg₂ hc hb₂).choose
  ΩMap_comp_a :=
    (exists_sliceTraitOfStrictLocalization_map ι c ha₁ halg₁ ha₂ halg₂ hc hb₂).choose_spec.1
  ΩMap_comp_ωS :=
    (exists_sliceTraitOfStrictLocalization_map ι c ha₁ halg₁ ha₂ halg₂ hc hb₂).choose_spec.2

/-- The ring map of `sliceTraitOfStrictLocalizationHom` is `sliceTraitMap ι b₂`. -/
lemma sliceTraitOfStrictLocalizationHom_ψ :
    (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂).ψ =
      sliceTraitMap ι b₂ :=
  rfl

/-- The map of closed points of `sliceTraitOfStrictLocalizationHom` is the identity of
`traitSliceField κ₂`. -/
lemma sliceTraitOfStrictLocalizationHom_κMap :
    (sliceTraitOfStrictLocalizationHom ι hι c ha₁ halg₁ ha₂ halg₂ hc hb₂).κMap =
      RingHom.id (traitSliceField κ₂) :=
  rfl

end AlgebraicGeometry
