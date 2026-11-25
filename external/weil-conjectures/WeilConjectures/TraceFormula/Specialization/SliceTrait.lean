/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!

# Slice traits over a strictly henselian trait

Let `S₁ = Spec R₁` be a strictly henselian trait, with a geometric generic point `a₁ : R₁ ⟶ Ω₁`
and a separably closed point `b₁ : R₁ ⟶ κ₁`. Deligne's proof of the finiteness of nearby cycles
and of their invariance under change of trait (SGA 4½, [Th. finitude], 3.3–3.9) slices along the
strict localization `S₁(x)` of `𝔸¹_{S₁}` at a geometric point over the generic point of its
special fibre: a strictly henselian trait, weakly étale over `𝔸¹_{S₁}`, with the same
uniformizer as `S₁`.

`AlgebraicGeometry.SliceTrait a₁ b₁` packages such a trait `S' = Spec R` with the structure map
`φ : R₁ ⟶ R`, a geometric generic point `a : R ⟶ Ω'` with `Ω'` algebraic over `Frac R`, and a
separably closed point `b : R ⟶ κ'`, compatible with those of `S₁`. Besides the trait, it records
the two properties of the strict localization used to describe the change of generic fibres:
* `φ` maps a uniformizer of `R₁` to a uniformizer of `R`;
* every element of the residue field of `R` which is algebraic over that of `R₁` comes from it.

For a model `N` of `Y` over `S₁` with a map `c : 𝒳_N ⟶ 𝔸¹_{S₁}` over `S₁`, the base change
`X' = 𝒳_N ×_{𝔸¹_{S₁}} S'` is a model over `S'` (`NearbyCyclesModel.sliceTraitModel`), mapped to the
geometric model of `N` by the *slice* morphism of models `σ` (`NearbyCyclesModel.sliceTraitHom`),
whose morphism of total spaces is weakly étale.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

/-- A **slice trait** over the trait `S₁ = Spec R₁` with geometric generic point `a₁ : R₁ ⟶ Ω₁`
and separably closed point `b₁ : R₁ ⟶ κ₁`: a strictly henselian trait `S' = Spec R` with a weakly
étale morphism `S' ⟶ 𝔸¹_{S₁}` (structure map `φ : R₁ ⟶ R`), such that a uniformizer of `R₁` is one
of `R` and every element of the residue field of `R` algebraic over that of `R₁` comes from it,
together with a geometric generic point `a : R ⟶ Ω'` (`Ω'` algebraic over `R`) and a separably
closed point `b : R ⟶ κ'` compatible with those of `S₁`. The strict localization of `𝔸¹_{S₁}` at
a geometric point over the generic point of its special fibre is one
(`AlgebraicGeometry.nonempty_sliceTrait`). -/
structure SliceTrait {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁]
    (a₁ : R₁ →+* Ω₁) {κ₁ : Type u} [Field κ₁] (b₁ : R₁ →+* κ₁) where
  /-- the strictly henselian discrete valuation ring `R` of `S'`. -/
  R : Type u
  [commRing : CommRing R]
  [isDomain : IsDomain R]
  [isDiscreteValuationRing : IsDiscreteValuationRing R]
  [isStrictlyHenselianLocalRing : IsStrictlyHenselianLocalRing R]
  /-- the weakly étale morphism `S' ⟶ 𝔸¹_{S₁}`. -/
  toAffineLine : Spec (.of R) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁))
  weaklyEtale : WeaklyEtale toAffineLine
  /-- the structure map `R₁ ⟶ R`. -/
  φ : R₁ →+* R
  spec_φ : Spec.map (CommRingCat.ofHom φ) =
    toAffineLine ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁)
  [isLocalHom_φ : IsLocalHom φ]
  /-- a uniformizer of `R₁` is a uniformizer of `R`. -/
  maximalIdeal_eq : maximalIdeal R = (maximalIdeal R₁).map φ
  /-- the elements of the residue field of `R` algebraic over that of `R₁` come from it. -/
  mem_range_residueField : letI := (ResidueField.map φ).toAlgebra
    ∀ z : ResidueField R, IsAlgebraic (ResidueField R₁) z → z ∈ (ResidueField.map φ).range
  /-- the field `Ω'` of the geometric generic point of `S'`. -/
  Ω : Type u
  [field_Ω : Field Ω]
  [isAlgClosed : IsAlgClosed Ω]
  /-- the geometric generic point `R ⟶ Ω'`. -/
  a : R →+* Ω
  injective_a : Function.Injective a
  isAlgebraic_a : letI := a.toAlgebra; Algebra.IsAlgebraic R Ω
  /-- the embedding `Ω₁ ⟶ Ω'` of geometric generic points. -/
  ωS : Ω₁ →+* Ω
  ωS_comp : ωS.comp a₁ = a.comp φ
  /-- the field `κ'` of the closed point of `S'`. -/
  κ : Type u
  [field_κ : Field κ]
  [isSepClosed : IsSepClosed κ]
  /-- the closed point `R ⟶ κ'`. -/
  b : R →+* κ
  ker_b : RingHom.ker b = maximalIdeal R
  /-- the embedding `κ₁ ⟶ κ'` of closed points. -/
  κS : κ₁ →+* κ
  κS_comp : κS.comp b₁ = b.comp φ

namespace SliceTrait

attribute [instance] commRing isDomain isDiscreteValuationRing isStrictlyHenselianLocalRing
  isLocalHom_φ field_Ω isAlgClosed field_κ isSepClosed weaklyEtale

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)

/-- The geometric generic point of `S'` lies over that of `S₁`. -/
@[reassoc]
lemma spec_a_comp_toAffineLine :
    Spec.map (CommRingCat.ofHom D.a) ≫ D.toAffineLine ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) =
      Spec.map (CommRingCat.ofHom D.ωS) ≫ Spec.map (CommRingCat.ofHom a₁) := by
  rw [← D.spec_φ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, D.ωS_comp]

/-- The closed point of `S'` lies over that of `S₁`. -/
@[reassoc]
lemma spec_b_comp_toAffineLine :
    Spec.map (CommRingCat.ofHom D.b) ≫ D.toAffineLine ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) =
      Spec.map (CommRingCat.ofHom D.κS) ≫ Spec.map (CommRingCat.ofHom b₁) := by
  rw [← D.spec_φ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, D.κS_comp]

end SliceTrait

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {R₁ : Type u} [CommRing R₁] [IsLocalRing R₁] {Ω₁ : Type u} [Field Ω₁] {a₁ : R₁ →+* Ω₁}
  {κ₁ : Type u} [Field κ₁] {b₁ : R₁ →+* κ₁} (D : SliceTrait a₁ b₁)
  {Y Y' : Scheme.{u}} (N : NearbyCyclesModel Y Y')
  (c : N.total ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)))

/-- The total space `X' = 𝒳_N ×_{𝔸¹_{S₁}} S'` of the slice of `N` along `c` over the slice trait. -/
noncomputable abbrev sliceTraitTotal : Scheme.{u} :=
  pullback c D.toAffineLine

/-- The structure morphism `X' ⟶ S'`. -/
noncomputable abbrev sliceTraitStructure : sliceTraitTotal D N c ⟶ Spec (.of D.R) :=
  pullback.snd _ _

/-- The **model of the slice over the slice trait**: total space `X' = 𝒳_N ×_{𝔸¹_{S₁}} S'`,
generic fibre `X' ×_{S'} Spec Ω'`, special fibre `X' ×_{S'} Spec κ'` and `ε = j`. -/
@[simps]
noncomputable def sliceTraitModel :
    NearbyCyclesModel (sliceTraitTotal D N c)
      (pullback (sliceTraitStructure D N c) (Spec.map (CommRingCat.ofHom D.b))) where
  total := sliceTraitTotal D N c
  generic := pullback (sliceTraitStructure D N c) (Spec.map (CommRingCat.ofHom D.a))
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := pullback.fst _ _

variable {q₁ : N.total ⟶ Spec (.of R₁)}
  (hc : c ≫ 𝔸(ULift.{u} (Fin 1); Spec (.of R₁)) ↘ Spec (.of R₁) = q₁)
  {g₁ : N.generic ⟶ Spec (.of Ω₁)}
  (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁)))
  {p₁ : Y' ⟶ Spec (.of κ₁)} (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))

include hc in
@[reassoc]
lemma sliceTrait_fst_comp :
    pullback.fst c D.toAffineLine ≫ q₁ =
      sliceTraitStructure D N c ≫ Spec.map (CommRingCat.ofHom D.φ) := by
  rw [← hc, pullback.condition_assoc, D.spec_φ]

/-- The map `X' ×_{S'} Spec Ω' ⟶ 𝒳_{N,η̄}` of geometric generic fibres. -/
noncomputable def sliceTraitGeneric :
    (sliceTraitModel D N c).generic ⟶ N.generic :=
  hNj.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωS))
    (by
      rw [Category.assoc, sliceTrait_fst_comp D N c hc, pullback.condition_assoc, Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        D.ωS_comp])

/-- The map `X' ×_{S'} Spec κ' ⟶ Y'` of special fibres. -/
noncomputable def sliceTraitSpecial :
    pullback (sliceTraitStructure D N c) (Spec.map (CommRingCat.ofHom D.b)) ⟶ Y' :=
  hNi.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.κS))
    (by
      rw [Category.assoc, sliceTrait_fst_comp D N c hc, pullback.condition_assoc, Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        D.κS_comp])

/-- The **slice morphism of models** `σ` from the model of the slice over the slice trait to the
geometric model of `N`; its morphism of total spaces `X' ⟶ 𝒳_N` is the projection, which is
weakly étale. -/
@[simps]
noncomputable def sliceTraitHom :
    (sliceTraitModel D N c).Hom N.geometric (pullback.fst c D.toAffineLine)
      (sliceTraitSpecial D N c hc hNi) where
  total := pullback.fst _ _
  generic := sliceTraitGeneric D N c hc hNj
  comm_j := hNj.lift_fst _ _ _
  comm_i := hNi.lift_fst _ _ _
  comm_ε := hNj.lift_fst _ _ _

instance : WeaklyEtale (pullback.fst c D.toAffineLine) :=
  MorphismProperty.of_isPullback (P := @WeaklyEtale) (IsPullback.of_hasPullback _ _).flip
    D.weaklyEtale

/-- The generic fibre of the slice model is the base change of `X' ⟶ S'` to `Spec Ω'`. -/
lemma isPullback_sliceTraitModel_j :
    IsPullback (sliceTraitModel D N c).j (pullback.snd _ _) (sliceTraitStructure D N c)
      (Spec.map (CommRingCat.ofHom D.a)) :=
  IsPullback.of_hasPullback _ _

/-- The special fibre of the slice model is the base change of `X' ⟶ S'` to `Spec κ'`. -/
lemma isPullback_sliceTraitModel_i :
    IsPullback (sliceTraitModel D N c).i (pullback.snd _ _) (sliceTraitStructure D N c)
      (Spec.map (CommRingCat.ofHom D.b)) :=
  IsPullback.of_hasPullback _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
