/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusExistence
public import WeilConjectures.TraceFormula.FixedPoint

/-!
# Extending the field of definition of a model

Let `k₀` be a finite field with `q` elements, `k` an algebraically closed field containing `k₀`,
`X₀` a scheme over `k₀` and `X = X₀ ×_{k₀} k` with model Frobenius `Φ`. For `m ≠ 0`, the field
`k` contains a subfield `k₁ ⊇ k₀` with `q ^ m` elements, and the iterate `Φ_m = Φ^m` is the
model Frobenius of the model `X₀ ×_{k₀} k₁` of `X` over `k₁`.

## Main statements

- `AlgebraicGeometry.ProEtale.CondensedRing.exists_intermediateField_natCard_eq_pow`,
  `AlgebraicGeometry.ProEtale.CondensedRing.exists_finiteField_natCard_eq_pow`: an
  algebraically closed field containing `k₀` contains an extension of `k₀` with `q ^ m`
  elements.
- `AlgebraicGeometry.ProEtale.CondensedRing.IsModelFrobenius.fieldChange`: `Φ_m` is the model
  Frobenius of the model `X₀ ×_{k₀} k₁` over the field `k₁` with `q ^ m` elements.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Finite subfields of an algebraically closed field -/

section Subfield

variable (k₀ : Type u) [Field k₀] [Finite k₀] (k : Type u) [Field k] [IsAlgClosed k]
  [Algebra k₀ k]

/-- An algebraically closed field `k` containing a finite field `k₀` with `q` elements contains,
for every `m ≠ 0`, an intermediate field with `q ^ m` elements. -/
theorem exists_intermediateField_natCard_eq_pow {m : ℕ} (hm : m ≠ 0) :
    ∃ K : IntermediateField k₀ k, Finite K ∧ Nat.card K = Nat.card k₀ ^ m := by
  have : Fact (ringChar k₀).Prime := ⟨CharP.char_is_prime k₀ _⟩
  have : NeZero m := ⟨hm⟩
  let φ := IsAlgClosed.lift (M := k) (R := k₀) (S := FiniteField.Extension k₀ (ringChar k₀) m)
  let e := AlgEquiv.ofInjectiveField φ
  have : Finite φ.fieldRange := Finite.of_equiv _ e.toEquiv
  refine ⟨φ.fieldRange, this, ?_⟩
  rw [← FiniteField.natCard_extension k₀ (ringChar k₀) m, Nat.card_congr e.toEquiv]
  rfl

/-- An algebraically closed field `k` containing a finite field `k₀` with `q` elements contains,
for every `m ≠ 0`, a finite field `k₁ ⊇ k₀` with `q ^ m` elements. -/
theorem exists_finiteField_natCard_eq_pow {m : ℕ} (hm : m ≠ 0) :
    ∃ (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : Algebra k₀ k₁) (_ : Algebra k₁ k)
      (_ : IsScalarTower k₀ k₁ k), Nat.card k₁ = Nat.card k₀ ^ m := by
  obtain ⟨K, hK, hcard⟩ := exists_intermediateField_natCard_eq_pow k₀ k hm
  exact ⟨K, inferInstance, hK, inferInstance, inferInstance, inferInstance, hcard⟩

end Subfield

/-! ### Base change of a model -/

section BaseChange

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  (f₀ : X₀ ⟶ Spec (.of k₀)) {p : X.left ⟶ X₀}
  (k₁ : Type u) [Field k₁] [Finite k₁] [Algebra k₀ k₁] [Algebra k₁ k] [IsScalarTower k₀ k₁ k]

omit [Finite k₀] [Finite k₁] in
/-- For a tower `k₀ ⊆ k₁ ⊆ k`, the morphism `Spec k ⟶ Spec k₀` factors through `Spec k₁`. -/
lemma specMap_algebraMap_eq_comp :
    Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₁ k)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The base change `X₀ ×_{k₀} k₁ ⟶ Spec k₁` of a scheme `f₀ : X₀ ⟶ Spec k₀` to an extension
`k₁` of `k₀`. -/
noncomputable def modelFieldChange :
    pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) ⟶ Spec (.of k₁) :=
  pullback.snd _ _

/-- The base change of a scheme locally of finite type is locally of finite type. -/
instance [LocallyOfFiniteType f₀] : LocallyOfFiniteType (modelFieldChange f₀ k₁) := by
  unfold modelFieldChange
  infer_instance

/-- The base change of a quasi-compact scheme is quasi-compact. -/
instance [QuasiCompact f₀] : QuasiCompact (modelFieldChange f₀ k₁) := by
  unfold modelFieldChange
  infer_instance

/-- The base change of a separated scheme is separated. -/
instance [IsSeparated f₀] : IsSeparated (modelFieldChange f₀ k₁) := by
  unfold modelFieldChange
  infer_instance

variable {f₀} in
/-- For a model `X = X₀ ×_{k₀} k` of `X` and a tower `k₀ ⊆ k₁ ⊆ k`, the projection
`X ⟶ X₀ ×_{k₀} k₁`. -/
noncomputable def modelFieldChangeLift
    (w : p ≫ f₀ = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :
    X.left ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) :=
  pullback.lift p (X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₁ k)))
    (by rw [w, specMap_algebraMap_eq_comp k₁, Category.assoc])

variable {f₀ k₁}

omit [Finite k₀] [Finite k₁] in
/-- The projection `X ⟶ X₀ ×_{k₀} k₁` followed by `X₀ ×_{k₀} k₁ ⟶ X₀` is `p`. -/
@[reassoc (attr := simp)]
lemma modelFieldChangeLift_fst
    (w : p ≫ f₀ = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :
    modelFieldChangeLift k₁ w ≫ pullback.fst _ _ = p :=
  pullback.lift_fst _ _ _

omit [Finite k₀] [Finite k₁] in
/-- The projection `X ⟶ X₀ ×_{k₀} k₁` is a morphism over `Spec k₁`. -/
@[reassoc (attr := simp)]
lemma modelFieldChangeLift_snd
    (w : p ≫ f₀ = X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) :
    modelFieldChangeLift k₁ w ≫ modelFieldChange f₀ k₁ =
      X.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₁ k)) :=
  pullback.lift_snd _ _ _

/-- If `Φ` is the model Frobenius of a model `X₀` of `X` over `k₀` with `q` elements and
`k₀ ⊆ k₁ ⊆ k` with `#k₁ = q ^ m`, then the iterate `Φ_m` is the model Frobenius of the model
`X₀ ×_{k₀} k₁` of `X` over `k₁`. -/
theorem IsModelFrobenius.fieldChange (hΦ : IsModelFrobenius Φ f₀ p) {m : ℕ}
    (hm : Nat.card k₁ = Nat.card k₀ ^ m) :
    IsModelFrobenius (frobeniusIterate Φ m) (modelFieldChange f₀ k₁)
      (modelFieldChangeLift k₁ hΦ.isPullback.w) where
  isPullback := by
    refine IsPullback.of_right (h₁₂ := pullback.fst _ _)
      (v₁₃ := f₀) (h₂₂ := Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) ?_
      (modelFieldChangeLift_snd _) (IsPullback.of_hasPullback _ _)
    rw [modelFieldChangeLift_fst, ← specMap_algebraMap_eq_comp]
    exact hΦ.isPullback
  exists_isFrobenius := by
    obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
    obtain ⟨F₁, hF₁⟩ := (modelFieldChange f₀ k₁).exists_isFrobenius
    have hF₀m : (End.asHom (End.of F₀ ^ m)).IsFrobenius (Nat.card k₁) := hm ▸ hF₀.pow f₀ m
    refine ⟨F₁, hF₁, pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, modelFieldChangeLift_fst,
        ← hF₁.comp_eq_comp (modelFieldChange f₀ k₁) hF₀m, modelFieldChangeLift_fst_assoc]
      exact frobeniusIterate_left_comp hp m
    · have h := hF₁.comp_eq (modelFieldChange f₀ k₁)
      rw [modelFieldChange] at h
      rw [Category.assoc, Category.assoc, h, modelFieldChangeLift, pullback.lift_snd,
        ← Category.assoc, Over.w]

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
