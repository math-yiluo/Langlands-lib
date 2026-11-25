/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory
import WeilConjectures.RingTheory.LocalizationAwaySemilinearTensor
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationPureTensor

/-! # Transport of integral ambient trace through rational localization

This module isolates the denominator and normalized scalar-extension transport.
(blueprint: new-sf-rational-scalar-ambient-localization-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- The uniformizer of `𝒪_F` divides the image of the uniformizer of `𝒪_E` under the
integer-ring inclusion induced by `ι`. -/
theorem coefficientExtensionUniformizer_dvd_integralScalarIntegerInclusion
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) :
    Padic.coefficientExtensionUniformizer l F ∣
      integralScalarIntegerInclusion l E F ι (Padic.coefficientExtensionUniformizer l E) := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hL := (Padic.coefficientExtensionIntegers_dvr l F).choose_spec
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenL : Ideal.span {Padic.coefficientExtensionUniformizer l F} =
      Padic.coefficientExtensionMaximalIdeal l F :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπE : Padic.coefficientExtensionUniformizer l E ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    rw [← hgenE]
    exact Ideal.mem_span_singleton_self _
  have hπL : integralScalarIntegerInclusion l E F ι
      (Padic.coefficientExtensionUniformizer l E) ∈
      Padic.coefficientExtensionMaximalIdeal l F := by
    exact (hL.2.1 _).mpr
      ((integralScalar_absoluteValue l E F ι _).trans_lt ((hE.2.1 _).mp hπE))
  rwa [← hgenL, Ideal.mem_span_singleton] at hπL

/-- The localized coefficient map induced by `ι` extends the integer-ring inclusion. -/
theorem sfRationalCoefficientEquiv_symm_apply_algebraMap
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (r : Padic.coefficientExtensionIntegers l E) :
    (sfRationalCoefficientEquiv l F).symm (ι (sfRationalCoefficientEquiv l E
        (algebraMap _ (Localization.Away (Padic.coefficientExtensionUniformizer l E)) r))) =
      algebraMap _ (Localization.Away (Padic.coefficientExtensionUniformizer l F))
        (integralScalarIntegerInclusion l E F ι r) := by
  apply (sfRationalCoefficientEquiv l F).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
  rfl

/-- The restricted completed scalar extension is additive. -/
theorem sfConstructibleIntegralScalarExtension_map_add
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (p : ℕ) (hl : l ≠ p) {X Y : sfIntegralConstructibleCategory l E W}
    (f g : X ⟶ Y) :
    (sfConstructibleIntegralScalarExtension p l hl E F ι W).map (f + g) =
      (sfConstructibleIntegralScalarExtension p l hl E F ι W).map f +
        (sfConstructibleIntegralScalarExtension p l hl E F ι W).map g := by
  apply ObjectProperty.hom_ext
  exact (integralScalarExtension l E F ι W).map_add

/-- The restricted completed scalar extension is semilinear along the integer-ring
inclusion. -/
theorem sfConstructibleIntegralScalarExtension_map_smul
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (p : ℕ) (hl : l ≠ p) {X Y : sfIntegralConstructibleCategory l E W}
    (a : Padic.coefficientExtensionIntegers l E) (f : X ⟶ Y) :
    (sfConstructibleIntegralScalarExtension p l hl E F ι W).map (a • f) =
      integralScalarIntegerInclusion l E F ι a •
        (sfConstructibleIntegralScalarExtension p l hl E F ι W).map f := by
  apply ObjectProperty.hom_ext
  exact ((integralScalarExtension l E F ι W).congr_map
    ((sfIntegralConstructible_linear l E W).1 a _ _ f.hom)).trans
    ((sfConstructibleIntegralScalarExtension_smul p l hl E F ι W X Y f a).trans
      ((sfIntegralConstructible_linear l F W).1 _ _ _ _).symm)

/-- A family of integral Hom equivalences from the actual derived restriction of `K`
to the completed integral scalar extension, indexed by integral constructible objects.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientIntegralFamily
    (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W)) :=
  ∀ M : sfIntegralConstructibleCategory l E W,
    ((rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj) ≃
      (K ⟶ ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj M).obj)

/-- Postcomposition naturality of an integral family of Hom equivalences.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientIntegralNaturality
    (l : ℕ) [Fact l.Prime] (E F : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K) :=
  ∀ (M N : sfIntegralConstructibleCategory l E W) (f : M ⟶ N) (h),
    e₀ N (h ≫ f.hom) =
      e₀ M h ≫ ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).map f).hom

/-- Inclusion of rational constructible objects into the ambient scalar localization
(the same expression as `rationalScalarAmbientInclusion` of the item module, which
cannot be imported here).
Source: the raw rationalization Hom formula
(blueprint: new-sf-rational-scalar-ambient-localization-transport). -/
abbrev rationalScalarAmbientTransportInclusion :=
  ScalarLocalization.fullSubcategoryInclusion (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)

/-- A natural family of integral Hom equivalences is semilinear along the integer-ring
inclusion: apply naturality to the scalar endomorphism `a • 𝟙`. -/
theorem rationalScalarAmbientIntegralFamily_apply_smul
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀)
    (X : sfIntegralConstructibleCategory l E W) (a : Padic.coefficientExtensionIntegers l E)
    (h : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ X.obj) :
    e₀ X (a • h) = integralScalarIntegerInclusion l E F ι a • e₀ X h := by
  have key := he₀ X X (a • 𝟙 X) h
  have hX : (a • 𝟙 X).hom = a • 𝟙 X.obj := rfl
  have hY : (integralScalarIntegerInclusion l E F ι a • 𝟙
      ((sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E F ι W).obj X)).hom = integralScalarIntegerInclusion l E F ι a • 𝟙 _ := rfl
  rw [sfConstructibleIntegralScalarExtension_map_smul, CategoryTheory.Functor.map_id, hX,
    hY, Linear.comp_smul, Category.comp_id, Linear.comp_smul, Category.comp_id] at key
  exact key

/-- A natural family of integral Hom equivalences is additive: write `h₁ + h₂` as the
binary-product lift followed by the sum of the projections, using that integral
constructible objects are closed under binary products. -/
theorem rationalScalarAmbientIntegralFamily_apply_add
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀)
    (X : sfIntegralConstructibleCategory l E W)
    (h₁ h₂ : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ X.obj) :
    e₀ X (h₁ + h₂) = e₀ X h₁ + e₀ X h₂ := by
  let P : sfIntegralConstructibleCategory l E W :=
    ⟨X.obj ⨯ X.obj, (sfIntegralConstructible l E W).prop_prod _ _ X.property X.property⟩
  let p₁ : P ⟶ X := ObjectProperty.homMk Limits.prod.fst
  let p₂ : P ⟶ X := ObjectProperty.homMk Limits.prod.snd
  have key := he₀ P X (p₁ + p₂) (Limits.prod.lift h₁ h₂)
  have hp : (p₁ + p₂).hom = Limits.prod.fst + Limits.prod.snd := rfl
  have hq (Z : sfIntegralConstructibleCategory l F W)
      (v w : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E F ι W).obj P ⟶ Z) :
      (v + w).hom = v.hom + w.hom := rfl
  have hp₁ : p₁.hom = Limits.prod.fst := rfl
  have hp₂ : p₂.hom = Limits.prod.snd := rfl
  rw [sfConstructibleIntegralScalarExtension_map_add, hp, hq, Preadditive.comp_add,
    Preadditive.comp_add, ← he₀ P X p₁, ← he₀ P X p₂, hp₁, hp₂, Limits.prod.lift_fst,
    Limits.prod.lift_snd] at key
  exact key

-- The tensor-induction over localized morphisms elaborates large scalar-localization terms.
/-- Rationalized trace transport from the integral trace data.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15, and the raw
scalar-localization Hom formula.
(blueprint: new-sf-rational-scalar-ambient-localization-transport).

Proof: tensor the integral equivalences with the localization coefficient ring,
then use the full-subcategory Hom equivalence on both sides. Pure tensors are
independent of their chosen denominators by balancing, and tensor induction
extends the calculation to all localized morphisms. The defining equations of
the normalized rational scalar extension identify the transported map with the
specified functor. Applying the same calculation to postcomposition proves the
displayed naturality equation. -/
theorem rationalScalarAmbientLocalizationTransport
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W))
    (e₀ : rationalScalarAmbientIntegralFamily l E F ι W K)
    (he₀ : rationalScalarAmbientIntegralNaturality l E F ι W K e₀) :
    ∃ e : ∀ M : sfRationalConstructibleCategory l E W,
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        (rationalScalarAmbientTransportInclusion l E W).obj M) ≃
      (ScalarLocalization.mk K ⟶
        (rationalScalarAmbientTransportInclusion l F W).obj
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)),
      ∀ (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ (rationalScalarAmbientTransportInclusion l E W).map f) =
          e M h ≫ (rationalScalarAmbientTransportInclusion l F W).map
            ((sfRationalScalarExtension l E W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f) := by
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let φ := integralScalarIntegerInclusion l E F ι
  let hl := Nat.Prime.ne_zero (Fact.out : l.Prime)
  let Ext := sfConstructibleIntegralScalarExtension 0 l hl E F ι W
  let G := sfRationalScalarExtension l E W 0 hl F ι
  let ιE := rationalScalarAmbientTransportInclusion l E W
  let ιF := rationalScalarAmbientTransportInclusion l F W
  let c : Localization.Away t →+* Localization.Away (Padic.coefficientExtensionUniformizer l F) :=
    (sfRationalCoefficientEquiv l F).symm.toRingHom.comp
      (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom)
  have hc (r : R) : c (algebraMap R _ r) = algebraMap _ _ (φ r) :=
    sfRationalCoefficientEquiv_symm_apply_algebraMap l E F ι r
  have he₀_smul := rationalScalarAmbientIntegralFamily_apply_smul l E W F ι K e₀ he₀
  have he₀_add := rationalScalarAmbientIntegralFamily_apply_add l E W F ι K e₀ he₀
  let ψ (M : sfRationalConstructibleCategory l E W) :
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ ιE.obj M) ≃+
        (ScalarLocalization.mk K ⟶ ιF.obj ⟨Ext.obj M.obj⟩) :=
    AddEquiv.ofBijective _ (Localization.Away.semilinearTensorMap_bijective c hc
      (AddMonoidHom.mk' (e₀ M.obj) (he₀_add M.obj)) (he₀_smul M.obj)
      (coefficientExtensionUniformizer_dvd_integralScalarIntegerInclusion l E F ι)
      (e₀ M.obj).bijective)
  have hobj (M : sfRationalConstructibleCategory l E W) :
      G.obj M = ⟨Ext.obj M.obj⟩ := sfRationalScalarExtension_obj l E W 0 hl F ι M
  have : G.Additive := sfRationalScalarExtension_additive l E W 0 hl F ι
  let Φ (M N : sfRationalConstructibleCategory l E W) :=
    Localization.Away.semilinearTensorMap c hc
      (AddMonoidHom.mk' (fun g : M.obj ⟶ N.obj ↦ Ext.map g)
        (fun g g' ↦ sfConstructibleIntegralScalarExtension_map_add l E W F ι 0 hl g g'))
      (fun a g ↦ sfConstructibleIntegralScalarExtension_map_smul l E W F ι 0 hl a g)
  have hG (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) :
      G.map f = eqToHom (hobj M) ≫
        (Φ M N f : (⟨Ext.obj M.obj⟩ : sfRationalConstructibleCategory l F W) ⟶
          ⟨Ext.obj N.obj⟩) ≫ eqToHom (hobj N).symm := by
    induction f using TensorProduct.inductionOn with
    | tmul a g =>
      refine (conj_eqToHom_iff_heq _ _ (hobj M) (hobj N)).2 ?_
      refine (sfRationalScalarExtension_map_tmul l E W 0 hl F ι M.obj N.obj g a).trans
        (heq_of_eq ?_)
      exact (Localization.Away.semilinearTensorMap_tmul c hc
        (AddMonoidHom.mk' (fun g : M.obj ⟶ N.obj ↦ Ext.map g) _) _ a g).symm
    | add x y hx hy =>
      rw [G.map_add, hx, hy, map_add, Preadditive.add_comp, Preadditive.comp_add]
  have key (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N)
      (h : ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        ιE.obj M) :
      ψ N (h ≫ ιE.map f) = ψ M h ≫ ιF.map (Φ M N f) := by
    have hψ (a : Localization.Away t)
        (h₀ : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ M.obj.obj) :
        ψ M (a ⊗ₜ h₀) = c a ⊗ₜ e₀ M.obj h₀ :=
      Localization.Away.semilinearTensorMap_tmul c hc _ (he₀_smul _) a h₀
    have hψ' (a : Localization.Away t)
        (h₀ : (rationalScalarDerivedRestriction l E F ι W).obj K ⟶ N.obj.obj) :
        ψ N (a ⊗ₜ h₀) = c a ⊗ₜ e₀ N.obj h₀ :=
      Localization.Away.semilinearTensorMap_tmul c hc _ (he₀_smul _) a h₀
    induction f using TensorProduct.inductionOn with
    | tmul a g =>
      induction h using TensorProduct.inductionOn with
      | tmul a' h₀ =>
        have h1 : (a' ⊗ₜ h₀ : ScalarLocalization.mk
            ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ ιE.obj M) ≫ ιE.map (a ⊗ₜ g) =
            ((a * a') ⊗ₜ (h₀ ≫ g.hom) : ScalarLocalization.mk
              ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶ ιE.obj N) := by
          rw [ScalarLocalization.fullSubcategoryInclusion_map_tmul]
          exact ScalarLocalization.tmul_comp_tmul (M := ιE.obj N) a' a h₀ g.hom
        have h2 : ιF.map (Φ M N (a ⊗ₜ g)) =
            (c a ⊗ₜ (Ext.map g).hom : ιF.obj ⟨Ext.obj M.obj⟩ ⟶ ιF.obj ⟨Ext.obj N.obj⟩) := by
          have hΦ : Φ M N (a ⊗ₜ g) = c a ⊗ₜ Ext.map g :=
            Localization.Away.semilinearTensorMap_tmul c hc _ _ a g
          rw [hΦ]
          exact ScalarLocalization.fullSubcategoryInclusion_map_tmul _ (c a) (Ext.map g)
        refine (congrArg (ψ N) h1).trans ((hψ' _ _).trans ?_)
        refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (hψ a' h₀) h2).symm
        have h3 := ScalarLocalization.tmul_comp_tmul (K := ScalarLocalization.mk K)
          (L := ιF.obj ⟨Ext.obj M.obj⟩) (M := ιF.obj ⟨Ext.obj N.obj⟩) (c a') (c a)
          (e₀ M.obj h₀) (Ext.map g).hom
        have h4 : e₀ N.obj (h₀ ≫ g.hom) = e₀ M.obj h₀ ≫ (Ext.map g).hom := he₀ M.obj N.obj g h₀
        exact (congrArg₂ (fun x z ↦ (x ⊗ₜ z : ScalarLocalization.mk K ⟶ ιF.obj ⟨Ext.obj N.obj⟩))
          (map_mul c a a') h4).trans h3.symm
      | add x y hx hy => rw [Preadditive.add_comp, map_add, hx, hy, map_add, Preadditive.add_comp]
    | add x y hx hy =>
      rw [Functor.map_add, Preadditive.comp_add, map_add, hx, hy, map_add, Functor.map_add,
        Preadditive.comp_add]
  refine ⟨fun M ↦
    { toFun := fun h ↦ ψ M h ≫ ιF.map (eqToHom (hobj M).symm)
      invFun := fun h' ↦ (ψ M).symm (h' ≫ ιF.map (eqToHom (hobj M)))
      left_inv := fun h ↦ by
        beta_reduce
        rw [Category.assoc, ← ιF.map_comp, eqToHom_trans, eqToHom_refl, ιF.map_id,
          Category.comp_id, AddEquiv.symm_apply_apply]
      right_inv := fun h' ↦ by
        beta_reduce
        rw [AddEquiv.apply_symm_apply, Category.assoc, ← ιF.map_comp, eqToHom_trans,
          eqToHom_refl, ιF.map_id, Category.comp_id] }, ?_⟩
  intro M N f h
  rw [Equiv.coe_fn_mk, Equiv.coe_fn_mk, hG, key]
  simp [ιF]

end WeilConjectures
