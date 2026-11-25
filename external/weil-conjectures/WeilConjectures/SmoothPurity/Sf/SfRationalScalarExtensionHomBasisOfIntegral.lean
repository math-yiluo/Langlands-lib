/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.Mathlib.RingTheory.IsTensorProductBasis

/-! # The rational finite free Hom formula from the integral one

For a finite extension `F/E` of finite extensions of `ℚ_ℓ`, suppose that for an
`𝒪_E`-basis `β` of `𝒪_F` every morphism `Ext N ⟶ Ext Z` of integral constructible
complexes is uniquely of the form `∑ i, β i • Ext (h i)`. Then after rationalization,
for any `E`-basis `v` of `F`, every morphism `T N ⟶ T Z` is uniquely of the form
`∑ i, v i • T (g i)`.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Section 6.8 (Lemma 6.7.2,
Proposition 6.8.14(2), Remark 6.8.15).
(blueprint: def-weil-rationalization-karoubi).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct

namespace WeilConjectures

/-- The rational finite free Hom formula follows from the integral one.

Mathematics: Hom groups of the rationalization are `Loc ⊗ Hom`, and after conjugating by the
object equations `T` sends `a ⊗ f` to `a ⊗ Ext f`. The integral hypothesis says that `Ext` is a
base change of Hom modules along `𝒪_E → 𝒪_F`; composing with base change along
`𝒪_F → Loc_F` and cancelling base change along `𝒪_E → Loc_E` shows that
`Loc_E ⊗ Hom → Loc_F ⊗ Hom_F` is a base change along `Loc_E → Loc_F`. Since `v` is a
`Loc_E`-basis of `Loc_F`, this is the claimed bijectivity
(`TensorProduct.bijective_sum_smul_of_bijective_sum_basis_smul`). -/
theorem sfRationalScalarExtension_map_basis_bijective_of_integral (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : AlgebraicGeometry.Scheme.{u}) (p : ℕ) (hl : l ≠ p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (hI : letI := (integralScalarIntegerInclusion l E F ι).toAlgebra
      ∃ (d' : ℕ) (β : Module.Basis (Fin d') (Padic.coefficientExtensionIntegers l E)
          (Padic.coefficientExtensionIntegers l F)),
        ∀ N Z : sfIntegralConstructibleCategory l E W,
          Function.Bijective fun h : Fin d' → (N ⟶ Z) ↦
            ∑ i, β i • (sfConstructibleIntegralScalarExtension p l hl E F ι W).map (h i))
    {d : ℕ} (v : Fin d → F) (hv : ∀ x : F, ∃! c : Fin d → E, ∑ i, ι (c i) * v i = x)
    (N Z : sfRationalConstructibleCategory l E W) :
    Function.Bijective (fun g : Fin d → (N ⟶ Z) ↦
      ∑ i, (sfRationalCoefficientEquiv l F).symm (v i) •
        (sfRationalScalarExtension l E W p hl F ι).map (g i)) := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l F
  let φ := integralScalarIntegerInclusion l E F ι
  let Ext := sfConstructibleIntegralScalarExtension p l hl E F ι W
  let T := sfRationalScalarExtension l E W p hl F ι
  let eE := sfRationalCoefficientEquiv l E
  let eF := sfRationalCoefficientEquiv l F
  let _ : Algebra R S := φ.toAlgebra
  obtain ⟨d', β, hβ⟩ := hI
  let H := N.obj ⟶ Z.obj
  let H' := Ext.obj N.obj ⟶ Ext.obj Z.obj
  let _ : Module R H' := Module.compHom H' φ
  have : IsScalarTower R S H' := ⟨fun r s x ↦ by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  have hadd : ∀ x y : H, Ext.map (x + y) = Ext.map x + Ext.map y := fun x y ↦ by
    apply ObjectProperty.hom_ext
    change (integralScalarExtension l E F ι W).map (x.hom + y.hom) = _
    exact (integralScalarExtension l E F ι W).map_add
  have hsmul : ∀ (a : R) (x : H), Ext.map (a • x) = φ a • Ext.map x := fun a x ↦ by
    apply ObjectProperty.hom_ext
    change (integralScalarExtension l E F ι W).map (a • x.hom) = φ a • (Ext.map x).hom
    rw [(sfIntegralConstructible_linear l E W).1, (sfIntegralConstructible_linear l F W).1]
    exact sfConstructibleIntegralScalarExtension_smul p l hl E F ι W N.obj Z.obj x a
  let e : H →ₗ[R] H' :=
    { toFun := Ext.map
      map_add' := hadd
      map_smul' := hsmul }
  let LE := Localization.Away (Padic.coefficientExtensionUniformizer l E)
  let LF := Localization.Away (Padic.coefficientExtensionUniformizer l F)
  let c : LE →+* LF := eF.symm.toRingHom.comp (ι.toRingHom.comp eE.toRingHom)
  let _ : Algebra LE LF := c.toAlgebra
  have : IsScalarTower R S LF := inferInstance
  have : IsScalarTower R LE LF := IsScalarTower.of_algebraMap_eq fun r ↦ by
    apply eF.injective
    change eF (algebraMap R LF r) = eF (eF.symm (ι (eE (algebraMap R LE r))))
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, IsScalarTower.algebraMap_apply R S LF,
      AlgEquiv.commutes]
    rfl
  have hN := sfRationalScalarExtension_obj l E W p hl F ι N
  have hZ := sfRationalScalarExtension_obj l E W p hl F ι Z
  let conj := (eqToIso hN).homCongr (eqToIso hZ)
  let Θ : LE ⊗[R] H →+ LF ⊗[S] H' :=
    { toFun := fun g ↦ conj (T.map (X := N) (Y := Z) g)
      map_zero' := by simp [conj]
      map_add' := fun x y ↦ by simp [conj, T.map_add] }
  have hΘ : ∀ (a : LE) (x : H), Θ (a ⊗ₜ x) = algebraMap LE LF a ⊗ₜ e x := fun a x ↦ by
    symm
    refine (conj_eqToHom_iff_heq _ _ hN.symm hZ.symm).2
      (sfRationalScalarExtension_map_tmul l E W p hl F ι N.obj Z.obj x a).symm
  have hv' : Function.Bijective fun c : Fin d → LE ↦ ∑ k, c k • eF.symm (v k) := by
    have hG : Function.Bijective fun c : Fin d → E ↦ ∑ i, ι (c i) * v i :=
      (Function.bijective_iff_existsUnique _).2 hv
    have hE : Function.Bijective fun (c : Fin d → LE) (k : Fin d) ↦ eE (c k) :=
      (Equiv.piCongrRight fun _ ↦ eE.toEquiv).bijective
    convert eF.symm.bijective.comp (hG.comp hE) using 1
    funext c
    rw [Function.comp_apply, Function.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Algebra.smul_def, map_mul]
    rfl
  have key := TensorProduct.bijective_sum_smul_of_bijective_sum_basis_smul e β
    (hβ N.obj Z.obj) _ hv' Θ hΘ
  have h2 : ∀ g : Fin d → (N ⟶ Z), conj (∑ i, eF.symm (v i) • T.map (g i)) =
      ∑ k, eF.symm (v k) • Θ (g k) := fun g ↦ by
    simp [conj, Θ, Preadditive.comp_sum, Preadditive.sum_comp]
  rw [← Function.Bijective.of_comp_iff' conj.bijective]
  exact (congrArg Function.Bijective (funext h2)).mpr key

end WeilConjectures
