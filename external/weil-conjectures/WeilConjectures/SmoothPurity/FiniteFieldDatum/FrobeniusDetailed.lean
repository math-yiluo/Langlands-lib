/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-!
# Arithmetic and geometric Frobenius

Source: Deligne, Weil II (1.1.7)--(1.1.8), pp. 150--151 and (1.1.14), p. 153
(blueprint: prose-10-19).

The arithmetic and geometric field automorphisms are the existing
`FiniteField.frobeniusAlgEquivOfAlgebraic` and
`FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`. The geometric scheme automorphism is
constructed on the geometric fibre of the recorded finite-field datum, for any fixed closure.
The absolute map is the existing `Scheme.iterateFrobenius` with p, a and the characteristic
proof `model_characteristic`; the relative map is `FiniteFieldDatum.relativeFrobenius`.
Only the geometric scheme automorphism is used for the blueprint's Frobenius operators.
## Main definitions

- `galoisMap`: the coefficient action on the chosen fibre product.
- `geometricFrobenius`: its geometric field-Frobenius specialization as an automorphism.

-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

/-- Spec of a base-field automorphism of the closure is a morphism over the base field.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: prose-10-19).
Proof: Spec is contravariant. The required composite corresponds to the composite of the
base embedding with σ. The latter equals the base embedding since σ is a k₀-algebra map. -/
theorem specGaloisMap_over (D : WeilConjectures.FiniteFieldDatum.{u})
    (σ : D.k ≃ₐ[D.k₀] D.k) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) =
      Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- The actual base-change map id × Spec σ on the geometric fibre, for a fixed closure.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: prose-10-19). -/
noncomputable def galoisMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) (σ : D.k ≃ₐ[D.k₀] D.k) :
    pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
  baseChangeMap f
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (T' := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom))
    (D.specGaloisMap_over σ))

/-- The inverse base-change map is obtained from the inverse field automorphism.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: prose-10-19).
Proof: composing the two base-change maps has identity on the model and Spec of σσ⁻¹,
respectively σ⁻¹σ, on the coefficient field. Both are identities. The universal property
of the fibre product then identifies both composites with its identity morphism. -/
theorem galoisMap_inverse (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) (σ : D.k ≃ₐ[D.k₀] D.k) :
    D.galoisMap f σ ≫ D.galoisMap f σ.symm = 𝟙 _ ∧
      D.galoisMap f σ.symm ≫ D.galoisMap f σ = 𝟙 _ := by
  let τ (ρ : D.k ≃ₐ[D.k₀] D.k) :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ρ.toRingHom)) (D.specGaloisMap_over ρ)
  have hmul (ρ η : D.k ≃ₐ[D.k₀] D.k) : τ ρ ≫ τ η = τ (ρ * η) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom η.toRingHom) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
  have hone : τ (1 : D.k ≃ₐ[D.k₀] D.k) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (RingHom.id D.k)) = 𝟙 _
    exact Spec.map_id _
  have hσmul : σ * σ.symm = 1 := mul_inv_cancel σ
  have hσmul' : σ.symm * σ = 1 := inv_mul_cancel σ
  have hσ : τ σ ≫ τ σ.symm = 𝟙 _ := by
    rw [hmul, hσmul, hone]
  have hσ' : τ σ.symm ≫ τ σ = 𝟙 _ := by
    rw [hmul, hσmul', hone]
  change baseChangeMap f (τ σ) ≫ baseChangeMap f (τ σ.symm) = 𝟙 _ ∧
    baseChangeMap f (τ σ.symm) ≫ baseChangeMap f (τ σ) = 𝟙 _
  constructor
  · rw [← baseChangeMap_comp, hσ, baseChangeMap_id]
  · rw [← baseChangeMap_comp, hσ', baseChangeMap_id]

/-- The geometric Frobenius automorphism id × Spec(φ_q⁻¹). Its inverse has arithmetic
Frobenius on coefficients; its underlying scheme is the dependency's geometric fibre.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: prose-10-19). -/
noncomputable def geometricFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    Aut (D.geometricFiber Y₀).left :=
  letI := Fintype.ofFinite D.k₀
  Aut.of
    { hom := D.galoisMap Y₀.hom (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
      inv := D.galoisMap Y₀.hom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
      hom_inv_id := (D.galoisMap_inverse Y₀.hom _).1
      inv_hom_id := (D.galoisMap_inverse Y₀.hom _).2 }

/-- The map fixes the model and is semilinear over the closure, with the stated coefficient
automorphism. These identities also make it a morphism over the finite base.
Source: Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: prose-10-19).
Proof: baseChangeMap is the universal lift with first projection unchanged and second
projection followed by Spec σ. Its defining projection equations prove both identities. -/
theorem galoisMap_projections (D : WeilConjectures.FiniteFieldDatum.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of D.k₀)) (σ : D.k ≃ₐ[D.k₀] D.k) :
    D.galoisMap f σ ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    D.galoisMap f σ ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  change baseChangeMap f _ ≫ pullback.fst f _ = _ ∧
    baseChangeMap f _ ≫ pullback.snd f _ = _
  constructor
  · exact baseChangeMap_fst f _
  · exact baseChangeMap_snd f _

end WeilConjectures.FiniteFieldDatum
