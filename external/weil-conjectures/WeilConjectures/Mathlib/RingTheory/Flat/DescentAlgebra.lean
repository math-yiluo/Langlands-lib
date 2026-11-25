/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Descent of algebras along flat ring maps

Let `A → A'` be a ring map and `E` an `A'`-algebra. A *descent datum* on `E` relative to `A'/A`,
in coalgebra form, is an `A'`-algebra map `δ : E → A' ⊗[A] E` (where `A' ⊗[A] E` is an
`A'`-algebra through the left factor) which is counital and coassociative, see
`Algebra.DescentDatum`. Classically a descent datum is an isomorphism
`φ : E ⊗[A] A' ≃ A' ⊗[A] E` of `A' ⊗[A] A'`-algebras satisfying the cocycle condition; the two
are related by `δ e = φ (e ⊗ 1)`, and the counit condition corresponds to the normalisation
of `φ` along the diagonal.

The *descended algebra* `D.descended` is the `A`-subalgebra of `E` of elements `e` with
`δ e = 1 ⊗ e`. We show that if `A'` is flat over `A`, the comparison map
`A' ⊗[A] D.descended → E` is an isomorphism (`Algebra.DescentDatum.descendedEquiv`), i.e. every
descent datum is effective. If `A'` is moreover faithfully flat over `A` and `E` is étale over
`A'`, then `D.descended` is étale over `A` (`Algebra.DescentDatum.etale_descended`).

## Implementation notes

The proof of effectivity is the classical one: the coaction `δ` itself provides the inverse of
the comparison map. By coassociativity, `δ` takes values in the equalizer of `𝟙 ⊗ δ` and
`𝟙 ⊗ (1 ⊗ ·)`, which by flatness of `A'` is `A' ⊗[A] D.descended`
(`AlgHom.tensorEqualizerEquiv`); the counit condition says that this is a right inverse, and
`δ d = 1 ⊗ d` for `d` in the descended algebra says that it is a left inverse.

## References

* [Stacks 023N], Descent, Section 35.3.
-/

@[expose] public section

open TensorProduct

namespace Algebra

section MulMap

variable (A A' E : Type*) [CommRing A] [CommRing A'] [CommRing E] [Algebra A A'] [Algebra A E]
  [Algebra A' E] [IsScalarTower A A' E]

/-- The multiplication map `A' ⊗[A] E → E`, `a' ⊗ e ↦ a' • e`, as a map of `A'`-algebras. -/
noncomputable def TensorProduct.mulMap : A' ⊗[A] E →ₐ[A'] E :=
  Algebra.TensorProduct.lift (Algebra.ofId A' E) (AlgHom.id A E) fun _ _ ↦ Commute.all _ _

variable {A A' E}

@[simp]
lemma TensorProduct.mulMap_tmul (a' : A') (e : E) :
    TensorProduct.mulMap A A' E (a' ⊗ₜ e) = a' • e := by
  simp [TensorProduct.mulMap, Algebra.smul_def, Algebra.ofId_apply]

@[simp]
lemma TensorProduct.mulMap_includeRight (e : E) :
    TensorProduct.mulMap A A' E (Algebra.TensorProduct.includeRight e) = e := by
  simp

end MulMap

/-- A descent datum on an `A'`-algebra `E` relative to `A'/A`, in coalgebra form: an `A'`-algebra
map `δ : E → A' ⊗[A] E` (the target being an `A'`-algebra through the left factor) which is
counital and coassociative.

In terms of the classical descent isomorphism `φ : E ⊗[A] A' ≃ A' ⊗[A] E`, one has
`δ e = φ (e ⊗ 1)`. -/
structure DescentDatum (A A' E : Type*) [CommRing A] [CommRing A'] [CommRing E] [Algebra A A']
    [Algebra A E] [Algebra A' E] [IsScalarTower A A' E] where
  /-- The coaction. -/
  δ : E →ₐ[A'] A' ⊗[A] E
  /-- The counit condition: multiplying back gives the identity. -/
  counit : ∀ e, TensorProduct.mulMap A A' E (δ e) = e
  /-- The coassociativity condition, i.e. the cocycle condition. -/
  coassoc : ∀ e, Algebra.TensorProduct.map (AlgHom.id A A') (δ.restrictScalars A) (δ e) =
    Algebra.TensorProduct.map (AlgHom.id A A') Algebra.TensorProduct.includeRight (δ e)

namespace DescentDatum

variable {A A' E : Type*} [CommRing A] [CommRing A'] [CommRing E] [Algebra A A'] [Algebra A E]
  [Algebra A' E] [IsScalarTower A A' E] (D : DescentDatum A A' E)

lemma δ_smul (a' : A') (e : E) : D.δ (a' • e) = a' • D.δ e :=
  map_smul D.δ a' e

lemma δ_algebraMap (a' : A') : D.δ (algebraMap A' E a') = a' ⊗ₜ 1 := by
  rw [AlgHom.commutes]
  rfl


/-- The descended algebra of a descent datum: the `A`-subalgebra of `E` consisting of the
elements `e` with `δ e = 1 ⊗ e`. -/
noncomputable def descended : Subalgebra A E :=
  AlgHom.equalizer (D.δ.restrictScalars A) Algebra.TensorProduct.includeRight

lemma mem_descended_iff (e : E) : e ∈ D.descended ↔ D.δ e = 1 ⊗ₜ e :=
  Iff.rfl


lemma δ_of_mem_descended {e : E} (he : e ∈ D.descended) : D.δ e = 1 ⊗ₜ e :=
  he

/-- The comparison map `A' ⊗[A] D.descended → E`, `a' ⊗ d ↦ a' • d`. -/
noncomputable def descendedMap : A' ⊗[A] D.descended →ₐ[A'] E :=
  Algebra.TensorProduct.lift (Algebra.ofId A' E) D.descended.val fun _ _ ↦ Commute.all _ _

@[simp]
lemma descendedMap_tmul (a' : A') (d : D.descended) : D.descendedMap (a' ⊗ₜ d) = a' • (d : E) := by
  simp [descendedMap, Algebra.smul_def, Algebra.ofId_apply]

section Flat

variable [Module.Flat A A']

/-- (Implementation) The equalizer of `𝟙 ⊗ δ` and `𝟙 ⊗ (1 ⊗ ·)` in `A' ⊗[A] E`, which is
`A' ⊗[A] D.descended` by flatness. -/
private noncomputable abbrev tensorEqualizer : Subalgebra A' (A' ⊗[A] E) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id A' A') (D.δ.restrictScalars A))
    (Algebra.TensorProduct.map (AlgHom.id A' A') Algebra.TensorProduct.includeRight)

omit [Module.Flat A A'] in
private lemma δ_mem_tensorEqualizer (e : E) : D.δ e ∈ D.tensorEqualizer :=
  D.coassoc e

/-- (Implementation) The coaction as a map into `A' ⊗[A] D.descended`. -/
private noncomputable def δ' (e : E) : A' ⊗[A] D.descended :=
  (AlgHom.tensorEqualizerEquiv A' A' (D.δ.restrictScalars A)
    Algebra.TensorProduct.includeRight).symm ⟨D.δ e, D.δ_mem_tensorEqualizer e⟩

private lemma coe_δ' (e : E) :
    Algebra.TensorProduct.map (AlgHom.id A' A') D.descended.val (D.δ' e) = D.δ e := by
  have := congrArg Subtype.val ((AlgHom.tensorEqualizerEquiv A' A' (D.δ.restrictScalars A)
    Algebra.TensorProduct.includeRight).apply_symm_apply ⟨D.δ e, D.δ_mem_tensorEqualizer e⟩)
  rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer] at this
  exact this

private lemma δ'_injective : Function.Injective D.δ' :=
  fun e₁ e₂ h ↦ by
    have := congrArg (fun x ↦ Algebra.TensorProduct.map (AlgHom.id A' A') D.descended.val x) h
    simp only [coe_δ'] at this
    rw [← D.counit e₁, ← D.counit e₂, this]


omit [Module.Flat A A'] in
private lemma descendedMap_comp_map_val (x : A' ⊗[A] D.descended) :
    TensorProduct.mulMap A A' E (Algebra.TensorProduct.map (AlgHom.id A' A') D.descended.val x) =
      D.descendedMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul a' d => simp
  | add x y hx hy => simp [hx, hy]

private lemma descendedMap_δ' (e : E) : D.descendedMap (D.δ' e) = e := by
  rw [← descendedMap_comp_map_val, coe_δ', D.counit]

/-- (Implementation) By flatness, `A' ⊗[A] D.descended → A' ⊗[A] E` is injective. -/
private lemma map_val_injective :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id A' A') D.descended.val) := by
  intro y₁ y₂ h
  apply (AlgHom.tensorEqualizerEquiv A' A' (D.δ.restrictScalars A)
    Algebra.TensorProduct.includeRight).injective
  ext1
  rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.tensorEqualizerEquiv_apply,
    AlgHom.coe_tensorEqualizer, AlgHom.coe_tensorEqualizer]
  exact h

private lemma δ'_descendedMap (x : A' ⊗[A] D.descended) : D.δ' (D.descendedMap x) = x := by
  apply D.map_val_injective
  rw [coe_δ']
  induction x using TensorProduct.inductionOn with
  | tmul a' d =>
    rw [descendedMap_tmul, D.δ_smul, D.δ_of_mem_descended d.2]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Effectivity of descent along flat ring maps**: the comparison map
`A' ⊗[A] D.descended → E` is bijective. -/
theorem bijective_descendedMap : Function.Bijective D.descendedMap :=
  ⟨fun x y h ↦ by rw [← D.δ'_descendedMap x, ← D.δ'_descendedMap y, h],
    fun e ↦ ⟨D.δ' e, D.descendedMap_δ' e⟩⟩

/-- **Effectivity of descent along flat ring maps**: the comparison map
`A' ⊗[A] D.descended ≃ E` is an isomorphism of `A'`-algebras. -/
noncomputable def descendedEquiv : A' ⊗[A] D.descended ≃ₐ[A'] E :=
  AlgEquiv.ofBijective D.descendedMap D.bijective_descendedMap

@[simp]
lemma descendedEquiv_apply (x : A' ⊗[A] D.descended) : D.descendedEquiv x = D.descendedMap x :=
  rfl

end Flat

section FaithfullyFlat

variable [Module.FaithfullyFlat A A']

/-- If `E` is étale over `A'` and `A'` is faithfully flat over `A`, the descended algebra is
étale over `A`. -/
theorem etale_descended [Algebra.Etale A' E] : Algebra.Etale A D.descended :=
  have : Algebra.Etale A' (A' ⊗[A] D.descended) := Algebra.Etale.of_equiv D.descendedEquiv.symm
  Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat A'

/-- If `E` is of finite presentation over `A'` and `A'` is faithfully flat over `A`, the
descended algebra is of finite presentation over `A`. -/
theorem finitePresentation_descended [Algebra.FinitePresentation A' E] :
    Algebra.FinitePresentation A D.descended :=
  have : Algebra.FinitePresentation A' (A' ⊗[A] D.descended) :=
    Algebra.FinitePresentation.equiv D.descendedEquiv.symm
  Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A'


end FaithfullyFlat

end DescentDatum

end Algebra
