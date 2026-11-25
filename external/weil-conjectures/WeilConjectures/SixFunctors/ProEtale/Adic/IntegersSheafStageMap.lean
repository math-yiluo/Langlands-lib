/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis
public import WeilConjectures.RingTheory.TensorBijectiveOfBasis
public import WeilConjectures.NumberTheory.Padics.IntegersSubalgebra

/-!
# `Φ(𝒪_{F,T}) = 𝒪_F ⊗_{𝒪_E} Φ(𝒪_{E,T})` for an additive functor `Φ`

Let `Φ` be an additive functor from abelian sheaves on `T_proét` to abelian groups (typically
`Γ(W, p^* Rⁱg_* -)`), `E ⊆ F` finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, and
`θ : A ≅ Φ(𝒪_{E,T})` an identification with an `𝒪_E`-module `A` which is `𝒪_E`-linear, `𝒪_E`
acting on `Φ(𝒪_{E,T})` through `Φ` of the multiplications. Then
`𝒪_F ⊗_{𝒪_E} A → Φ(𝒪_{F,T})`, `o ⊗ a ↦ Φ(o • -)(θ a)` (`AlgebraicGeometry.ProEtale.stageMap`),
is bijective (`AlgebraicGeometry.ProEtale.bijective_stageMap`), `𝒪_{F,T}` being a finite direct
sum of copies of `𝒪_{E,T}` (`WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis`), and
compatible with the inclusions `𝒪_F ⊆ 𝒪_{F'}` (`AlgebraicGeometry.ProEtale.stageMap_rTensor`).
Here `𝒪_F` is the `𝒪_E`-subalgebra `PadicAlgCl.integersSubalgebraFamily` of `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl TensorProduct

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section Stage

open TensorProduct

variable {T : Scheme.{u}} (Φ : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1} ⥤ Ab.{u + 1})
  [Φ.Additive] (E : FiniteIntermediateField l) {A : Type*} [AddCommGroup A]
  [Module (integers l E.1) A]
  (θ : A ≃+ Φ.obj ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (padicIntegersSheaf T l E.1)))
  (hθ : ∀ (r : integers l E.1) (a : A),
    θ (r • a) = Φ.map (padicIntegersSheafMulOfLE T (le_refl E.1) r) (θ a))

/-- The identification `𝒪_F ≅ PadicAlgCl.integers ℓ F` for `F ⊇ E`. -/
noncomputable abbrev integersSubalgebraFamilyEquiv (F : FiniteIntermediateFieldOver l E.1) :
    integersSubalgebraFamily l E.1 F ≃+* integers l F.1.1 :=
  (integersEquivIntegersSubalgebra l E.1 F.1.1 F.2).symm

lemma integersSubalgebraFamilyEquiv_smul (F : FiniteIntermediateFieldOver l E.1)
    (r : integers l E.1) (o : integersSubalgebraFamily l E.1 F) :
    integersSubalgebraFamilyEquiv E F (r • o) =
      integersInclusion l (E := E.1) (F := F.1.1) F.2 r * integersSubalgebraFamilyEquiv E F o :=
  rfl

/-- The biadditive map `(o, a) ↦ Φ(o • -)(θ a)`, `𝒪_F × A → Φ(𝒪_{F,T})`. -/
noncomputable def stageBiadd (F : FiniteIntermediateFieldOver l E.1) :
    integersSubalgebraFamily l E.1 F →+ A →+
      Φ.obj ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntegersSheaf T l F.1.1)) :=
  AddMonoidHom.mk' (fun o ↦ (Φ.map (padicIntegersSheafMulOfLE T (E := E) (F := F.1) F.2
      (integersSubalgebraFamilyEquiv E F o))).hom.comp θ.toAddMonoidHom) fun o o' ↦ by
    ext a
    simp only [RingEquiv.map_add, padicIntegersSheafMulOfLE_add, Functor.map_add,
      AddCommGrpCat.hom_add, AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply]

include hθ in
lemma stageBiadd_balanced (F : FiniteIntermediateFieldOver l E.1) (r : integers l E.1)
    (o : integersSubalgebraFamily l E.1 F) (a : A) :
    stageBiadd Φ E θ F (r • o) a = stageBiadd Φ E θ F o (r • a) := by
  simp only [stageBiadd, AddMonoidHom.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, hθ, integersSubalgebraFamilyEquiv_smul]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, padicIntegersSheafMulOfLE_refl_comp]

/-- The map `𝒪_F ⊗_{𝒪_E} A → Φ(𝒪_{F,T})`, `o ⊗ a ↦ Φ(o • -)(θ a)`. -/
noncomputable def stageMap (F : FiniteIntermediateFieldOver l E.1) :
    integersSubalgebraFamily l E.1 F ⊗[integers l E.1] A →+
      Φ.obj ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (padicIntegersSheaf T l F.1.1)) :=
  liftOfBalanced (stageBiadd Φ E θ F) (stageBiadd_balanced Φ E θ hθ F)

lemma stageMap_tmul (F : FiniteIntermediateFieldOver l E.1)
    (o : integersSubalgebraFamily l E.1 F) (a : A) :
    stageMap Φ E θ hθ F (o ⊗ₜ a) = Φ.map (padicIntegersSheafMulOfLE T (E := E) (F := F.1) F.2
      (integersSubalgebraFamilyEquiv E F o)) (θ a) :=
  rfl

/-- `𝒪_F ≅ PadicAlgCl.integers ℓ F` is `𝒪_E`-linear. -/
noncomputable def integersSubalgebraFamilyLinearEquiv (F : FiniteIntermediateFieldOver l E.1) :
    letI := (integersInclusion l (E := E.1) (F := F.1.1) F.2).toAlgebra
    integers l F.1.1 ≃ₗ[integers l E.1] integersSubalgebraFamily l E.1 F :=
  letI := (integersInclusion l (E := E.1) (F := F.1.1) F.2).toAlgebra
  { (integersSubalgebraFamilyEquiv E F).symm.toAddEquiv with
    map_smul' r x := (integersSubalgebraFamilyEquiv E F).injective (by
      change integersSubalgebraFamilyEquiv E F ((integersSubalgebraFamilyEquiv E F).symm _) =
        integersSubalgebraFamilyEquiv E F (r • (integersSubalgebraFamilyEquiv E F).symm x)
      rw [RingEquiv.apply_symm_apply, integersSubalgebraFamilyEquiv_smul,
        RingEquiv.apply_symm_apply]
      exact Algebra.smul_def r x) }

lemma addCommGrpCat_sum_apply {Y Z : Ab.{u + 1}} {ι : Type*} (s : Finset ι) (φ : ι → (Y ⟶ Z))
    (y : Y) :
    (∑ j ∈ s, φ j) y = ∑ j ∈ s, φ j y :=
  map_sum ({ toFun ψ := ψ y, map_zero' := rfl, map_add' _ _ := rfl } : (Y ⟶ Z) →+ Z) φ s

/-- **`Φ(𝒪_{F,T}) = 𝒪_F ⊗_{𝒪_E} A`**: `stageMap` is bijective, `𝒪_F` being finite free over `𝒪_E`
with continuous coordinates. -/
theorem bijective_stageMap (F : FiniteIntermediateFieldOver l E.1) :
    Function.Bijective (stageMap Φ E θ hθ F) := by
  obtain ⟨d, b, hb⟩ := exists_basis_integersInclusion (E := E.1) (F := F.1.1) F.2
  let := (integersInclusion l (E := E.1) (F := F.1.1) F.2).toAlgebra
  classical
  refine bijective_liftOfBalanced (b.map (integersSubalgebraFamilyLinearEquiv E F)) _ _
    (fun j ↦ θ.symm.toAddMonoidHom.comp
      (Φ.map (padicIntegersSheafCoord T (E := E) (F := F.1) F.2 b hb j)).hom) (fun y ↦ ?_)
    (fun o a j ↦ ?_)
  · simp only [stageBiadd, AddMonoidHom.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, Module.Basis.map_apply]
    change ∑ j, Φ.map _ (Φ.map _ y) = y
    simp_rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rw [← addCommGrpCat_sum_apply, ← Functor.map_sum]
    have he (j : Fin d) : integersSubalgebraFamilyEquiv E F
        (integersSubalgebraFamilyLinearEquiv E F (b j)) = b j :=
      RingEquiv.apply_symm_apply _ _
    simp_rw [he, sum_padicIntegersSheafCoord_comp_mul, CategoryTheory.Functor.map_id]
    rfl
  · have key := padicIntegersSheafMulOfLE_comp_coord (X := T) (E := E) (F := F.1) F.2 b hb
      (integersSubalgebraFamilyEquiv E F o) j
    have hr : (b.map (integersSubalgebraFamilyLinearEquiv E F)).repr o j =
        b.repr (integersSubalgebraFamilyEquiv E F o) j := rfl
    change θ.symm (Φ.map _ (Φ.map _ (θ a))) = _
    rw [hr, AddEquiv.symm_apply_eq, hθ, ← key, Functor.map_comp, ConcreteCategory.comp_apply]

/-- `stageMap` is compatible with the inclusions `𝒪_F ⊆ 𝒪_{F'}`. -/
lemma stageMap_rTensor {F F' : FiniteIntermediateFieldOver l E.1} (hFF' : F.1.1 ≤ F'.1.1)
    (hs : integersSubalgebraFamily l E.1 F ≤ integersSubalgebraFamily l E.1 F')
    (τ : integersSubalgebraFamily l E.1 F ⊗[integers l E.1] A) :
    stageMap Φ E θ hθ F' ((Subalgebra.inclusion hs).toLinearMap.rTensor A τ) =
      Φ.map ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (padicIntegersSheafMapOfLE T l hFF')) (stageMap Φ E θ hθ F τ) := by
  induction τ using TensorProduct.inductionOn with
  | add τ τ' hτ hτ' => simp only [map_add, hτ, hτ']
  | tmul o a =>
    change Φ.map (padicIntegersSheafMulOfLE T (E := E) (F := F'.1) F'.2
        (integersSubalgebraFamilyEquiv E F' (Subalgebra.inclusion hs o))) (θ a) =
      (Φ.map (padicIntegersSheafMulOfLE T (E := E) (F := F.1) F.2
        (integersSubalgebraFamilyEquiv E F o)) ≫ Φ.map ((sheafCompose _
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntegersSheafMapOfLE T l hFF'))) (θ a)
    rw [← Functor.map_comp, padicIntegersSheafMulOfLE_comp_mapOfLE]
    rfl

end Stage

/-- `ℓ⁻ⁿ o = ℓ⁻ⁿ o` for `o ∈ 𝒪_F`, seen in `ℚ̄_ℓ` through `𝒪_E` and through `𝒪_F`. -/
lemma algebraMap_natCast_pow_inv_mul_eq (E : FiniteIntermediateField l)
    (F : FiniteIntermediateFieldOver l E.1)
    (n : ℕ) (o : integersSubalgebraFamily l E.1 F) :
    ((algebraMap (integers l E.1) (PadicAlgCl l)) (l : integers l E.1) ^ n)⁻¹ *
        (o : PadicAlgCl l) =
      ((l : PadicAlgCl l) ^ n)⁻¹ *
        algebraMap (integers l F.1.1) (PadicAlgCl l) (integersSubalgebraFamilyEquiv E F o) := by
  rw [map_natCast]
  rfl

lemma natCast_pow_smul_eq_nsmul {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (n m : ℕ) (x : A) : ((n : R) ^ m) • x = (n ^ m) • x := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end AlgebraicGeometry.ProEtale
