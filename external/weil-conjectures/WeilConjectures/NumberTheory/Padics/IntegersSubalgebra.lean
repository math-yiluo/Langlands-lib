/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.NumberTheory.Padics.IntegersModPow
public import WeilConjectures.RingTheory.TensorBijectiveOfStages

/-!
# `ℚ̄_ℓ ⊗_{𝒪_E} A` as the colimit of the `𝒪_F ⊗_{𝒪_E} A`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` and `A` an `𝒪_E`-module. For the finite extensions
`F ⊇ E` inside `ℚ̄_ℓ`, the rings of integers `𝒪_F` are `𝒪_E`-subalgebras of `ℚ̄_ℓ`
(`PadicAlgCl.integersSubalgebra`, isomorphic to `PadicAlgCl.integers ℓ F` by
`PadicAlgCl.integersEquivIntegersSubalgebra`), forming a directed family which exhausts
`ℚ̄_ℓ` after inverting `ℓ`. Hence `ℚ̄_ℓ ⊗_{𝒪_E} A = colim_{F, n} ℓ⁻ⁿ (𝒪_F ⊗_{𝒪_E} A)`, and a map
`T : ℚ̄_ℓ ⊗_{𝒪_E} A → B` is bijective as soon as `B` is the colimit of the same system
compatibly with `T` (`PadicAlgCl.bijective_of_integersSubalgebra`).
-/

@[expose] public section

open TensorProduct IntermediateField

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

lemma norm_natCast_self_padicAlgCl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ :=
  norm_algebraMap_natCast_self l (PadicAlgCl l)

/-- The ring of integers `𝒪_F` of an extension `F ⊇ E` inside `ℚ̄_ℓ`, as an `𝒪_E`-subalgebra of
`ℚ̄_ℓ`: the elements of `F` of norm at most `1`. -/
noncomputable def integersSubalgebra (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (h : E ≤ F) :
    Subalgebra (integers l E) (PadicAlgCl l) where
  carrier := {z | z ∈ F ∧ ‖z‖ ≤ 1}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha.2).trans hb.2⟩
  add_mem' {a b} ha hb := ⟨add_mem ha.1 hb.1,
    (PadicAlgCl.isNonarchimedean l a b).trans (max_le ha.2 hb.2)⟩
  algebraMap_mem' r := ⟨h (r : E).2, by
    have hr : ‖algebraMap E (PadicAlgCl l) (r : E)‖₊ ≤ 1 := r.2
    exact hr⟩

variable {l E} in
lemma mem_integersSubalgebra {F : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : E ≤ F)
    (z : PadicAlgCl l) : z ∈ integersSubalgebra l E F h ↔ z ∈ F ∧ ‖z‖ ≤ 1 :=
  Iff.rfl

/-- `𝒪_F` as a subalgebra of `ℚ̄_ℓ` is `PadicAlgCl.integers ℓ F`. -/
noncomputable def integersEquivIntegersSubalgebra (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (h : E ≤ F) : integers l F ≃+* integersSubalgebra l E F h where
  toFun x := ⟨((x : F) : PadicAlgCl l), (x : F).2, by
    have hx : ‖algebraMap F (PadicAlgCl l) (x : F)‖₊ ≤ 1 := x.2
    exact hx⟩
  invFun z := ⟨⟨z, z.2.1⟩, by
    change ‖(z : PadicAlgCl l)‖₊ ≤ 1
    exact z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable {l E}

lemma integersSubalgebra_mono {F F' : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : E ≤ F)
    (h' : F ≤ F') : integersSubalgebra l E F h ≤ integersSubalgebra l E F' (h.trans h') :=
  fun _ hz ↦ ⟨h' hz.1, hz.2⟩

variable (l E) in
/-- The finite extensions of `ℚ_ℓ` in `ℚ̄_ℓ` containing `E`. -/
abbrev FiniteIntermediateFieldOver : Type :=
  {F : FiniteIntermediateField l // E ≤ F.1}

variable (l E) in
/-- The family `F ↦ 𝒪_F` over the finite extensions `F ⊇ E`. -/
noncomputable abbrev integersSubalgebraFamily (F : FiniteIntermediateFieldOver l E) :
    Subalgebra (integers l E) (PadicAlgCl l) :=
  integersSubalgebra l E F.1.1 F.2

lemma algebraMap_natCast_ne_zero :
    algebraMap (integers l E) (PadicAlgCl l) (l : integers l E) ≠ 0 := by
  rw [map_natCast]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

lemma integersSubalgebraFamily_directed (F F' : FiniteIntermediateFieldOver l E) :
    ∃ F'', integersSubalgebraFamily l E F ≤ integersSubalgebraFamily l E F'' ∧
      integersSubalgebraFamily l E F' ≤ integersSubalgebraFamily l E F'' :=
  ⟨⟨⟨F.1.1 ⊔ F'.1.1, inferInstance⟩, F.2.trans le_sup_left⟩,
    integersSubalgebra_mono F.2 le_sup_left, integersSubalgebra_mono F'.2 le_sup_right⟩

/-- Every element of `ℚ̄_ℓ` is `ℓ⁻ⁿ o` with `o ∈ 𝒪_F` for a finite extension `F ⊇ E`. -/
lemma integersSubalgebraFamily_exhaustive [FiniteDimensional ℚ_[l] E] (c : PadicAlgCl l) :
    ∃ (F : FiniteIntermediateFieldOver l E) (n : ℕ),
      algebraMap (integers l E) (PadicAlgCl l) (l : integers l E) ^ n * c ∈
        integersSubalgebraFamily l E F := by
  have : FiniteDimensional ℚ_[l] ℚ_[l]⟮c⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)
  let F : FiniteIntermediateFieldOver l E := ⟨⟨E ⊔ ℚ_[l]⟮c⟯, inferInstance⟩, le_sup_left⟩
  have hcF : c ∈ F.1.1 :=
    (le_sup_right : ℚ_[l]⟮c⟯ ≤ E ⊔ ℚ_[l]⟮c⟯) (IntermediateField.mem_adjoin_simple_self _ c)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖c‖ + 1) by positivity)
    (inv_prime_lt_one l)
  refine ⟨F, n, ?_, ?_⟩
  · rw [map_natCast]
    exact mul_mem (pow_mem (IntermediateField.natCast_mem _ l) n) hcF
  · rw [map_natCast, norm_mul, norm_pow, norm_natCast_self_padicAlgCl]
    rw [lt_div_iff₀ (by positivity)] at hn
    calc (l : ℝ)⁻¹ ^ n * ‖c‖ ≤ (l : ℝ)⁻¹ ^ n * (‖c‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (inv_prime_pos l).le n)
      _ ≤ 1 := hn.le

/-- **Bijectivity criterion for a map out of `ℚ̄_ℓ ⊗_{𝒪_E} A`.** Let `T : ℚ̄_ℓ ⊗_{𝒪_E} A → B` be
additive. Suppose every element of `B` is `T(ℓ⁻ⁿ τ)` for some finite `F ⊇ E`, `n` and
`τ ∈ 𝒪_F ⊗_{𝒪_E} A`, and that `T(ℓ⁻ⁿ τ) = 0` forces `ℓᵐ τ` to vanish in `𝒪_{F'} ⊗_{𝒪_E} A` for
some finite `F' ⊇ F` and some `m`. Then `T` is bijective. -/
theorem bijective_of_integersSubalgebra [FiniteDimensional ℚ_[l] E] {A : Type*} [AddCommGroup A]
    [Module (integers l E) A] {B : Type*} [AddCommGroup B]
    (T : PadicAlgCl l ⊗[integers l E] A →+ B)
    (hsurj : ∀ b : B, ∃ (F : FiniteIntermediateFieldOver l E) (n : ℕ)
      (τ : integersSubalgebraFamily l E F ⊗[integers l E] A),
        T (Subalgebra.stageTensorMap (l : integers l E) (integersSubalgebraFamily l E) F n τ) = b)
    (hinj : ∀ (F : FiniteIntermediateFieldOver l E) (n : ℕ)
      (τ : integersSubalgebraFamily l E F ⊗[integers l E] A),
      T (Subalgebra.stageTensorMap (l : integers l E) (integersSubalgebraFamily l E) F n τ) = 0 →
        ∃ (F' : FiniteIntermediateFieldOver l E)
          (h : integersSubalgebraFamily l E F ≤ integersSubalgebraFamily l E F') (m : ℕ),
          (l : integers l E) ^ m • (Subalgebra.inclusion h).toLinearMap.rTensor A τ = 0) :
    Function.Bijective T :=
  have : Nonempty (FiniteIntermediateFieldOver l E) := ⟨⟨⟨E, inferInstance⟩, le_rfl⟩⟩
  Subalgebra.bijective_of_stageTensorMap (x := (l : integers l E))
    (O := integersSubalgebraFamily l E) algebraMap_natCast_ne_zero
    integersSubalgebraFamily_directed integersSubalgebraFamily_exhaustive T hsurj hinj

end PadicAlgCl
