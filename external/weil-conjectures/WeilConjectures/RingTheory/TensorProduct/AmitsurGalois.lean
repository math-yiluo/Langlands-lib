/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Amitsur `2`-cocycles of a finite Galois extension

Let `L / K` be a finite Galois extension with group `G`. The Amitsur complex of `K → L` with
coefficients in `𝔾ₘ` is identified with the complex of `G`-equivariant homogeneous cochains
via the isomorphisms `L ⊗_K L ≅ ∏_{σ ∈ G} L`, `x ⊗ y ↦ (x σ(y))_σ` and their higher analogues.
We use this to show that if every Galois `2`-cocycle `G × G → Lˣ` is a coboundary, then so is
every Amitsur `2`-cocycle in `(L ⊗_K L ⊗_K L)ˣ`.

## Main statements

- `AlgHom.bijective_pi_of_injective`: `dim_L A` pairwise distinct `L`-algebra maps `A → L`
  jointly give an isomorphism `A ≅ L^n`.
- `Algebra.TensorProduct.exists_eq_of_cocycle₂`: an Amitsur `2`-cocycle of a finite Galois
  extension is a coboundary, provided every Galois `2`-cocycle is a coboundary.
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- If `A` is a finite-dimensional `L`-algebra and `χ` is an injective family of `L`-algebra
maps `A → L` indexed by a type of cardinality `dim_L A`, then `a ↦ (χ i a)ᵢ` is bijective. -/
theorem AlgHom.bijective_pi_of_injective {L A ι : Type*} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A] [_root_.Finite ι] (χ : ι → A →ₐ[L] L) (hχ : Function.Injective χ)
    (hcard : Nat.card ι = Module.finrank L A) :
    Function.Bijective (fun a i ↦ χ i a) := by
  classical
  have := Fintype.ofFinite ι
  let T : A →ₗ[L] (ι → L) := LinearMap.pi fun i ↦ (χ i).toLinearMap
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    have hli := (linearIndependent_algHom_toLinearMap L A L).comp χ hχ
    rw [Fintype.linearIndependent_iff] at hli
    have hT (a : A) : φ (T a) = 0 := by
      have := Submodule.mem_map_of_mem (f := φ) (LinearMap.mem_range_self T a)
      rwa [hφ, Submodule.mem_bot] at this
    have h0 := hli (fun i ↦ φ fun j ↦ if i = j then 1 else 0) (by
      ext a
      have := hT a
      rw [LinearMap.pi_apply_eq_sum_univ] at this
      simpa [T, mul_comm] using this)
    apply hφ0
    ext x
    have hx : (Pi.single x (1 : L) : ι → L) = fun j ↦ if x = j then 1 else 0 := by
      ext j
      simp [Pi.single_apply, eq_comm]
    simpa [hx] using h0 x
  have hinj : Function.Injective T := by
    rwa [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [Module.finrank_fintype_fun_eq_card, ← hcard, Nat.card_eq_fintype_card]
  exact ⟨hinj, hsurj⟩

namespace Algebra.TensorProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The map `L ⊗_K L → L`, `x ⊗ y ↦ a(x) b(y)`. -/
private noncomputable def φ₂ (a b : L ≃ₐ[K] L) : L ⊗[K] L →ₐ[K] L :=
  productMap (a : L →ₐ[K] L) (b : L →ₐ[K] L)

/-- The map `L ⊗_K L ⊗_K L → L`, `x ⊗ y ⊗ z ↦ a(x) b(y) c(z)`. -/
private noncomputable def φ₃ (a b c : L ≃ₐ[K] L) : L ⊗[K] (L ⊗[K] L) →ₐ[K] L :=
  productMap (a : L →ₐ[K] L) (φ₂ b c)

/-- The map `L^{⊗ 4} → L`, `x ⊗ y ⊗ z ⊗ w ↦ a(x) b(y) c(z) d(w)`. -/
private noncomputable def φ₄ (a b c d : L ≃ₐ[K] L) :
    L ⊗[K] (L ⊗[K] (L ⊗[K] L)) →ₐ[K] L :=
  productMap (a : L →ₐ[K] L) (φ₃ b c d)

private lemma φ₄_comp_δ₀ (a b c d : L ≃ₐ[K] L) :
    (φ₄ a b c d).comp includeRight = φ₃ b c d := by
  ext <;> simp [φ₂, φ₃, φ₄]

private lemma φ₄_comp_δ₁ (a b c d : L ≃ₐ[K] L) :
    (φ₄ a b c d).comp (map (AlgHom.id K L) includeRight) = φ₃ a c d := by
  ext <;> simp [φ₂, φ₃, φ₄]

private lemma φ₄_comp_δ₂ (a b c d : L ≃ₐ[K] L) :
    (φ₄ a b c d).comp (map (AlgHom.id K L) (map (AlgHom.id K L) includeRight)) = φ₃ a b d := by
  ext <;> simp [φ₂, φ₃, φ₄]

private lemma φ₄_comp_δ₃ (a b c d : L ≃ₐ[K] L) :
    (φ₄ a b c d).comp (map (AlgHom.id K L) (map (AlgHom.id K L) includeLeft)) = φ₃ a b c := by
  ext <;> simp [φ₂, φ₃, φ₄]

private lemma φ₃_comp_d₀ (a b c : L ≃ₐ[K] L) :
    (φ₃ a b c).comp includeRight = φ₂ b c := by
  ext <;> simp [φ₂, φ₃]

private lemma φ₃_comp_d₁ (a b c : L ≃ₐ[K] L) :
    (φ₃ a b c).comp (map (AlgHom.id K L) includeRight) = φ₂ a c := by
  ext <;> simp [φ₂, φ₃]

private lemma φ₃_comp_d₂ (a b c : L ≃ₐ[K] L) :
    (φ₃ a b c).comp (map (AlgHom.id K L) includeLeft) = φ₂ a b := by
  ext <;> simp [φ₂, φ₃]

private lemma φ₂_equivariant (s a b : L ≃ₐ[K] L) (x : L ⊗[K] L) :
    s (φ₂ a b x) = φ₂ (s * a) (s * b) x := by
  rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr 1
  ext <;> simp [φ₂]

private lemma φ₃_equivariant (s a b c : L ≃ₐ[K] L) (x : L ⊗[K] (L ⊗[K] L)) :
    s (φ₃ a b c x) = φ₃ (s * a) (s * b) (s * c) x := by
  rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply]
  congr 1
  ext <;> simp [φ₂, φ₃]

/-- `x ⊗ y ↦ x b(y)`, as an `L`-algebra map. -/
private noncomputable def χ₂ (b : L ≃ₐ[K] L) : L ⊗[K] L →ₐ[L] L :=
  lift (AlgHom.id L L) (b : L →ₐ[K] L) fun _ _ ↦ .all _ _

/-- `x ⊗ y ⊗ z ↦ x a(y) b(z)`, as an `L`-algebra map. -/
private noncomputable def χ₃ (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) :
    L ⊗[K] (L ⊗[K] L) →ₐ[L] L :=
  lift (AlgHom.id L L) (φ₂ p.1 p.2) fun _ _ ↦ .all _ _

private lemma χ₂_apply (b : L ≃ₐ[K] L) (x : L ⊗[K] L) : χ₂ b x = φ₂ 1 b x := by
  induction x using TensorProduct.inductionOn with
  | tmul => simp [χ₂, φ₂]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma χ₃_apply (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) (x : L ⊗[K] (L ⊗[K] L)) :
    χ₃ p x = φ₃ 1 p.1 p.2 x := by
  induction x using TensorProduct.inductionOn with
  | tmul => simp [χ₃, φ₃]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma χ₂_injective : Function.Injective (χ₂ (K := K) (L := L)) := by
  intro a b h
  ext y
  simpa [χ₂] using congr($h (1 ⊗ₜ y))

private lemma χ₃_injective : Function.Injective (χ₃ (K := K) (L := L)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [Prod.mk.injEq]
  constructor
  · ext y
    simpa [χ₃, φ₂] using congr($h (1 ⊗ₜ (y ⊗ₜ 1)))
  · ext y
    simpa [χ₃, φ₂] using congr($h (1 ⊗ₜ (1 ⊗ₜ y)))

variable [FiniteDimensional K L] [IsGalois K L]

private lemma bijective_χ₂ : Function.Bijective fun x (b : L ≃ₐ[K] L) ↦ χ₂ b x :=
  AlgHom.bijective_pi_of_injective _ χ₂_injective
    (by rw [IsGalois.card_aut_eq_finrank, Module.finrank_baseChange])

private lemma bijective_χ₃ :
    Function.Bijective fun x (p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L)) ↦ χ₃ p x :=
  AlgHom.bijective_pi_of_injective _ χ₃_injective
    (by rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, Module.finrank_baseChange,
      Module.finrank_tensorProduct])

/-- **Amitsur `2`-cocycles of a Galois extension are coboundaries.** Let `L / K` be a finite
Galois extension with group `G` such that every Galois `2`-cocycle `G × G → Lˣ` is a
coboundary. Let `u` be a unit of `L ⊗_K L ⊗_K L` satisfying the Amitsur cocycle identity
`u₁₂₃ u₀₁₃ = u₀₂₃ u₀₁₂` in `L^{⊗ 4}` (slots numbered `0, …, 3`). Then
`u = v₁₂ (v₀₂)⁻¹ v₀₁` for a unit `v` of `L ⊗_K L`.

The proof identifies `L ⊗_K L` with `∏_{σ ∈ G} L` and `L ⊗_K L ⊗_K L` with
`∏_{(σ, τ) ∈ G × G} L`, turning `u` into the Galois `2`-cocycle
`(σ, τ) ↦ (1 ⊗ σ ⊗ στ)(u)`.
(blueprint: `lemma-cohomology-multiplicative-group--7`, Amitsur-to-Galois step) -/
theorem exists_eq_of_cocycle₂
    (hgal : ∀ f : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ,
      (∀ σ τ ρ, (f σ τ : L) * f (σ * τ) ρ = σ (f τ ρ : L) * f σ (τ * ρ)) →
      ∃ c : (L ≃ₐ[K] L) → Lˣ, ∀ σ τ, (f σ τ : L) * c (σ * τ) = σ (c τ : L) * c σ)
    (u : (L ⊗[K] (L ⊗[K] L))ˣ)
    (hu : (includeRight (u : L ⊗[K] (L ⊗[K] L)) : L ⊗[K] (L ⊗[K] (L ⊗[K] L))) *
        map (AlgHom.id K L) (map (AlgHom.id K L) includeRight) (u : L ⊗[K] (L ⊗[K] L)) =
      map (AlgHom.id K L) includeRight (u : L ⊗[K] (L ⊗[K] L)) *
        map (AlgHom.id K L) (map (AlgHom.id K L) includeLeft) (u : L ⊗[K] (L ⊗[K] L))) :
    ∃ v : (L ⊗[K] L)ˣ, (u : L ⊗[K] (L ⊗[K] L)) =
      includeRight (v : L ⊗[K] L) * map (AlgHom.id K L) includeRight (↑v⁻¹ : L ⊗[K] L) *
        map (AlgHom.id K L) includeLeft (v : L ⊗[K] L) := by
  let f : (L ≃ₐ[K] L) → (L ≃ₐ[K] L) → Lˣ := fun σ τ ↦
    Units.map ((φ₃ 1 σ (σ * τ) : L ⊗[K] (L ⊗[K] L) →ₐ[K] L) : L ⊗[K] (L ⊗[K] L) →* L) u
  have hf (σ τ ρ : L ≃ₐ[K] L) :
      (f σ τ : L) * f (σ * τ) ρ = σ (f τ ρ : L) * f σ (τ * ρ) := by
    have h := congrArg (φ₄ 1 σ (σ * τ) (σ * τ * ρ)) hu
    rw [map_mul, map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply,
      ← AlgHom.comp_apply, φ₄_comp_δ₀, φ₄_comp_δ₁, φ₄_comp_δ₂, φ₄_comp_δ₃] at h
    simp only [f, Units.coe_map, MonoidHom.coe_ofClass, φ₃_equivariant, mul_one, mul_assoc]
    rw [mul_assoc] at h
    linear_combination -h
  obtain ⟨c, hc⟩ := hgal f hf
  obtain ⟨w, hw⟩ := bijective_χ₂.2 fun σ ↦ (c σ : L)
  obtain ⟨w', hw'⟩ := bijective_χ₂.2 fun σ ↦ (((c σ)⁻¹ : Lˣ) : L)
  have hww' : w * w' = 1 := bijective_χ₂.1 <| funext fun σ ↦ by
    have h1 := congrFun hw σ
    have h2 := congrFun hw' σ
    simp only at h1 h2 ⊢
    rw [map_mul, h1, h2, map_one, Units.mul_inv]
  let v : (L ⊗[K] L)ˣ := ⟨w, w', hww', mul_comm w' w ▸ hww'⟩
  refine ⟨v, bijective_χ₃.1 <| funext fun p ↦ ?_⟩
  obtain ⟨a, b⟩ := p
  have hφw (σ : L ≃ₐ[K] L) : φ₂ 1 σ w = c σ := by
    rw [← χ₂_apply]; exact congrFun hw σ
  have hφw' (σ : L ≃ₐ[K] L) : φ₂ 1 σ w' = ((c σ)⁻¹ : Lˣ) := by
    rw [← χ₂_apply]; exact congrFun hw' σ
  have hab : φ₂ a b w = a (c (a⁻¹ * b)) := by
    rw [← hφw, φ₂_equivariant, mul_one, mul_inv_cancel_left]
  have key := hc a (a⁻¹ * b)
  simp only [f, Units.coe_map, MonoidHom.coe_ofClass, mul_inv_cancel_left] at key
  simp only [χ₃_apply, map_mul]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, φ₃_comp_d₀, φ₃_comp_d₁,
    φ₃_comp_d₂, hab, hφw]
  change _ = _ * φ₂ 1 b w' * _
  rw [hφw', Units.val_inv_eq_inv_val]
  have hb : (c b : L) ≠ 0 := (c b).ne_zero
  field_simp
  linear_combination key

end Algebra.TensorProduct
