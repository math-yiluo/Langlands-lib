/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Noetherian approximation of a flat algebra along a fibre

Let `B` be a flat, finitely presented `A`-algebra with a section `s`, and `y` a prime of `A`.
Then `B` and `s` descend to a finite type algebra `B₁` with a section `s₁` over a noetherian
subring `A₁` of `A`, such that `B₁` is flat over `A₁` at the points lying under `y`.

## Main statements

- `PrimeSpectrum.exists_isPushout_forall_flat_of_tensorProduct`: descending a flat model along a
  fibre.
- `PrimeSpectrum.exists_isPushout_forall_flat`: noetherian approximation along a fibre.

The general facts on the flat locus used here (openness, persistence under enlarging the base,
lifting points along base change) are in
`WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.

## References

- Stacks Project, Tags `00R6`, `055Q`
-/

@[expose] public section

universe u

open TensorProduct

namespace PrimeSpectrum

/-- **Descending a flat model along a fibre.** Let `B = A ⊗[R₀] B₀` with a section `s` induced by
a section `s₀` of `B₀`, and let `A₁` be a noetherian `R₀`-algebra mapping to `A` such that
`A₁ ⊗[R₀] B₀` is flat over `A₁` at every prime lying under a prime of `A ⊗[R₀] B₀` over `y`.
Then `B₁ = A₁ ⊗[R₀] B₀` with the section induced by `s₀` is a model of `B` over `A₁` which is
flat over `A₁` at every prime lying over `y ∩ A₁`: such primes lie under primes of `B` over `y`. -/
theorem exists_isPushout_forall_flat_of_tensorProduct {R₀ A₁ A B₀ B : Type u} [CommRing R₀]
    [CommRing A₁] [CommRing A] [CommRing B₀] [CommRing B] [Algebra R₀ A₁] [Algebra A₁ A]
    [Algebra R₀ A] [IsScalarTower R₀ A₁ A] [Algebra R₀ B₀] [Algebra A B] [Algebra B₀ B]
    [Algebra R₀ B] [IsScalarTower R₀ A B] [IsScalarTower R₀ B₀ B] [Algebra.IsPushout R₀ A B₀ B]
    [IsNoetherianRing A₁] [Algebra.FiniteType R₀ B₀] (s : B →ₐ[A] A) (s₀ : B₀ →ₐ[R₀] R₀)
    (hs : ∀ b, algebraMap R₀ A (s₀ b) = s (algebraMap B₀ B b)) (y : PrimeSpectrum A)
    (hflat : ∀ q : PrimeSpectrum (A ⊗[R₀] B₀), comap (algebraMap A (A ⊗[R₀] B₀)) q = y →
      Module.Flat A₁ (Localization.AtPrime (comap (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R₀ A₁ A) (AlgHom.id R₀ B₀) : A₁ ⊗[R₀] B₀ →+* A ⊗[R₀] B₀)
          q).asIdeal)) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ A) (_ : Algebra A₁ B₁)
      (_ : Algebra B₁ B) (_ : Algebra A₁ B) (_ : IsScalarTower A₁ A B)
      (_ : IsScalarTower A₁ B₁ B),
      IsNoetherianRing A₁ ∧ Algebra.FiniteType A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B ∧
      ∃ s₁ : B₁ →ₐ[A₁] A₁, (∀ b, algebraMap A₁ A (s₁ b) = s (algebraMap B₁ B b)) ∧
        ∀ q : PrimeSpectrum B₁,
          comap (algebraMap A₁ B₁) q = comap (algebraMap A₁ A) y →
          Module.Flat A₁ (Localization.AtPrime q.asIdeal) := by
  classical
  let e₀ : A ⊗[R₀] B₀ ≃ₐ[A] B := Algebra.IsPushout.equiv R₀ A B₀ B
  let φ : A₁ ⊗[R₀] B₀ →ₐ[R₀] B := (e₀.toAlgHom.restrictScalars R₀).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ A₁ A) (AlgHom.id R₀ B₀))
  let : Algebra (A₁ ⊗[R₀] B₀) B := φ.toRingHom.toAlgebra
  let : Algebra A₁ B := ((algebraMap A B).comp (algebraMap A₁ A)).toAlgebra
  have : IsScalarTower A₁ A B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A₁ (A₁ ⊗[R₀] B₀) B := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, φ, e₀, Algebra.IsPushout.equiv_tmul,
      Algebra.TensorProduct.algebraMap_apply]
  have : Algebra.IsPushout A₁ A (A₁ ⊗[R₀] B₀) B := by
    let : Algebra (A₁ ⊗[R₀] B₀) (A ⊗[A₁] (A₁ ⊗[R₀] B₀)) := Algebra.TensorProduct.rightAlgebra
    refine Algebra.IsPushout.of_equiv
      ((Algebra.TensorProduct.cancelBaseChange R₀ A₁ A A B₀).trans e₀) (RingHom.ext fun x ↦ ?_)
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      simp [RingHom.algebraMap_toAlgebra, φ, e₀, Algebra.IsPushout.equiv_tmul,
        Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let s₁ : A₁ ⊗[R₀] B₀ →ₐ[A₁] A₁ := Algebra.TensorProduct.lift (Algebra.ofId A₁ A₁)
    ((Algebra.ofId R₀ A₁).comp s₀) fun _ _ ↦ Commute.all _ _
  refine ⟨A₁, A₁ ⊗[R₀] B₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, s₁, fun b ↦ ?_, fun q₁ hq₁ ↦ ?_⟩
  · induction b using TensorProduct.inductionOn with
    | tmul r b =>
      simp only [s₁, RingHom.algebraMap_toAlgebra, φ, e₀]
      simp [Algebra.IsPushout.equiv_tmul, ← IsScalarTower.algebraMap_apply, hs]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  · obtain ⟨q, hqy, hqq₁⟩ := exists_comap_eq_of_isPushout (B := B) y.asIdeal.ResidueField
      (Ideal.ker_algebraMap_residueField _) q₁ hq₁
    have h₁ : comap (algebraMap A (A ⊗[R₀] B₀)) (comap (e₀ : A ⊗[R₀] B₀ →+* B) q) = y := by
      rw [← comap_comp_apply, ← hqy]
      congr 1
      exact RingHom.ext fun a ↦ e₀.commutes a
    have h₂ : comap (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ A₁ A)
        (AlgHom.id R₀ B₀) : A₁ ⊗[R₀] B₀ →+* A ⊗[R₀] B₀) (comap (e₀ : A ⊗[R₀] B₀ →+* B) q) =
        q₁ := by
      rw [← comap_comp_apply, ← hqq₁]
      rfl
    have := hflat _ h₁
    rwa [h₂] at this

/-- **Noetherian approximation along a fibre.** Let `B` be a flat, finitely presented `A`-algebra
with a section `s`, and `y` a prime of `A`. Then `B` and `s` descend to a finite type algebra `B₁`
with a section `s₁` over a noetherian ring `A₁` mapping to `A`, such that `B₁` is flat over `A₁`
at the points lying over `y ∩ A₁`.

Each point of `Spec B` has a neighbourhood on which some noetherian model is flat (Stacks `00R6`,
`Module.exists_fg_flat_localization_tensor`, and openness of the flat locus). The fibre over `y`
is quasi-compact, so a single model suffices, and every point of the fibre of the model lies under
a point of the fibre of `B`. -/
theorem exists_isPushout_forall_flat (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] (s : B →ₐ[A] A) (y : PrimeSpectrum A) :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ A) (_ : Algebra A₁ B₁)
      (_ : Algebra B₁ B) (_ : Algebra A₁ B) (_ : IsScalarTower A₁ A B)
      (_ : IsScalarTower A₁ B₁ B),
      IsNoetherianRing A₁ ∧ Algebra.FiniteType A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B ∧
      ∃ s₁ : B₁ →ₐ[A₁] A₁, (∀ b, algebraMap A₁ A (s₁ b) = s (algebraMap B₁ B b)) ∧
        ∀ q : PrimeSpectrum B₁,
          comap (algebraMap A₁ B₁) q = comap (algebraMap A₁ A) y →
          Module.Flat A₁ (Localization.AtPrime q.asIdeal) := by
  classical
  obtain ⟨A₀, B₀, _, _, _, _, hA₀, hB₀, hpush, s₀, hs⟩ :=
    Algebra.FinitePresentation.exists_fg_subalgebra_with_section s
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A (A ⊗[A₀] B₀) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv A₀ A B₀ B).toLinearEquiv
  obtain ⟨R₁, hR₁, hflat⟩ := exists_fg_forall_flat_localization_tensor (R₀ := A₀) (S₀ := B₀) y
  have : Algebra.FiniteType A₀ R₁ := (Subalgebra.fg_iff_finiteType _).mp hR₁
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing A₀ R₁
  exact exists_isPushout_forall_flat_of_tensorProduct (A₁ := R₁) s s₀ hs y hflat

end PrimeSpectrum
