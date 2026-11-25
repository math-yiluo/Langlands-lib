/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Weakly étale algebras: localizations and algebras over fields

A localization map `R → S⁻¹R` is weakly étale (Stacks, Tag 092J (1)): it is flat, and the
multiplication `S⁻¹R ⊗[R] S⁻¹R → S⁻¹R` is bijective. This is ported from the `proetale` project
(`Proetale.Mathlib.RingTheory.WeaklyEtale.Localization`).

Over a field `K`, the residue fields of a weakly étale `K`-algebra are algebraic over `K`
(compare Stacks, Tag 092Q): if `y` had transcendental image in the residue field of a local
weakly étale `K`-algebra `R`, then `R` would be flat over `K[X]` via `X ↦ y`, so `R` would be
flat over `K[X] ⊗[K] K[X]` via `R ⊗[K] R → R`; but the regular element `X ⊗ 1 - 1 ⊗ X` acts
as `y - y = 0` on `R`. In particular a nonzero weakly étale algebra over an algebraically
closed field `K` has a `K`-point.

## Main results

- `Algebra.WeaklyEtale.of_isLocalization`: a localization of `R` is a weakly étale `R`-algebra.
- `Algebra.WeaklyEtale.isAlgebraic_residueField`: the residue field of a local weakly étale
  algebra over a field `K` is algebraic over `K`.
- `Algebra.WeaklyEtale.nonempty_algHom_of_isAlgClosed`: a nonzero weakly étale algebra over an
  algebraically closed field `K` has a `K`-algebra map to `K`.
-/

@[expose] public section

namespace Algebra.WeaklyEtale

/-- If `T` is the localization of `R` at a submonoid `S`, then `T` is weakly étale over `R`. -/
@[stacks 092J "(1)"]
theorem of_isLocalization (R : Type*) [CommRing R] (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T] :
    Algebra.WeaklyEtale R T where
  flat := IsLocalization.flat T S
  flat_lmul' :=
    RingHom.Flat.of_bijective
      (f := (Algebra.TensorProduct.lmul' R (S := T)).toRingHom)
      (IsLocalization.bijective_linearMap_mul' (R := R) (A := T) S)

/-- The canonical localization `R → Localization S` is weakly étale. -/
instance localization (R : Type*) [CommRing R] (S : Submonoid R) :
    Algebra.WeaklyEtale R (Localization S) :=
  of_isLocalization R S _

open Polynomial _root_.TensorProduct

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [WeaklyEtale K R]

/-- A nonzero weakly étale algebra `R` over a field `K` has no element `y` all of whose nonzero
polynomial expressions `p(y)` are units: otherwise `R` would be flat over `K[X] ⊗[K] K[X]` via
`X ↦ y` on both factors and the multiplication `R ⊗[K] R → R`, while the regular element
`X ⊗ 1 - 1 ⊗ X` acts as zero on `R`. -/
theorem not_forall_isUnit_aeval [Nontrivial R] (y : R) :
    ¬ ∀ p : K[X], p ≠ 0 → IsUnit (aeval y p) := by
  intro hy
  let φ : K[X] →ₐ[K] R := aeval y
  have hφ : φ.toRingHom.Flat := by
    let := φ.toRingHom.toAlgebra
    have : Module.IsTorsionFree K[X] R := ⟨fun p hp x x' hxx' ↦ by
      have hu := (hy p hp.ne_zero).isRegular.left
      exact hu hxx'⟩
    change Module.Flat K[X] R
    infer_instance
  let χ := (Algebra.TensorProduct.lmul' K (S := R)).comp (Algebra.TensorProduct.map φ φ)
  have hχ : χ.toRingHom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.tensorProductMap hφ hφ) (flat_lmul' K R)
  let d : K[X] ⊗[K] K[X] := X ⊗ₜ 1 - 1 ⊗ₜ X
  have hχd : χ d = 0 := by simp [χ, d, φ]
  let e := polyEquivTensor K K[X]
  have : IsDomain (K[X] ⊗[K] K[X]) :=
    MulEquiv.isDomain _ e.symm.toRingEquiv.toMulEquiv
  have hd : d ≠ 0 := by
    have : d = e (C X - X) := by simp [e, d, polyEquivTensor_apply]
    rw [this, ne_eq, map_eq_zero_iff _ e.injective]
    intro h
    have := congrArg (coeff · 1) h
    simp at this
  let := χ.toRingHom.toAlgebra
  have : Module.Flat (K[X] ⊗[K] K[X]) R := hχ
  have h := Module.Flat.isSMulRegular_of_isRegular (M := R) (IsRegular.of_ne_zero hd)
  refine one_ne_zero (α := R) (h ?_)
  change χ d * 1 = χ d * 0
  rw [hχd, zero_mul, zero_mul]

/-- The residue field of a local weakly étale algebra over a field `K` is algebraic over `K`.
(compare Stacks, Tag 092Q) -/
theorem isAlgebraic_residueField [IsLocalRing R] :
    Algebra.IsAlgebraic K (IsLocalRing.ResidueField R) := by
  refine ⟨fun x ↦ ?_⟩
  by_contra hx
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  refine not_forall_isUnit_aeval (K := K) y fun p hp ↦ ?_
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro h
  refine hx ⟨p, hp, ?_⟩
  rw [← h]
  exact aeval_algebraMap_apply (IsLocalRing.ResidueField R) y p

/-- A nonzero weakly étale algebra over an algebraically closed field `K` has a `K`-algebra map
to `K`, through the residue field at a maximal ideal, algebraic over `K`. -/
theorem nonempty_algHom_of_isAlgClosed [IsAlgClosed K] [Nontrivial R] :
    Nonempty (R →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have : WeaklyEtale K (Localization.AtPrime m) := .trans K R _
  have := isAlgebraic_residueField (K := K) (R := Localization.AtPrime m)
  exact ⟨(IsAlgClosed.lift (M := K)
    (R := K) (S := IsLocalRing.ResidueField (Localization.AtPrime m))).comp
    ((IsScalarTower.toAlgHom K (Localization.AtPrime m) _).comp
      (IsScalarTower.toAlgHom K R _))⟩

end Algebra.WeaklyEtale
