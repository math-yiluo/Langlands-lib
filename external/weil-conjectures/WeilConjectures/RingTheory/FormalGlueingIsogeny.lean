/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.TorsionModuleFlatBaseChangeIso
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.RingTheory.FormalGlueingMapToAlgebraization
import WeilConjectures.RingTheory.FormalGlueingMapFromAlgebraization

/-!
# Formal glueing of maps with ideal-power torsion kernel and cokernel

Source: Stacks Project, More on Algebra, Lemma 0ALK, with Lemmas 05EC and 05E9
(blueprint: lem-weil-pbc-formal-glueing-isogeny).

The tensor factors follow Mathlib's convention `S ⊗[R] M`. Ideal-power torsion
is expressed elementwise, and the comparison equivalences are specified on
kernel elements and on representatives of the cokernel.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

private theorem torsion_unit_equiv
    (hflat : (algebraMap R S).Flat) (I : Ideal R)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type*) [AddCommGroup M] [Module R M]
    (ht : ∀ x : M, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ e : M ≃ₗ[R] S ⊗[R] M, ∀ x, e x = (1 : S) ⊗ₜ[R] x := by
  let q := Ideal.quotientMap (I.map (algebraMap R S))
    (algebraMap R S) Ideal.le_comap_map
  have hpos : ∀ x : M, ∃ n : ℕ, 0 < n ∧ ∀ r : R, r ∈ I ^ n → r • x = 0 := by
    intro x
    obtain ⟨n, hn⟩ := ht x
    exact ⟨n + 1, Nat.zero_lt_succ n, fun r hr ↦
      hn r (Ideal.pow_le_pow_right (Nat.le_succ n) hr)⟩
  have hb := RingTheory.torsionModule_flat_baseChange_bijective
    (algebraMap R S) hflat I
    ⟨RingEquiv.ofBijective q hquot, fun r ↦ rfl⟩ hpos
  have hm : @Module.compHom S R S _ _ (Semiring.toModule (R := S)) _
      (algebraMap R S) = (inferInstance : Module R S) := by
    ext r s
    exact (Algebra.smul_def r s).symm
  rw [hm] at hb
  let j : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  have hj : Function.Bijective j := by
    have hb' : Function.Bijective (fun x : M ↦ (x ⊗ₜ[R] (1 : S) : M ⊗[R] S)) := by
      exact hb
    have hc := (TensorProduct.comm R M S).bijective.comp hb'
    convert hc using 1
    funext x
    simp [j]
  exact ⟨LinearEquiv.ofBijective j hj, fun x ↦ rfl⟩

private theorem torsion_map_comparisons
    (hflat : (algebraMap R S).Flat) (I : Ideal R)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (ψ : M →ₗ[R] N)
    (hker : ∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : N ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    (∃ k : ψ.ker ≃ₗ[R] ((ψ.baseChange S).restrictScalars R).ker,
      ∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val) ∧
    (∃ c : (N ⧸ ψ.range) ≃ₗ[R]
        ((S ⊗[R] N) ⧸ ((ψ.baseChange S).restrictScalars R).range),
      ∀ y : N, c (ψ.range.mkQ y) =
        ((ψ.baseChange S).restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) := by
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  obtain ⟨ek, hek⟩ := torsion_unit_equiv hflat I hquot ψ.ker hker
  obtain ⟨ec, hec⟩ := torsion_unit_equiv hflat I hquot (N ⧸ ψ.range) hcoker
  constructor
  · let k := ek.trans ((LinearMap.tensorKerEquiv S S ψ).restrictScalars R)
    refine ⟨k, ?_⟩
    intro x
    change ((LinearMap.tensorKerEquiv S S ψ) (ek x)).val = _
    rw [hek]
    rfl
  · have hr : (ψ.range.subtype.lTensor S).range =
        ((ψ.baseChange S).restrictScalars R).range := by
      exact (LinearMap.lTensor_range S (g := ψ)).symm
    let c := ec.trans ((TensorProduct.tensorQuotientEquiv S ψ.range).trans
      (Submodule.quotEquivOfEq _ _ hr))
    refine ⟨c, ?_⟩
    intro y
    change (Submodule.quotEquivOfEq _ _ hr)
      ((TensorProduct.tensorQuotientEquiv S ψ.range) (ec (ψ.range.mkQ y))) = _
    rw [hec]
    rfl

/-- Part (1) and the comparisons in part (3) of Stacks, Lemma 0ALK;
Lemmas 05EC and 05E9 (blueprint: lem-weil-pbc-formal-glueing-isogeny).

Localize at a finite set of generators of `I`: torsion kernels and cokernels
vanish, so the given map becomes an isomorphism (module localization and its
exactness, def-weil-pbc-module-localization-away and
lem-weil-pbc-localization-module-exact). Build the glueing datum using these
localized isomorphisms and the canonical comparison maps
(theorem-finite-etale-covers-proper-henselian--2). The formal glueing equivalence
(prop-weil-pbc-formal-glueing-equivalence) algebraizes the datum and its map;
comparison of components gives `ψ` and `β`. The localized `ψ` are isomorphisms.
Thus each element of its kernel and cokernel is killed by a power of every
generator. Choose positive exponents `eᵢ` killing that element and use degree
`1 + ∑ eᵢ`: every generating monomial has an exponent at least `eᵢ`, so
this power of `I` kills the element, including for the empty generating set.
Flatness identifies the base-changed
kernel with the kernel of the base-changed map (lem-weil-pbc-flat-tensor-exact);
right exactness gives the analogous cokernel identification
(lem-weil-pbc-tensor-right-exact). For ideal-power torsion modules the map
`x ↦ 1 ⊗ x` is an isomorphism (lem-weil-pbc-torsion-module-flat-base-change-iso).
These composites are the canonical comparison maps specified below.
Finally `β` transports their targets to the kernel and cokernel of `φ'`;
the last two clauses specify these transported comparisons.
-/
theorem exists_map_to_of_torsion_baseChange
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (P : Type (max u v w)) [AddCommGroup P] [Module R P]
    (Q : Type (max u v w)) [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q]
    (φ' : Q →ₗ[S] S ⊗[R] P)
    (hker : ∀ x : (φ'.restrictScalars R).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : _ ⧸ (φ'.restrictScalars R).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ T : ModuleCat.{max u v w} R,
      ∃ (ψ : T →ₗ[R] P) (β : Q ≃ₗ[S] S ⊗[R] T),
        (ψ.baseChange S).comp β.toLinearMap = φ' ∧
        (∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∀ x : P ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∃ k : ψ.ker ≃ₗ[R] ((ψ.baseChange S).restrictScalars R).ker,
          ∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ c : (P ⧸ ψ.range) ≃ₗ[R]
            ((S ⊗[R] P) ⧸ ((ψ.baseChange S).restrictScalars R).range),
          ∀ y : P, c (ψ.range.mkQ y) =
            ((ψ.baseChange S).restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) ∧
        (∃ e : ψ.ker ≃ₗ[R] (φ'.restrictScalars R).ker,
          ∀ x, β (e x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ e : (P ⧸ ψ.range) ≃ₗ[R] (_ ⧸ (φ'.restrictScalars R).range),
          ∀ y : P, e (ψ.range.mkQ y) =
            (φ'.restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) := by
  obtain ⟨T, ψ, β, hcomm, hkt, hct⟩ :=
    exists_map_to_algebraization hflat I hI hquot P Q φ' hker hcoker
  obtain ⟨⟨k, hk⟩, ⟨c, hc⟩⟩ := torsion_map_comparisons hflat I hquot ψ hkt hct
  have hcomp (x : Q) : (ψ.baseChange S) (β x) = φ' x :=
    LinearMap.congr_fun hcomm x
  let b : ((ψ.baseChange S).restrictScalars R).ker ≃ₗ[R]
      (φ'.restrictScalars R).ker :=
    { toFun := fun x ↦ ⟨β.symm x.val, by
        change φ' (β.symm x.val) = 0
        rw [← hcomp, β.apply_symm_apply]
        exact x.property⟩
      invFun := fun x ↦ ⟨β x.val, by
        change (ψ.baseChange S) (β x.val) = 0
        rw [hcomp]
        exact x.property⟩
      left_inv := fun x ↦ by ext; exact β.apply_symm_apply x.val
      right_inv := fun x ↦ by ext; exact β.symm_apply_apply x.val
      map_add' := fun x y ↦ by ext; exact β.symm.map_add x.val y.val
      map_smul' := fun r x ↦ by
        ext
        exact (β.symm.restrictScalars R).map_smul r x.val }
  have hr : ((ψ.baseChange S).restrictScalars R).range =
      (φ'.restrictScalars R).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨β.symm x, ?_⟩
      simpa only [β.apply_symm_apply, LinearMap.restrictScalars_apply]
        using (hcomp (β.symm x)).symm
    · rintro ⟨x, rfl⟩
      exact ⟨β x, hcomp x⟩
  refine ⟨T, ψ, β, hcomm, hkt, hct, ⟨k, hk⟩, ⟨c, hc⟩, ?_, ?_⟩
  · refine ⟨k.trans b, ?_⟩
    intro x
    change β (β.symm (k x).val) = _
    rw [β.apply_symm_apply, hk]
  · refine ⟨c.trans (Submodule.quotEquivOfEq _ _ hr), ?_⟩
    intro y
    change (Submodule.quotEquivOfEq _ _ hr) (c (ψ.range.mkQ y)) = _
    rw [hc]
    rfl

/-- Part (2) and the comparisons in part (3) of Stacks, Lemma 0ALK;
Lemmas 05EC and 05E9 (blueprint: lem-weil-pbc-formal-glueing-isogeny).

Localize at a finite set of generators of `I`: torsion kernels and cokernels
vanish, so the given map becomes an isomorphism (module localization and its
exactness, def-weil-pbc-module-localization-away and
lem-weil-pbc-localization-module-exact). Build the glueing datum using these
localized isomorphisms and the canonical comparison maps
(theorem-finite-etale-covers-proper-henselian--2). The formal glueing equivalence
(prop-weil-pbc-formal-glueing-equivalence) algebraizes the datum and its map;
comparison of components gives `ψ` and `β`. The localized `ψ` are isomorphisms.
Thus each element of its kernel and cokernel is killed by a power of every
generator. Choose positive exponents `eᵢ` killing that element and use degree
`1 + ∑ eᵢ`: every generating monomial has an exponent at least `eᵢ`, so
this power of `I` kills the element, including for the empty generating set.
Flatness identifies the base-changed
kernel with the kernel of the base-changed map (lem-weil-pbc-flat-tensor-exact);
right exactness gives the analogous cokernel identification
(lem-weil-pbc-tensor-right-exact). For ideal-power torsion modules the map
`x ↦ 1 ⊗ x` is an isomorphism (lem-weil-pbc-torsion-module-flat-base-change-iso).
These composites are the canonical comparison maps specified below.
Finally `β` transports their targets to the kernel and cokernel of `φ'`;
the last two clauses specify these transported comparisons.
For part (2), use the inverses of the localized maps in the glueing datum.
-/
theorem exists_map_from_of_torsion_baseChange
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (P : Type (max u v w)) [AddCommGroup P] [Module R P]
    (Q : Type (max u v w)) [AddCommGroup Q] [Module S Q] [Module R Q]
    [IsScalarTower R S Q]
    (φ' : S ⊗[R] P →ₗ[S] Q)
    (hker : ∀ x : (φ'.restrictScalars R).ker,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0)
    (hcoker : ∀ x : _ ⧸ (φ'.restrictScalars R).range,
      ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) :
    ∃ T : ModuleCat.{max u v w} R,
      ∃ (ψ : P →ₗ[R] T) (β : S ⊗[R] T ≃ₗ[S] Q),
        β.toLinearMap.comp (ψ.baseChange S) = φ' ∧
        (∀ x : ψ.ker, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∀ x : T ⧸ ψ.range, ∃ n : ℕ, ∀ r ∈ I ^ n, r • x = 0) ∧
        (∃ k : ψ.ker ≃ₗ[R] ((ψ.baseChange S).restrictScalars R).ker,
          ∀ x, (k x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ c : (T ⧸ ψ.range) ≃ₗ[R]
            ((S ⊗[R] T) ⧸ ((ψ.baseChange S).restrictScalars R).range),
          ∀ y : T, c (ψ.range.mkQ y) =
            ((ψ.baseChange S).restrictScalars R).range.mkQ ((1 : S) ⊗ₜ[R] y)) ∧
        (∃ e : ψ.ker ≃ₗ[R] (φ'.restrictScalars R).ker,
          ∀ x, (e x).val = (1 : S) ⊗ₜ[R] x.val) ∧
        (∃ e : (T ⧸ ψ.range) ≃ₗ[R] (_ ⧸ (φ'.restrictScalars R).range),
          ∀ y : T, e (ψ.range.mkQ y) =
            (φ'.restrictScalars R).range.mkQ (β ((1 : S) ⊗ₜ[R] y))) := by
  obtain ⟨T, ψ, β, hcomm, hkt, hct⟩ :=
    exists_map_from_algebraization hflat I hI hquot P Q φ' hker hcoker
  obtain ⟨⟨k, hk⟩, ⟨c, hc⟩⟩ := torsion_map_comparisons hflat I hquot ψ hkt hct
  have hcomp (x : S ⊗[R] P) : β ((ψ.baseChange S) x) = φ' x :=
    LinearMap.congr_fun hcomm x
  let b : ((ψ.baseChange S).restrictScalars R).ker ≃ₗ[R]
      (φ'.restrictScalars R).ker :=
    { toFun := fun x ↦ ⟨x.val, by
        change φ' x.val = 0
        rw [← hcomp, show (ψ.baseChange S) x.val = 0 from x.property, map_zero]⟩
      invFun := fun x ↦ ⟨x.val, by
        change (ψ.baseChange S) x.val = 0
        apply β.injective
        rw [hcomp, show φ' x.val = 0 from x.property, map_zero]⟩
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ rfl
      map_add' := fun x y ↦ rfl
      map_smul' := fun r x ↦ rfl }
  have hr : ((ψ.baseChange S).restrictScalars R).range.map
        (β.restrictScalars R).toLinearMap = (φ'.restrictScalars R).range := by
    rw [← LinearMap.range_comp]
    change ((β.toLinearMap.comp (ψ.baseChange S)).restrictScalars R).range = _
    rw [hcomm]
  refine ⟨T, ψ, β, hcomm, hkt, hct, ⟨k, hk⟩, ⟨c, hc⟩, ?_, ?_⟩
  · exact ⟨k.trans b, hk⟩
  · refine ⟨c.trans (Submodule.Quotient.equiv _ _ (β.restrictScalars R) hr), ?_⟩
    intro y
    change (Submodule.Quotient.equiv _ _ (β.restrictScalars R) hr)
      (c (ψ.range.mkQ y)) = _
    rw [hc]
    rfl


end FormalGlueing
