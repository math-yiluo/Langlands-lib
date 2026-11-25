/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.RingTheory.Kaehler.JacobiZariski
import WeilConjectures.RingTheory.FiniteKernelScalarExtension

/-!
# Finite-rank correction of a square-zero-valued field derivation

Source: Stacks Project, Tag 07FG, differential-basis and Jacobi--Zariski paragraphs.
(blueprint: lem-weil-pbc-finite-rank-defect-derivation)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

set_option linter.unusedVariables false in
/-- A derivation of `k` into an ideal annihilated by the residue kernel extends to `K`
up to an error contained in the `k`-span of finitely many elements of the ideal.
No coefficient subfield or generated subring is involved in this assertion.

Source: Stacks Project, Tag 07FG, from the choice of the differential basis to the
finite family of values of the corrected derivation.
(blueprint: lem-weil-pbc-finite-rank-defect-derivation)

Proof:
1. Use the section to act on `I` by `K`. Since `(ker r) * I = 0`, multiplication
   by any lift of a residue scalar gives the same action. Compatibility of `r`
   with `k` identifies its restricted action with the given `k`-action. Package
   `theta` as an integer-linear derivation into `I` using its product rule.
2. Work with differentials over `ℤ`. Middle Jacobi--Zariski exactness identifies
   the kernel of `K ⊗[k] Omega(k/ℤ) → Omega(K/ℤ)` with the image of
   `H1Cotangent k K`, so this kernel is finite dimensional over `K`.
3. Apply `LinearMap.exists_extension_finite_error` to the map representing
   `theta` on `Omega(k/ℤ)`. The helper chooses an arbitrary basis, bounds the
   kernel's support by a finite set, and extends the prescribed values on the
   independent complementary images. Compose the resulting `K`-linear map
   with the universal derivation of `K` to obtain `D` with values in `I`.
   Naturality and the universal lifting identity identify its finite error with
   `theta - D|k`. Map the finite family and its `k`-span through the `k`-linear
   inclusion of `I` into `Λ`. The zero ideal is allowed. -/
theorem exists_finite_rank_defect_derivation
    (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K]
    (Λ : Type v) [CommRing Λ] [Algebra k Λ]
    (r : Λ →+* K) (hcomm : r.comp (algebraMap k Λ) = algebraMap k K)
    (I : Ideal Λ) (hI : I ≤ RingHom.ker r) (hkill : RingHom.ker r * I = ⊥)
    (σ0 : K →+* Λ) (hσ0 : r.comp σ0 = RingHom.id K)
    (theta : k →+ Λ) (htheta : ∀ a : k, theta a ∈ I)
    (htheta_one : theta 1 = 0)
    (htheta_mul : ∀ a b : k,
      theta (a * b) = algebraMap k Λ a * theta b + algebraMap k Λ b * theta a)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (hH : Module.Finite K (H1Cotangent k K)) :
    ∃ (D : K →+ Λ) (f : Finset Λ),
      D 1 = 0 ∧
      (∀ x y : K, D (x * y) = σ0 x * D y + σ0 y * D x) ∧
      (∀ x : K, D x ∈ I) ∧
      (f : Set Λ) ⊆ I ∧
      (∀ a : k, theta a - D (algebraMap k K a) ∈
        Submodule.span k (f : Set Λ)) := by
  classical
  have hzero {x y : Λ} (hx : x ∈ RingHom.ker r) (hy : y ∈ I) : x * y = 0 := by
    have hm := Ideal.mul_mem_mul hx hy
    rw [hkill] at hm
    exact hm
  have hrσ (x : K) : r (σ0 x) = x := RingHom.congr_fun hσ0 x
  have hact (a : k) (y : I) :
      σ0 (algebraMap k K a) * (y : Λ) = algebraMap k Λ a * (y : Λ) := by
    have hx : σ0 (algebraMap k K a) - algebraMap k Λ a ∈ RingHom.ker r := by
      rw [RingHom.mem_ker, map_sub, hrσ]
      simpa only [RingHom.comp_apply, sub_self] using
        congrArg (fun z ↦ algebraMap k K a - z) (RingHom.congr_fun hcomm a)
    have hz := hzero hx y.property
    linear_combination hz
  let : Module K I := Module.compHom I σ0
  have hact' (a : k) (y : I) : (algebraMap k K a) • y = a • y := by
    apply Subtype.ext
    change σ0 (algebraMap k K a) • (y : Λ) = a • (y : Λ)
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self,
      RingHom.id_apply] using hact a y
  let : IsScalarTower k K I :=
    { smul_assoc := fun a b y ↦ by
        rw [Algebra.smul_def, mul_smul, hact'] }
  let θ : k →+ I :=
    { toFun := fun a ↦ ⟨theta a, htheta a⟩
      map_zero' := by ext; exact theta.map_zero
      map_add' := by intros; ext; exact theta.map_add _ _ }
  let δ : Derivation ℤ k I :=
    { toLinearMap := θ.toIntLinearMap
      map_one_eq_zero' := by ext; exact htheta_one
      leibniz' := fun a b ↦ by
        apply Subtype.ext
        change theta (a * b) = a • theta b + b • theta a
        simpa only [Algebra.smul_def] using htheta_mul a b }
  let phi := KaehlerDifferential.mapBaseChange ℤ k K
  have : Module.Finite K (H1Cotangent k K) := hH
  have hphi : Module.Finite K phi.ker := by
    have he : (H1Cotangent.δ ℤ k K).range = phi.ker :=
      (LinearMap.exact_iff.mp (H1Cotangent.exact_δ_mapBaseChange ℤ k K)).symm
    rw [← he]
    infer_instance
  obtain ⟨g, f, herr⟩ := LinearMap.exists_extension_finite_error
    k K (KaehlerDifferential ℤ k) (KaehlerDifferential ℤ K) I phi hphi
    δ.liftKaehlerDifferential
  let d : Derivation ℤ K I := g.compDer (KaehlerDifferential.D ℤ K)
  let D : K →+ Λ := I.subtype.toAddMonoidHom.comp d.toAddMonoidHom
  refine ⟨D, f.image Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
  · change (d 1 : Λ) = 0
    exact congrArg Subtype.val d.map_one_eq_zero
  · intro x y
    change (d (x * y) : Λ) = _
    have hd := congrArg Subtype.val (d.leibniz x y)
    change (d (x * y) : Λ) = σ0 x * (d y : Λ) + σ0 y * (d x : Λ) at hd
    exact hd
  · intro x
    exact (d x).property
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro a
    have he := herr (KaehlerDifferential.D ℤ k a)
    have hmap : phi (TensorProduct.tmul k (1 : K) (KaehlerDifferential.D ℤ k a)) =
        KaehlerDifferential.D ℤ K (algebraMap k K a) := by
      simp [phi, KaehlerDifferential.map_D]
    rw [Derivation.liftKaehlerDifferential_comp_D, hmap] at he
    change (↑(δ a - d (algebraMap k K a)) : Λ) ∈ _
    change δ a - d (algebraMap k K a) ∈ Submodule.span k (f : Set I) at he
    have hm := Submodule.mem_map_of_mem (f := I.subtype.restrictScalars k) he
    simpa only [Submodule.map_span, Set.image, Finset.coe_image,
      LinearMap.restrictScalars_apply, Submodule.subtype_apply] using hm


end Algebra
