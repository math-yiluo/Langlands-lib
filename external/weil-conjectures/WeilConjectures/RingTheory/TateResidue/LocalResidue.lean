/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.TateResidue.ResidueProperties

/-!
# The local residue

Let `k` be a field, `K` a commutative `k`-algebra (typically a function field) and `O ⊆ K` a
`k`-subalgebra (typically the local ring of a closed point of a curve) such that `f O ~ O` for
all `f ∈ K`. Tate's local residue is `res_O := res_{K, O} : Ω[K⁄k] → k`, `K` acting on itself.

## Main definitions

- `TateResidue.localRes O`: the local residue `res_{K,O}`.

## Main results

- `TateResidue.localRes_smul_D_eq_zero`: `res_O (f dg) = 0` for `f, g ∈ O`.
- `TateResidue.localRes_map_eq_zero`: `res_O` kills the image of `Ω[O⁄k]`.
- `TateResidue.admissible_of_exists`: a criterion for `f O ~ O`: every `f` has a denominator
  `g ∈ O` (a unit of `K`) with `O / g O` finite-dimensional.
- `TateResidue.localRes_mul_inv_smul_D` (R5): `res_O (u t⁻¹ dt) = Tr_{(O / t O)/k} (u)`.
-/

@[expose] public section

open LinearMap Submodule Module.End KaehlerDifferential

namespace TateResidue

variable {k K : Type*} [Field k] [CommRing K] [Algebra k K]

/-- **Tate's local residue** `res_O = res_{K,O} : Ω[K⁄k] → k` attached to a `k`-subalgebra
`O ⊆ K` (blueprint: `theorem-riemann-roch-coherent-serre-duality--2`). -/
noncomputable def localRes (O : Subalgebra k K) : Ω[K⁄k] →ₗ[k] k :=
  res K (Subalgebra.toSubmodule O)

/-- `res_O (f dg) = 0` if `f, g ∈ O` (R2). -/
theorem localRes_smul_D_eq_zero {O : Subalgebra k K} {f g : K} (hf : f ∈ O) (hg : g ∈ O) :
    localRes O (f • D k K g) = 0 :=
  res_smul_D_eq_zero (fun a ha ↦ by rw [smul_eq_mul]; exact O.mul_mem hf ha)
    (fun a ha ↦ by rw [smul_eq_mul]; exact O.mul_mem hg ha)

/-- `res_O` kills the image of `Ω[O⁄k]` in `Ω[K⁄k]`. -/
theorem localRes_map_eq_zero (O : Subalgebra k K) (ω : Ω[O⁄k]) :
    localRes O (KaehlerDifferential.map k k O K ω) = 0 := by
  have : localRes O ∘ₗ (KaehlerDifferential.map k k O K).restrictScalars k = 0 := by
    refine linearMap_ext_smul_D fun a b ↦ ?_
    rw [comp_apply, restrictScalars_apply, LinearMap.map_smul, map_D, ← algebraMap_smul K a,
      LinearMap.zero_apply]
    exact localRes_smul_D_eq_zero a.2 b.2
  exact congr($this ω)

/-- **Criterion for admissibility**: if every `f ∈ K` has a "denominator" `g ∈ O`, a unit of `K`
with `g f ∈ O` and `O / g O` finite-dimensional over `k`, then `f O ~ O` for all `f ∈ K`. -/
theorem admissible_of_exists (O : Subalgebra k K)
    (h : ∀ f : K, ∃ g : O, IsUnit (g : K) ∧ (g : K) * f ∈ O ∧
      Module.Finite k (O ⧸ Ideal.span {g})) :
    Admissible K (Subalgebra.toSubmodule O) := by
  intro f
  obtain ⟨g, hg, hgf, hfin⟩ := h f
  set I : Ideal O := Ideal.span {g}
  set q : O →ₗ[k] O ⧸ I := (Ideal.Quotient.mkₐ k I).toLinearMap
  have htop : ((⊤ : Submodule k O).map q).FG :=
    (Module.Finite.fg_top (R := k) (M := O ⧸ I)).of_le le_top
  obtain ⟨W₀, hW₀, hle⟩ := exists_fg_le_ker_sup q htop
  set ginv : K := ↑hg.unit⁻¹
  have hginv : ginv * g = 1 := by simp [ginv]
  refine ⟨W₀.map ((act k ginv) ∘ₗ O.val.toLinearMap), hW₀.map _, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  -- `f a = ginv * y` with `y = (g f) a ∈ O`
  have hy : (g : K) * f * a ∈ O := O.mul_mem hgf ha
  obtain ⟨i, hi, w, hw, hiw⟩ := mem_sup.1 (hle (show (⟨_, hy⟩ : O) ∈ ⊤ from trivial))
  have hi' : i ∈ I := by
    rw [mem_ker] at hi
    exact Ideal.Quotient.eq_zero_iff_mem.1 hi
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hi'
  have hfa : act k f a = (z : K) + ginv * (w : K) := by
    have h1 : (g : K) * f * a = (z : K) * g + w := by
      rw [← Subalgebra.coe_mul, ← Subalgebra.coe_add, hiw]
    have h2 : f * a = ginv * ((g : K) * f * a) := by
      rw [← mul_assoc, ← mul_assoc, hginv, one_mul]
    rw [act_apply, smul_eq_mul, h2, h1, mul_add, mul_comm (z : K), ← mul_assoc, hginv, one_mul]
  rw [hfa]
  exact add_mem_sup z.2 ⟨w, hw, rfl⟩

end TateResidue

namespace TateResidue

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **(R5) for the local residue**: for `u, t ∈ O` with `t ≠ 0` and `O / t O` finite-dimensional,
`res_O (u t⁻¹ dt) = Tr_{(O / t O)/k} (u)` (blueprint:
`theorem-riemann-roch-coherent-serre-duality--2`). -/
theorem localRes_mul_inv_smul_D {O : Subalgebra k K}
    (hO : Admissible K (Subalgebra.toSubmodule O)) (u t : O) (ht : (t : K) ≠ 0)
    [Module.Finite k (O ⧸ Ideal.span {t})] :
    localRes O (((u : K) * (t : K)⁻¹) • D k K t) =
      Algebra.trace k (O ⧸ Ideal.span {t}) (Ideal.Quotient.mk _ u) := by
  set A := Subalgebra.toSubmodule O
  set I : Ideal O := Ideal.span {t}
  have hg : IsUnit (t : K) := ht.isUnit
  have hinv : (↑hg.unit⁻¹ : K) = (t : K)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  have hgA : ∀ a ∈ A, (t : K) • a ∈ A := fun a ha ↦ by
    rw [smul_eq_mul]; exact O.mul_mem t.2 ha
  have huA : ∀ a ∈ A, (u : K) • a ∈ A := fun a ha ↦ by
    rw [smul_eq_mul]; exact O.mul_mem u.2 ha
  have hmap : (smulSub A (t : K)).map (O.toSubmoduleEquiv : A →ₗ[k] O) = I.restrictScalars k := by
    ext y
    simp only [mem_map, restrictScalars_mem, I, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨x, ⟨b, hb, hbx⟩, rfl⟩
      refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
      change b * t = (x : K)
      have hbx' : (t : K) * b = x := hbx
      rw [← hbx', mul_comm]
    · rintro ⟨b, rfl⟩
      refine ⟨⟨b * t, (b * t).2⟩, ⟨b, b.2, ?_⟩, rfl⟩
      change (t : K) • (b : K) = (b : K) * t
      rw [smul_eq_mul, mul_comm]
  let e : (A ⧸ smulSub A (t : K)) ≃ₗ[k] (O ⧸ I) :=
    (Submodule.Quotient.equiv _ _ O.toSubmoduleEquiv hmap).trans
      (Submodule.Quotient.restrictScalarsEquiv k I)
  have : FiniteDimensional k (A ⧸ smulSub A (t : K)) := Module.Finite.equiv e.symm
  rw [localRes, ← hinv, res_mul_inv_smul_D hO hg hgA huA, Algebra.trace_apply,
    ← LinearMap.trace_conj' _ e]
  congr 1
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

end TateResidue
