/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.LocallyConstant.Algebra
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# Integral `ℓ`-adic functions as limits of their finite levels

This file proves the section-level content of `lemma-comparison-completed-coefficients--1`
for `E = ℚ_ℓ`: on any topological space `T` (in particular on the underlying space of an object
of the pro-étale site), the continuous functions `T → ℤ_ℓ` are the compatible families of
locally constant functions `T → ℤ/ℓⁿ`, as rings. The sections of the constant pro-étale sheaf
`(ℤ/ℓⁿ)_X` over `U` are the locally constant functions `|U| → ℤ/ℓⁿ`, so this identifies the
sections of `ℤ_ℓ,X` with those of `lim_n (ℤ/ℓⁿ)_X`.

It also provides the inclusion `C(T, ℤ_ℓ) → ℚ̄_ℓ,T` of integral functions into the locally
finite functions `PadicAlgCl.locallyFiniteFunctions`, the sections of
`AlgebraicGeometry.ProEtale.adicConstantSheaf`: this is the map along which an integral lattice
`lim_n F_n` of a lisse sheaf is to be rationalised.

## Main definitions

- `PadicInt.compatibleFamilies`: the compatible families in `∏ₙ ℤ/pⁿ`.
- `PadicInt.ringEquivCompatibleFamilies`: `ℤ_p ≃+* lim_n ℤ/pⁿ`.
- `PadicInt.compatibleLocallyConstant`: compatible families of locally constant functions
  `T → ℤ/pⁿ`.
- `PadicInt.continuousMapRingEquivCompatibleLocallyConstant`:
  `C(T, ℤ_p) ≃+* lim_n LocallyConstant(T, ℤ/pⁿ)`.
- `PadicAlgCl.integralToLocallyFiniteFunctions`: `C(T, ℤ_ℓ) →+* ℚ̄_ℓ,T`.
-/

@[expose] public section

open Topology

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- Two `p`-adic integers with the same reduction modulo `pⁿ` are at distance at most `p⁻ⁿ`. -/
lemma norm_sub_le_of_toZModPow_eq {n : ℕ} {x y : ℤ_[p]} (h : toZModPow n x = toZModPow n y) :
    ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]

/-- Two `p`-adic integers at distance less than `p⁻ⁿ` have the same reduction modulo `pⁿ`. -/
lemma toZModPow_eq_of_norm_sub_lt {n : ℕ} {x y : ℤ_[p]} (h : ‖x - y‖ < (p : ℝ) ^ (-(n : ℤ))) :
    toZModPow n x = toZModPow n y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow,
    ← norm_le_pow_iff_mem_span_pow]
  exact h.le

/-- The reduction `ℤ_p → ℤ/pⁿ` is locally constant: it is constant on balls of radius `p⁻ⁿ`. -/
lemma isLocallyConstant_toZModPow (n : ℕ) :
    IsLocallyConstant (toZModPow n : ℤ_[p] → ZMod (p ^ n)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ ?_
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  filter_upwards [Metric.ball_mem_nhds x (zpow_pos hp0 (-(n : ℤ)))] with y hy
  exact toZModPow_eq_of_norm_sub_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hy)

variable (p) in
/-- The compatible families `(aₙ)` in `∏ₙ ℤ/pⁿ`: `aₙ` reduces to `aₘ` for `m ≤ n`. This is the
inverse limit `lim_n ℤ/pⁿ`. -/
def compatibleFamilies : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := {a | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow p h) _ (a n) = a m}
  zero_mem' _ _ _ := map_zero _
  one_mem' _ _ _ := map_one _
  add_mem' ha hb m n h := by
    simp only [Pi.add_apply, map_add, ha m n h, hb m n h]
  mul_mem' ha hb m n h := by
    simp only [Pi.mul_apply, map_mul, ha m n h, hb m n h]
  neg_mem' ha m n h := by
    simp only [Pi.neg_apply, map_neg, ha m n h]

/-- The `n`-th component of a compatible family, as a ring homomorphism. -/
noncomputable def compatibleFamiliesEval (n : ℕ) : compatibleFamilies p →+* ZMod (p ^ n) :=
  (Pi.evalRingHom _ n).comp (compatibleFamilies p).subtype

/-- The reductions of a `p`-adic integer form a compatible family. -/
noncomputable def toCompatibleFamilies : ℤ_[p] →+* compatibleFamilies p :=
  (RingHom.pi fun n ↦ toZModPow n).codRestrict _ fun x m n h ↦
    RingHom.congr_fun (zmod_cast_comp_toZModPow m n h) x

omit hp in
/-- The components of compatible families are compatible ring homomorphisms. -/
lemma compatibleFamiliesEval_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (compatibleFamiliesEval n) =
      compatibleFamiliesEval m :=
  RingHom.ext fun a ↦ a.2 m n h

/-- **`ℤ_p = lim_n ℤ/pⁿ`** as rings: a `p`-adic integer is determined by its reductions, and
every compatible family of residues is the family of reductions of a `p`-adic integer
(`PadicInt.lift`). -/
noncomputable def ringEquivCompatibleFamilies : ℤ_[p] ≃+* compatibleFamilies p where
  __ := toCompatibleFamilies
  invFun := lift compatibleFamiliesEval_compat
  left_inv _ := ext_of_toZModPow.1 fun n ↦
    RingHom.congr_fun (lift_spec compatibleFamiliesEval_compat n) _
  right_inv a := Subtype.ext <| funext fun n ↦
    RingHom.congr_fun (lift_spec compatibleFamiliesEval_compat n) a

@[simp]
lemma ringEquivCompatibleFamilies_apply_coe (x : ℤ_[p]) (n : ℕ) :
    (ringEquivCompatibleFamilies x : ∀ n : ℕ, ZMod (p ^ n)) n = toZModPow n x :=
  rfl

@[simp]
lemma toZModPow_ringEquivCompatibleFamilies_symm (a : compatibleFamilies p) (n : ℕ) :
    toZModPow n (ringEquivCompatibleFamilies.symm a) = (a : ∀ n : ℕ, ZMod (p ^ n)) n := by
  rw [← ringEquivCompatibleFamilies_apply_coe, RingEquiv.apply_symm_apply]

variable (p) (T : Type*) [TopologicalSpace T]

/-- The compatible families of locally constant functions `aₙ : T → ℤ/pⁿ`: `aₙ` reduces to
`aₘ` for `m ≤ n`. This is the inverse limit `lim_n LocallyConstant(T, ℤ/pⁿ)`, i.e. the sections
over `T` of `lim_n (ℤ/pⁿ)_T`. -/
def compatibleLocallyConstant : Subring (∀ n : ℕ, LocallyConstant T (ZMod (p ^ n))) where
  carrier := {a | ∀ m n (h : m ≤ n) t, ZMod.castHom (pow_dvd_pow p h) _ (a n t) = a m t}
  zero_mem' _ _ _ _ := map_zero _
  one_mem' _ _ _ _ := map_one _
  add_mem' ha hb m n h t := by
    simp only [Pi.add_apply, LocallyConstant.coe_add, map_add, ha m n h t, hb m n h t]
  mul_mem' ha hb m n h t := by
    simp only [Pi.mul_apply, LocallyConstant.coe_mul, map_mul, ha m n h t, hb m n h t]
  neg_mem' ha m n h t := by
    simp only [Pi.neg_apply, LocallyConstant.coe_neg, map_neg, ha m n h t]

variable {p T}

/-- The value at `t` of a compatible family of locally constant functions, a compatible family
of residues. -/
def compatibleLocallyConstantEval (t : T) :
    compatibleLocallyConstant p T →+* compatibleFamilies p where
  toFun a := ⟨fun n ↦ (a : ∀ n : ℕ, LocallyConstant T (ZMod (p ^ n))) n t,
    fun m n h ↦ a.2 m n h t⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit hp in
@[simp]
lemma compatibleLocallyConstantEval_apply_coe (t : T) (a : compatibleLocallyConstant p T)
    (n : ℕ) :
    (compatibleLocallyConstantEval t a : ∀ n : ℕ, ZMod (p ^ n)) n =
      (a : ∀ n : ℕ, LocallyConstant T (ZMod (p ^ n))) n t :=
  rfl

/-- The `p`-adic integer with reductions a compatible family of locally constant functions
depends continuously on the point: near `t` it agrees with its value at `t` modulo `pⁿ`. -/
lemma continuous_ringEquivCompatibleFamilies_symm_eval (a : compatibleLocallyConstant p T) :
    Continuous fun t ↦ ringEquivCompatibleFamilies.symm (compatibleLocallyConstantEval t a) := by
  refine continuous_iff_continuousAt.2 fun t ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  filter_upwards [((a : ∀ n : ℕ, LocallyConstant T (ZMod (p ^ n))) n).isLocallyConstant
    |>.eventually_eq t] with s hs
  rw [dist_eq_norm]
  refine (norm_sub_le_of_toZModPow_eq (n := n) ?_).trans_lt ?_
  · simpa using hs
  · rwa [zpow_neg, zpow_natCast, ← inv_pow]

/-- The reduction modulo `pⁿ` of a continuous function `T → ℤ_p`, a locally constant function
`T → ℤ/pⁿ`. -/
noncomputable def continuousMapReduction (n : ℕ) :
    C(T, ℤ_[p]) →+* LocallyConstant T (ZMod (p ^ n)) where
  toFun f := ⟨toZModPow n ∘ f, (isLocallyConstant_toZModPow n).comp_continuous f.continuous⟩
  map_zero' := LocallyConstant.ext fun _ ↦ map_zero (toZModPow n)
  map_one' := LocallyConstant.ext fun _ ↦ map_one (toZModPow n)
  map_add' f g := LocallyConstant.ext fun t ↦ map_add (toZModPow n) (f t) (g t)
  map_mul' f g := LocallyConstant.ext fun t ↦ map_mul (toZModPow n) (f t) (g t)

@[simp]
lemma continuousMapReduction_apply (n : ℕ) (f : C(T, ℤ_[p])) (t : T) :
    continuousMapReduction n f t = toZModPow n (f t) :=
  rfl

/-- A continuous function `T → ℤ_p` gives the compatible family of its reductions, locally
constant functions `T → ℤ/pⁿ`. -/
noncomputable def continuousMapToCompatibleLocallyConstant :
    C(T, ℤ_[p]) →+* compatibleLocallyConstant p T :=
  (RingHom.pi continuousMapReduction).codRestrict _ fun f m n h t ↦
    RingHom.congr_fun (zmod_cast_comp_toZModPow m n h) (f t)

/-- The continuous function `T → ℤ_p` with reductions a compatible family of locally constant
functions. -/
noncomputable def compatibleLocallyConstantToContinuousMap :
    compatibleLocallyConstant p T →+* C(T, ℤ_[p]) where
  toFun a := ⟨_, continuous_ringEquivCompatibleFamilies_symm_eval a⟩
  map_zero' := ContinuousMap.ext fun t ↦ by simp
  map_one' := ContinuousMap.ext fun t ↦ by simp
  map_add' a b := ContinuousMap.ext fun t ↦ by simp
  map_mul' a b := ContinuousMap.ext fun t ↦ by simp

/-- **`C(T, ℤ_p) = lim_n LocallyConstant(T, ℤ/pⁿ)`** as rings: the section-level form of
`ℤ_p,X ≅ lim_n (ℤ/pⁿ)_X` (`lemma-comparison-completed-coefficients--1`, for `E = ℚ_p`). -/
noncomputable def continuousMapRingEquivCompatibleLocallyConstant :
    C(T, ℤ_[p]) ≃+* compatibleLocallyConstant p T :=
  RingEquiv.ofRingHom continuousMapToCompatibleLocallyConstant
    compatibleLocallyConstantToContinuousMap
    (RingHom.ext fun a ↦ Subtype.ext <| funext fun n ↦ LocallyConstant.ext fun t ↦ by
      simp [continuousMapToCompatibleLocallyConstant, compatibleLocallyConstantToContinuousMap])
    (RingHom.ext fun f ↦ ContinuousMap.ext fun t ↦ ext_of_toZModPow.1 fun n ↦ by
      simp [continuousMapToCompatibleLocallyConstant, compatibleLocallyConstantToContinuousMap])

end PadicInt

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (T : Type*) [TopologicalSpace T]

/-- The function `T → ℚ̄_ℓ` underlying an integral function `T → ℤ_ℓ`. -/
noncomputable def integralCoe (f : C(T, ℤ_[l])) : C(T, PadicAlgCl l) :=
  ⟨fun t ↦ algebraMap ℚ_[l] (PadicAlgCl l) (f t),
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp f.continuous)⟩

/-- An integral function `T → ℤ_ℓ` is a locally finite function `T → ℚ̄_ℓ`: its values lie in
the line `ℚ_ℓ`. -/
lemma integralCoe_mem_locallyFiniteFunctions (f : C(T, ℤ_[l])) :
    integralCoe l T f ∈ locallyFiniteFunctions l T := by
  intro x
  refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[l] {1}) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨y, -, rfl⟩
  refine Submodule.mem_span_singleton.2 ⟨(f y : ℚ_[l]), ?_⟩
  simp [integralCoe, Algebra.smul_def]

/-- The inclusion `C(T, ℤ_ℓ) → ℚ̄_ℓ,T` of integral functions into the locally finite functions,
the sections of the constant `ℓ`-adic sheaf: the map `ℤ_ℓ,X → ℚ̄_ℓ,X` along which integral
lattices are rationalised. -/
noncomputable def integralToLocallyFiniteFunctions :
    C(T, ℤ_[l]) →+* locallyFiniteFunctions l T where
  toFun f := ⟨_, integralCoe_mem_locallyFiniteFunctions l T f⟩
  map_zero' := Subtype.ext <| ContinuousMap.ext fun _ ↦ by simp [integralCoe]
  map_one' := Subtype.ext <| ContinuousMap.ext fun _ ↦ by simp [integralCoe]
  map_add' _ _ := Subtype.ext <| ContinuousMap.ext fun _ ↦ by simp [integralCoe]
  map_mul' _ _ := Subtype.ext <| ContinuousMap.ext fun _ ↦ by simp [integralCoe]

/-- The inclusion of integral functions into the locally finite functions is injective. -/
lemma integralToLocallyFiniteFunctions_injective :
    Function.Injective (integralToLocallyFiniteFunctions l T) := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  have := congrArg (fun φ : locallyFiniteFunctions l T ↦ (φ : C(T, PadicAlgCl l)) t) h
  exact PadicInt.ext (by simpa [integralToLocallyFiniteFunctions, integralCoe] using this)

/-- The norm of `ℓ` in `ℚ̄_ℓ` is `ℓ⁻¹`. -/
lemma norm_natCast_self : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact (norm_extends l _).trans Padic.norm_p

variable {l T}

/-- **Continuous functions on a compact space are integral up to a power of `ℓ`**: for a
continuous `f : T → ℚ̄_ℓ` on a compact `T`, some `ℓᵐ f` takes values in the closed unit ball
(the point-level content of `lemma-comparison-completed-coefficients--2`). -/
lemma exists_norm_pow_mul_le_one [CompactSpace T] (f : C(T, PadicAlgCl l)) :
    ∃ m : ℕ, ∀ t, ‖(l : PadicAlgCl l) ^ m * f t‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hC1 : 0 < (max C 1)⁻¹ := inv_pos.2 (lt_max_of_lt_right one_pos)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hC1 (inv_lt_one_of_one_lt₀ hl1)
  refine ⟨m, fun t ↦ ?_⟩
  rw [norm_mul, norm_pow, norm_natCast_self]
  calc (l : ℝ)⁻¹ ^ m * ‖f t‖ ≤ (max C 1)⁻¹ * max C 1 :=
        mul_le_mul hm.le ((hC t (Set.mem_univ t)).trans (le_max_left C 1)) (norm_nonneg _)
          hC1.le
    _ = 1 := inv_mul_cancel₀ (lt_max_of_lt_right one_pos).ne'

/-- **`C(T, ℚ_ℓ) = C(T, ℤ_ℓ)[1/ℓ]` on a compact space**: every continuous `f : T → ℚ_ℓ` on a
compact `T` is `ℓ⁻ᵐ g` for a continuous `g : T → ℤ_ℓ` (`lemma-comparison-completed-coefficients--2`
on a profinite set, for `E = ℚ_ℓ`). -/
lemma exists_padicInt_eq_pow_mul [CompactSpace T] (f : C(T, ℚ_[l])) :
    ∃ (m : ℕ) (g : C(T, ℤ_[l])), ∀ t, ((g t : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ m * f t := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hC1 : 0 < (max C 1)⁻¹ := inv_pos.2 (lt_max_of_lt_right one_pos)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hC1 (inv_lt_one_of_one_lt₀ hl1)
  have hle (t : T) : ‖(l : ℚ_[l]) ^ m * f t‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p]
    calc (l : ℝ)⁻¹ ^ m * ‖f t‖ ≤ (max C 1)⁻¹ * max C 1 :=
          mul_le_mul hm.le ((hC t (Set.mem_univ t)).trans (le_max_left C 1)) (norm_nonneg _)
            hC1.le
      _ = 1 := inv_mul_cancel₀ (lt_max_of_lt_right one_pos).ne'
  exact ⟨m, ⟨fun t ↦ ⟨_, hle t⟩, Continuous.subtype_mk
    ((continuous_const.mul f.continuous)) _⟩, fun _ ↦ rfl⟩

end PadicAlgCl
