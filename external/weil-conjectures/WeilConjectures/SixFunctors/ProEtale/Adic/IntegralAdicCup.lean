/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheafPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicCup

/-!
# The cup product on `Hⁿ(S_proét, ℤ_ℓ)`

Let `S` be a quasi-compact quasi-separated scheme whose cohomology groups `Hᵏ(S, ℤ/ℓᵐ)` are finite.
The integral cohomology `Hⁿ(S, ℤ_ℓ) = Hⁿ(S_proét, C(-, ℤ_ℓ))` is the inverse limit of the
`Hⁿ(S, ℤ/ℓᵐ)` (the pro-étale topos is replete and `lim¹` of finite groups vanishes), and the cup
products of the finite levels (`AlgebraicGeometry.ProEtale.finiteAdicHCup`) are compatible with the
reductions of the coefficients. Hence there is a unique bilinear cup product
`⌣ : Hⁱ(S, ℤ_ℓ) × Hʲ(S, ℤ_ℓ) ⟶ Hⁱ⁺ʲ(S, ℤ_ℓ)` (`AlgebraicGeometry.ProEtale.integralAdicHCup`) whose
reductions are the finite-level cup products
(`AlgebraicGeometry.ProEtale.reduction_integralAdicHCup`). It is graded commutative and compatible
with the pullback along an automorphism of a connected `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (S : Scheme.{u})

/-- The reductions of the coefficients are compatible: `ℤ_ℓ ⟶ ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` is `ℤ_ℓ ⟶ ℤ/ℓᵐ`. -/
lemma finiteAdicHTransition_reduction (m n : ℕ) (x : IntegralAdicH S l n) :
    finiteAdicHTransition l m S n (reduction S l (m + 1) n x) = reduction S l m n x :=
  (Sheaf.H.map_comp_apply _ _ x).symm.trans
    (congrArg (fun f ↦ Sheaf.H.map f n x) (continuousSheafMap_comp S _ _).symm)

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The family of finite-level cup products of the reductions of two integral classes lifts to an
integral class. -/
lemma exists_reduction_eq_finiteAdicHCup {i j k : ℕ} (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) :
    ∃ z : IntegralAdicH S l k, ∀ m, reduction S l m k z =
      finiteAdicHCup l m S h (reduction S l m i x) (reduction S l m j y) := by
  have hU := powOpenAddSubgroup_succ_le l
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := S)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((continuousSheafTower S (powOpenAddSubgroup l) hU).map (homOfLE k.le_succ).op) := by
    rw [continuousSheafTower_map_succ]
    exact (shortExact_continuousSheafShortComplex S (powOpenAddSubgroup l) hU k).epi_g
  obtain ⟨z, hz⟩ := Ext.exists_comp_eq_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht)
    (isLimitContinuousSheafCone S (powOpenAddSubgroup l) hU
      (eq_zero_of_forall_mem_powOpenAddSubgroup l)) (q := k)
    (fun m ↦ finiteAdicHCup l m S h (reduction S l m i x) (reduction S l m j y)) (fun m ↦ by
      rw [continuousSheafTower_map_succ]
      change finiteAdicHTransition l m S k _ = _
      rw [finiteAdicHTransition_finiteAdicHCup, finiteAdicHTransition_reduction,
        finiteAdicHTransition_reduction])
  exact ⟨z, hz⟩

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- Classes of `Hⁿ(S, ℤ_ℓ)` with the same reductions are equal, if the `Hᵏ(S, ℤ/ℓᵐ)` are
finite. -/
lemma eq_of_forall_reduction_eq (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) {n : ℕ}
    {a b : IntegralAdicH S l n} (hab : ∀ m, reduction S l m n a = reduction S l m n b) :
    a = b :=
  sub_eq_zero.1 (eq_zero_of_forall_reduction_eq_zero S l n (fun m k _ ↦ hfin m k) _
    fun m ↦ by rw [map_sub, hab, sub_self])

/-- The **cup product** `Hⁱ(S, ℤ_ℓ) × Hʲ(S, ℤ_ℓ) ⟶ Hᵏ(S, ℤ_ℓ)`, `i + j = k`, for `S` with finite
cohomology groups `Hᵏ(S, ℤ/ℓᵐ)`: the unique class whose reductions modulo every `ℓᵐ` are the cup
products of the reductions (`AlgebraicGeometry.ProEtale.reduction_integralAdicHCup`). -/
noncomputable def integralAdicHCup (hfin : ∀ m k, Finite (FiniteAdicH S l m k)) {i j k : ℕ}
    (h : i + j = k) :
    IntegralAdicH S l i →ₗ[ℤ_[l]] IntegralAdicH S l j →ₗ[ℤ_[l]] IntegralAdicH S l k :=
  have hc (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) (m : ℕ) :=
    (exists_reduction_eq_finiteAdicHCup l S h x y).choose_spec m
  LinearMap.mk₂ ℤ_[l] (fun x y ↦ (exists_reduction_eq_finiteAdicHCup l S h x y).choose)
    (fun x x' y ↦ eq_of_forall_reduction_eq l S hfin fun m ↦ by
      rw [hc, map_add (reduction S l m k), hc, hc, map_add (reduction S l m i), map_add,
        AddMonoidHom.add_apply])
    (fun c x y ↦ eq_of_forall_reduction_eq l S hfin fun m ↦ by
      rw [hc, LinearMap.map_smul (reduction S l m k), hc, LinearMap.map_smul (reduction S l m i),
        finiteAdicHCup_smul_left])
    (fun x y y' ↦ eq_of_forall_reduction_eq l S hfin fun m ↦ by
      rw [hc, map_add (reduction S l m k), hc, hc, map_add (reduction S l m j), map_add])
    (fun c x y ↦ eq_of_forall_reduction_eq l S hfin fun m ↦ by
      rw [hc, LinearMap.map_smul (reduction S l m k), hc, LinearMap.map_smul (reduction S l m j),
        finiteAdicHCup_smul_right])

variable (hfin : ∀ m k, Finite (FiniteAdicH S l m k))

/-- The reductions of the cup product are the cup products of the reductions. -/
theorem reduction_integralAdicHCup {i j k : ℕ} (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) (m : ℕ) :
    reduction S l m k (integralAdicHCup l S hfin h x y) =
      finiteAdicHCup l m S h (reduction S l m i x) (reduction S l m j y) :=
  (exists_reduction_eq_finiteAdicHCup l S h x y).choose_spec m

/-- **Graded commutativity**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem integralAdicHCup_comm {i j k : ℕ} (h : i + j = k) (x : IntegralAdicH S l i)
    (y : IntegralAdicH S l j) :
    integralAdicHCup l S hfin ((add_comm j i).trans h) y x =
      ((i : ℤ) * j).negOnePow • integralAdicHCup l S hfin h x y :=
  eq_of_forall_reduction_eq l S hfin fun m ↦ by
    rw [reduction_integralAdicHCup, finiteAdicHCup_comm, Units.smul_def, Units.smul_def,
      map_zsmul, reduction_integralAdicHCup]

/-- The pullback along an automorphism of a connected `S` is multiplicative. -/
theorem integralAdicHPullback_integralAdicHCup [ConnectedSpace S] (e : S ≅ S) {i j k : ℕ}
    (h : i + j = k) (x : IntegralAdicH S l i) (y : IntegralAdicH S l j) :
    integralAdicHPullback e l k (integralAdicHCup l S hfin h x y) =
      integralAdicHCup l S hfin h (integralAdicHPullback e l i x)
        (integralAdicHPullback e l j y) :=
  eq_of_forall_reduction_eq l S hfin fun m ↦ by
    rw [reduction_integralAdicHPullback, reduction_integralAdicHCup,
      finiteAdicHPullback_finiteAdicHCup, reduction_integralAdicHCup,
      reduction_integralAdicHPullback, reduction_integralAdicHPullback]

end AlgebraicGeometry.ProEtale
